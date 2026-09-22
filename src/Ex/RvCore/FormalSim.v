From Coq Require Import ZArith.BinInt Lia Program.Tactics Classes.DecidableClass Classes.RelationClasses Classes.Morphisms Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface coqutil.Byte coqutil.Datatypes.PrimitivePair
              coqutil.Z.bitblast coqutil.Datatypes.HList coqutil.Word.Properties coqutil.Map.Properties.
Require Import Ex.RvCore.Sim Ex.RvCore.Spec Ex.RvCore.Common Ex.RvCore.FormalSpec Ex.RvCore.Mem Ex.RvCore.SpecTrsHelper.
Require Import Lang.Lang Lang.ModuleITree.
From ITree Require Import ITree ITreeFacts.
From FreeSim Require Import Tutorial SimGlobalIndex SimGlobalEquiv SimGlobalIndexFacts.
From Ordinal Require Import Ordinal.

Require Import coqutil.Word.Bitwidth32.
Require Import riscv.Utility.MkMachineWidth.
Require riscv.Spec.Decode.

From Paco Require Import paco.
Import Spec.Spec.
Import ListNotations.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.
#[local] Delimit Scope sf_monad_scope with sf_monad.

Section proof.
  Context {word : Interface.word 32} {word_ok : word.ok word}.
  Context {Registers: map.map Decode.Register word} {registers_ok : map.ok Registers}.
  Context {Mem: map.map word byte} {mem_ok : map.ok Mem}.

  #[local] Open Scope Z_scope.

  #[local] Opaque hbinUArr.
  #[local] Arguments Z.pow_pos : simpl never.
  #[local] Arguments Z.pow : simpl never.
  #[local] Arguments Z.shiftl : simpl never.

  Definition spec_initial_state initial_imem: State := (Spec.rstS (List.map (fun iv => (fst iv, HMapBits #{snd iv, 32, false})) initial_imem)).
  Definition spec_concrete_transition: ModuleITree.Transition := trsT (Spec.mtrs).(mtrs_func).
  Definition spec_itree_raw state :=
    filter_io Sim.fixed_input Sim.outputValid (module_itree spec_concrete_transition state).

  Definition translate_riscv_output : (moduleE +' ModSemE.eventE) ~> itree (FormalSpec.riscv_ioE +' ModSemE.eventE) :=
    fun _ e =>
      match e with
      | inl1 module_io =>
        match module_io with
        | Output out =>
              match (sfind pc_commit out)%sf_monad with
              | Sret v => trigger (FormalSpec.Output (sz_norm (hbits v)))
              | _ => ModSemE.triggerUB
              end
        | Input => ModSemE.triggerUB
        end
      | inr1 e => trigger e
      end.

  Definition rf_val_related (op : option word) (h : hmap) :=
    match op with
    | None => 0
    | Some v => word.unsigned v
    end = szNormZ (szCastV #{32, 32, true} (hbits h)).
  (* rsvi = szCastV #{32, 32, true} hbits (array_select rfv rsi) *)

  Definition rf_related (formal_regs : Registers) (rfv : list (Z * Value)) : Prop :=
    forall k,
      k <> 0 -> (* 0 is zero register *)
      rf_val_related (map.get formal_regs k) (array_select rfv k).

  Definition mem_related (formal_mem : Mem) (impl_mem : list (Z * hmap)) : Prop :=
    forall (addr : word) (inst_ind : Z),
    (word.unsigned addr) = 4 * inst_ind ->                                            (* if an address is aligned to 4 bytes, *)
      exists tup, TupleMemory.load_bytes 4 formal_mem addr = Some tup  /\                  (* the load on formal_mem succeeds, and *)
      LittleEndian.combine 4 tup = szNormZ (hbits (array_select impl_mem inst_ind)).  (* its value is related to the load value of the impl_mem. *)

  Definition imem_related (formal_imem : Mem) (impl_imem : ICache.Flops) : Prop :=
    mem_related formal_imem impl_imem.(ICache.imem_v).

  Definition dmem_related (formal_dmem : Mem) (impl_dmem : DCache.Flops) : Prop :=
    mem_related formal_dmem impl_dmem.(DCache.dmem_v).

  Definition is_formatted size signed arr : Prop :=
    forall ind,
      match hselectA arr ind with
      | HMapBits b => exists z, b = #{z, size, signed}
      | _ => True
      end.

  (* Some helpful lemmas *)
  Lemma rf_update_0 regs rfv rfv' h
    (PREV : rf_related regs rfv)
    (UPD : rfv' = hbinUArr hupds rfv ((0, h) :: nil)) :
    rf_related regs rfv'.
  Proof.
    unfold rf_related in *. subst rfv'. intros k k_NONZERO.
    setoid_rewrite hselectA_single_upd_neq; auto.
  Qed.

  Lemma rf_update_related regs rfv regs' rfv' (ind : Z) w sz
    (PREV : rf_related regs rfv)
    (UPD_REGS : regs' = map.put regs ind w)
    (UPD_RFV : rfv' = hbinUArr hupds rfv ((ind, HMapBits sz) :: nil))
    (VAL_REL : word.unsigned w = szNormZ (szCastV #{32,32,true} sz)) :
    rf_related regs' rfv'.
  Proof.
    subst. unfold rf_related in *. intros k k_NONZERO.
    destruct (Z.eq_dec k ind) as [->|NEQ].
    - setoid_rewrite hselectA_single_upd_bits. rewrite map.get_put_same. unfold rf_val_related. cbn. exact VAL_REL.
    - setoid_rewrite hselectA_single_upd_neq; [|auto]. rewrite map.get_put_diff; [|auto]. eapply PREV. auto.
  Qed.

  Lemma setRegister_success f f' rfv rs w
    (SUCCESS : Machine.setRegister rs w f = (Some tt, f')) :
    exists regs', f' = withRegs regs' f /\
    forall sz rfv', rfv' = (hbinUArr hupds rfv ((rs, HMapBits sz) :: nil)) ->
      rf_related (getRegs f) rfv ->
      word.unsigned w = szNormZ (szCastV #{32,32,true} sz) ->
      rf_related regs' rfv'.
  Proof.
    cbn in SUCCESS. destruct (Z.eq_dec rs 0) as [->|?].
    - injection SUCCESS as <-. destruct f. cbn.
      eexists. split; [eauto|].
      intros. eapply rf_update_0; eauto.
    - destruct (_ && _)%bool in SUCCESS; [|discriminate SUCCESS].
      unfold Monads.OStateOperations.put, Monads.OState_Monad in SUCCESS.
      injection SUCCESS as <-.
      eexists. repeat ssplit; auto.
      intros. eapply rf_update_related; eauto.
  Qed.

  Definition sznorm_cast_hbits_formatted_unsigned arr i sz_size sz_signed size size_pos
    (FORMAT : is_formatted size false arr)
    (SIZE_POS : size = Zpos size_pos) :
    szNorm (szCastV #{size, sz_size, sz_signed} (hbits (hselectA arr i))) = szNormZ (hbits (hselectA arr i)).
  Proof.
    specialize (FORMAT i). subst size.
    destruct (hselectA arr i); try (eexists; reflexivity).
    destruct FORMAT as [? ->]. unfold szCastV. cbn. rewrite Pos.eqb_refl. reflexivity.
  Qed.

  Definition is_formatted_update_bits size signed arr sz z i arr'
    (UPD_ARR : arr' = hbinUArr hupds arr ((i, HMapBits sz) :: nil))
    (PREV : is_formatted size signed arr)
    (SZ_FORMATTED : sz = #{z, size, signed}) :
    is_formatted size signed arr'.
  Proof.
    unfold is_formatted in *. subst. intros i'.
    destruct (Z.eq_dec i i') as [->|NEQ].
    - rewrite hselectA_single_upd_bits. eexists. eauto.
    - rewrite hselectA_single_upd_neq; [|eauto]. apply PREV.
  Qed.

  Lemma assert_aligned_success addr u s s' :
    assert_aligned addr s = (Some u, s') ->
    s' = s /\ (word.unsigned addr mod 4 = 0).
  Proof.
    unfold assert_aligned. intros H.
    set (is_aligned := (Utility.reg_eqb (_) (_))) in H. cbn in is_aligned.

    assert (is_aligned = true) as aligned_true. { destruct is_aligned; [auto|discriminate H]. }
    rewrite aligned_true in H. cbn in H. injection H as _ ->. split; [auto|].

    subst is_aligned.
    eapply word.eqb_true in aligned_true.
    apply f_equal with (f := word.unsigned) in aligned_true.
    rewrite word.unsigned_modu_nowrap in aligned_true. 2: { rewrite word.unsigned_of_Z. change (word.wrap 4) with 4. lia. }
    rewrite 2!word.unsigned_of_Z in aligned_true. progress change (word.wrap ?a) with a in aligned_true.
    eauto.
  Qed.

  Lemma access_mem_rel formal_mem impl_mem (addr_w : word) addr_sz
    (MEM_REL : mem_related formal_mem impl_mem)
    (ADDR_REL : word.unsigned addr_w = szNormZ addr_sz)
    (ADDR_32 : szof addr_sz = 32)
    (ADDR_UNSIGNED : snof addr_sz = false)
    (ALIGNED : word.unsigned addr_w mod 4 = 0) :
    exists tup,
      TupleMemory.load_bytes 4 formal_mem addr_w = Some tup /\
      LittleEndian.combine 4 tup = szNormZ (hbits (hselectA impl_mem (szNormZ (szRange addr_sz 31 2)))).
  Proof.
    enough (word.unsigned addr_w = 4 * (szNormZ (szRange addr_sz 31 2))).
    { epose proof (MEM_REL _ _ H) as (?&?&?). eauto. }
    clear MEM_REL.

    setoid_rewrite ADDR_REL in ALIGNED. rewrite ADDR_REL.

    unfold szRange, szNorm, szNormZ in *. cbn in *.
    rewrite ADDR_32 in ALIGNED, ADDR_REL |- *. rewrite ADDR_UNSIGNED. clear ADDR_32 ADDR_UNSIGNED.

    remember (_ mod 2 ^ _) as addr_wrap eqn: Haddr_wrap in ADDR_REL, ALIGNED |- *.
    rewrite BitOps.bitSlice_alt; [|lia]. unfold BitOps.bitSlice'. change (2 ^ 2) with 4. cbn. rewrite Zdiv.Zmod_mod.
    assert (0 <= addr_wrap < 2 ^ 32) as Haddr_range. { subst. eapply Zdiv.Z_mod_lt. lia. } clear Haddr_wrap.
    pose proof (Zdiv.Z_div_mod_eq_full addr_wrap 4) as Hmult. rewrite ALIGNED, Z.add_0_r in Hmult.
    rewrite Z.mod_small; [auto|]. lia.
  Qed.

  Lemma access_rf_rel rs f f' w rfv
    (SUCCESS : Machine.getRegister rs f = (Some w, f'))
    (RF_REL : rf_related (getRegs f) rfv) :
    f' = f /\ word.unsigned w = szNormZ (szCastV #{32,32,true} (hbits (if rs =? 0 then HMapBits #{0,32,false} else hselectA rfv rs))).
  Proof.
    unfold Machine.getRegister, IsRiscvProgram in SUCCESS. destruct (Z.eq_dec rs 0) as [->|NEQ].
    - cbn in SUCCESS |- *. inversion SUCCESS. rewrite word.unsigned_of_Z. auto.
    - destruct (_ && _)%bool. 2: { discriminate SUCCESS. }
      specialize (RF_REL rs NEQ). cbn in *.
      replace (rs =? 0) with false. 2: { symmetry. eapply Z.eqb_neq. eauto. }
      destruct (map.get (getRegs f) rs); inversion SUCCESS; subst; (split; [auto|]).
      + (* value found *) exact RF_REL.
      + (* value not found*) rewrite word.unsigned_of_Z. exact RF_REL.
  Qed.

  Lemma mod_bitSlice_small z l r m :
    l <= r ->
    m >= 2 ^ (r - l) ->
    BitOps.bitSlice z l r mod m = BitOps.bitSlice z l r.
  Proof.
    intros. rewrite Z.mod_small; [reflexivity|].
    pose proof (BitOps.bitSlice_bounds l r z) as Bound.
    replace (Z.max 0 (r - l)) with (r - l) in Bound by lia.
    lia.
  Qed.

  Lemma mod_bitSlice_fit z l r :
    l <= r ->
    BitOps.bitSlice z l r mod 2 ^ (r - l) = BitOps.bitSlice z l r.
  Proof.
    intros. rewrite mod_bitSlice_small; eauto. lia.
  Qed.

  Lemma sznormZ_bitSlice_fit l r val : l <= r -> szNormZ #{BitOps.bitSlice val l r, r - l, false} = BitOps.bitSlice val l r.
  Proof.
    unfold szNormZ. cbn. eapply mod_bitSlice_fit.
  Qed.

  Lemma b2z_eqb_0_negb b: (Z.b2z (b) mod 2 ^ 1=? 0) = negb b.
  Proof. destruct b; reflexivity. Qed.

  Fixpoint combine' (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => (byte.unsigned (pair._1 bs))
                      + (2 ^ 8) * combine' n (pair._2 bs)
    end.

  #[local] Arguments LittleEndian.combine_deprecated !n bs.
  #[local] Opaque Z.mul.

  Lemma combine_alt n tup :
    LittleEndian.combine n tup = combine' n tup.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - cbn. rewrite IH.
      rewrite BitOps.or_to_plus. 2: {
        Z.bitblast. subst.
        destruct (ZArith_dec.Z_lt_le_dec i 8).
        - rewrite (Z.testbit_neg_r _ (i - 8)); [|lia].
          rewrite Bool.andb_false_r. eauto.
        - pose proof (byte.unsigned_range (pair._1 tup)).
          remember (byte.unsigned (pair._1 tup)) as u. clear Hequ.
          destruct (Z.testbit u i) eqn: Hb.
          + exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
            assert (2 ^ 8 <= 2 ^ i). { apply Z.pow_le_mono_r; lia. }
            lia.
          + reflexivity.
      }
      f_equal. rewrite Z.shiftl_mul_pow2; lia.
  Qed.

  #[local] Arguments LittleEndian.combine_deprecated : simpl never.

  (* ITree helpers. *)
  #[local] Instance euttge_simg {E R}: Proper ((euttge eq) ==> (@euttge (E +' ModSemE.eventE) R R eq) ==> impl) ((⪸)).
  Proof.
    repeat intro. eapply Tutorial.eutt_simg.  1,2: eapply euttge_sub_eutt; eassumption. eauto.
  Qed.

  #[local] Instance gsimg_cong_euttge {E} r1 r2 R0 R1 RR f_src f_tgt :
  Proper ((euttge eq) ==> (euttge eq) ==> flip impl)
    (gpaco7 (_simg (E := E)) (cpn7 (_simg (E:=E))) r1 r2 R0 R1 RR f_src f_tgt).
  Proof.
    repeat intro. guclo euttC_spec. econstructor; eauto.
  Qed.

  #[local] Hint Rewrite @interp_tau : itree.
  #[local] Hint Rewrite @interp_mrec_bind : itree.
  #[local] Hint Rewrite @interp_mrec_trigger : itree.

  #[local] Hint Rewrite @ITreelib.interp_mrec_tau : itree.
  #[local] Hint Rewrite @ITreelib.interp_mrec_ret : itree.
  Definition spec_itree_with_state state := interp translate_riscv_output (spec_itree_raw state).
  Definition spec_itree initial_imem := spec_itree_with_state (spec_initial_state initial_imem).

  Theorem spec_ok initial_imem
    (IMEM_OK: List.Forall (fun iv => 0 <= fst iv < 2 ^ 30) initial_imem)
  : (FormalSpec.riscv_itree (FormalSpec.formal_initial_imem initial_imem)) ⪸ (spec_itree initial_imem).
  Proof.
    unfold FormalSpec.riscv_itree, spec_itree.
    remember (FormalSpec.initial_state (FormalSpec.formal_initial_imem _)) as f1 eqn: Hf1.

    eremember (Spec.Build_Flops _ _ (ICache.Build_Flops _) (DCache.Build_Flops _)) as sf1 eqn: Hsf1.
    assert ((spec_initial_state initial_imem) = to_state sf1) as H.
    { rewrite Hsf1. reflexivity. }
    rewrite H. clear H.

    assert (word.unsigned (getPc f1) = szNormZ (Spec.pc_v sf1)) as PC_REL.
    { rewrite Hf1, Hsf1. cbn. rewrite word.unsigned_of_Z. reflexivity. }

    assert (imem_related (getInstMem f1) (Spec.icache_v sf1)) as IMEM_REL.
    { rewrite Hf1, Hsf1. clear -word_ok mem_ok IMEM_OK. unfold imem_related. cbn. unfold mem_related. intros access_w access_ind H.
      induction initial_imem as [|[a val] imem' IH].
      - (* base case *)
        assert (FormalSpec.formal_initial_imem nil = FormalSpec.zeroed) as -> by reflexivity.
        epose proof (FormalSpec.zeroed_load_bytes _ _) as (? & -> & Hcomb). eexists. split; [reflexivity|].
        exact Hcomb.
      - (* inductive case *)
        destruct IH as (tup_prev & Hprev_acc & Harr_select).
        { apply Forall_inv_tail in IMEM_OK. exact IMEM_OK. }
        unfold FormalSpec.formal_initial_imem. simpl.
        set (fold_right _ _ _) as prev_mem. replace (FormalSpec.formal_initial_imem _) with prev_mem in Hprev_acc by reflexivity. clearbody prev_mem.

        destruct (Z.eq_dec a access_ind) as [-> | NEQ].

        + exists (LittleEndian.split 4 val).
          unfold TupleMemory.load_bytes, TupleMemory.unchecked_store_bytes, map.getmany_of_tuple, map.putmany_of_tuple. simpl.
          assert (word.of_Z (4 * access_ind) = access_w) as ->. { apply word.unsigned_inj. rewrite <- H. rewrite word.of_Z_unsigned. reflexivity. }
          progress repeat (rewrite map.get_put_same || rewrite map.get_put_diff).
          2-7:
            clear -word_ok; intros Heq;
            apply f_equal with (f := word.unsigned), Zeq_minus, f_equal with (f := word.wrap) in Heq;
            rewrite !word.unsigned_add, !word.unsigned_of_Z in Heq;
            unfold word.wrap in Heq;
            rewrite_strat (bottomup repeat choice Z.add_mod_idemp_l Z.add_mod_idemp_r Zdiv.Zminus_mod_idemp_r Zdiv.Zminus_mod_idemp_l) in Heq; [|lia..];
            match type of Heq with | (?a mod _ = _) => first [replace a with 1 in Heq by lia| replace a with 2 in Heq by lia| replace a with 3 in Heq by lia] end;
            discriminate Heq.
          split.
          * reflexivity.
          * rewrite Z.eqb_refl. rewrite LittleEndian.combine_split. reflexivity.
        + exists tup_prev.
          apply Forall_inv in IMEM_OK. simpl in IMEM_OK.
          split.
          * unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.
            assert (access_w <> word.of_Z (4 * a)) as Haccess_w.
            { intros ->. rewrite word.unsigned_of_Z in H. unfold word.wrap in H. rewrite Z.mod_small in H; lia. }
            clear -Haccess_w H word_ok mem_ok IMEM_OK Hprev_acc.
            rewrite 16!map.get_put_diff.
            17: { assumption. }
            2, 7, 12: intros Heq;
                repeat (apply f_equal with (f:= fun x => word.sub x (word.of_Z 1)) in Heq; rewrite !word.word_sub_add_l_same_r in Heq);
                contradiction.
            2-13:
              intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
              rewrite ?word.unsigned_add, ?word.unsigned_of_Z, H in Heq;
              unfold word.wrap in Heq;
              rewrite_strat (bottomup repeat choice Z.add_mod_idemp_l Z.add_mod_idemp_r) in Heq; [|lia..];
              repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]);
              rewrite !Z.add_comm with (m := 1), ?Z.add_assoc, 2!Z.mul_comm with (n := 4), ?Z.mod_mul, ?Zdiv.Z_mod_plus_full in Heq by lia;
              discriminate Heq.

            exact Hprev_acc.
          * rewrite <- Z.eqb_neq, Z.eqb_sym in NEQ. rewrite NEQ. exact Harr_select.
    }

    assert (dmem_related (getDataMem f1) (Spec.dcache_v sf1)) as DMEM_REL.
    { rewrite Hf1, Hsf1. unfold dmem_related. cbn. unfold mem_related. intros.
      epose proof (FormalSpec.zeroed_load_bytes _ _) as (? & -> & Hcomb). eexists. split; [eauto|].
      cbn. dest_if; exact Hcomb. }

    assert (rf_related (getRegs f1) (Spec.rf_v sf1)) as RF_REL.
    { rewrite Hf1, Hsf1. unfold rf_related. cbn. intros k NEQ.
      replace (k =? 0) with false. 2: { symmetry. eapply Z.eqb_neq; eauto. }
      rewrite map.get_empty. reflexivity. }

    assert (exists pcv_z, Spec.pc_v sf1 = #{pcv_z, 32, false}) as (pcv_z & PC_FORMAT).
    { rewrite Hsf1. eexists. reflexivity. }

    assert (word.unsigned (getNextPc f1) = (word.unsigned (getPc f1) + 4) mod 2 ^ 32) as NEXT_PC.
    { rewrite Hf1. cbn. rewrite !word.unsigned_of_Z. reflexivity. }

    assert (is_formatted 32 false (ICache.imem_v (Spec.icache_v sf1))) as IMEM_FORMAT.
    { unfold is_formatted. intros ind.
      rewrite Hsf1. cbn. clear.
      induction initial_imem as [|[i v] l' IH]; [exact I|].
      cbn. destruct (ind =? i) eqn: Heq.
      - eauto.
      - exact IH. }

    assert (is_formatted 32 false (DCache.dmem_v (Spec.dcache_v sf1))) as DMEM_FORMAT.
    { rewrite Hsf1. unfold is_formatted. cbn. intros. dest_if; eauto. }

    assert (is_formatted 32 false (Spec.rf_v sf1)) as RF_FORMAT.
    { rewrite Hsf1. unfold is_formatted. cbn. intros. dest_if; eauto. }

    clear Hf1 Hsf1.
    revert_until initial_imem.
    ginit. gcofix CIH. intros.

    (* start unfolding the target(spec_itree_with_state). *)
    unfold spec_itree_with_state, spec_itree_raw, module_itree. unfold rec, mrec.
    unfold module_itree_body at 2, filter_io.
    repeat (autorewrite with itree; cbn -[spec_concrete_transition to_state]).
    remember (spec_concrete_transition fixed_input _) as SO eqn: Hstep. destruct SO as (s2, outs).
    repeat (autorewrite with itree; cbn).

    pose proof (spec_transition_concrete_unfold _ _ _ Hstep) as Hstep'. clear Hstep.
    destruct sf1 as [pcv rfv [imem][dmem]].

    destruct Hstep' as [Hs2_sf2 ->].

    remember (Spec.Build_Flops _ _ _ _) as sf2 eqn: Hsf2 in Hs2_sf2.

    simpl. repeat (autorewrite with itree; cbn).

    (* now lets analyze the execution of the spec. *)
    set (hide_target := ITree.bind _ _).
    unfold FormalSpec.riscv_itree_with_state, rec_fix, rec, mrec. set (recursive := fun _ : FormalSpec.State => _) at 1.
    simpl. destruct (FormalSpec.run1 f1) as [[[]|] f2] eqn: Hrun.
    2: { (* Case: error in riscv_itree. UB. *)
      unfold ModSemE.triggerUB. repeat (autorewrite with itree; cbn).
      guclo simg_indC_spec. econstructor; [eauto|]. inversion x.
    }
    (* Case: the instruction has been successful executed. *)
    repeat (autorewrite with itree; cbn). subst hide_target.
    apply FormalSpec.run1_success in Hrun.

    let T := type of Hrun in let T' := (eval simpl in T) in replace T with T' in Hrun by (simpl; reflexivity).
    (* equivalent 'simpl in Hrun' but faster for kernel check. See https://github.com/coq/coq/wiki/Troubleshooting *)

    destruct f1 as [f1_regs f1_pc f1_next_pc f1_inst_mem f1_data_mem] eqn: Hf1 in |- *.
    rewrite Hf1 in Hrun at 1, PC_REL, IMEM_REL, DMEM_REL, RF_REL, NEXT_PC.
    (* Note: using destruct f1 in Hrun at 1, PC_REL, IMEM_REL, ... will result in long Qed time.
      See https://github.com/coq/coq/wiki/Troubleshooting. *)
    simpl in Hrun, PC_REL, IMEM_REL, DMEM_REL, RF_REL, PC_FORMAT, IMEM_FORMAT, DMEM_FORMAT, RF_FORMAT, NEXT_PC |- *.

    setoid_rewrite PC_REL.
    replace (negb (_)) with true by reflexivity.
    repeat (autorewrite with itree; cbn).
    replace (szNorm pcv) with (szNormZ pcv). 2: { subst pcv. reflexivity. }

    guclo simg_indC_spec.
    econstructor; eauto. intros _ _ _.
    unfold call. repeat (autorewrite with itree; cbn). unfold mrec. cbn.

    change (interp translate_riscv_output _) with (spec_itree_with_state s2).
    change (interp_mrec _ _) with (FormalSpec.riscv_itree_with_state f2).
    do 2 instantiate (1 := 1%nat). clear recursive.

    (* Prepare for the inductive step. *)
    assert (exists pcv_z, word.unsigned (getPc f2) = szNormZ (Spec.pc_v sf2) /\
            imem_related (getInstMem f2) (Spec.icache_v sf2) /\
            dmem_related (getDataMem f2) (Spec.dcache_v sf2) /\
            rf_related (getRegs f2) (Spec.rf_v sf2) /\
            Spec.pc_v sf2 = #{pcv_z,32,false} /\
            word.unsigned (getNextPc f2) = (word.unsigned (getPc f2) + 4) mod 2 ^ 32 /\
            is_formatted 32 false (ICache.imem_v (Spec.icache_v sf2)) /\
            is_formatted 32 false (DCache.dmem_v (Spec.dcache_v sf2)) /\
            is_formatted 32 false (Spec.rf_v sf2))  as (?&?&?&?&?&?&?&?&?&?)
            .
    {
      #[local] Opaque szEqStr szConcat2 szConcat
        szSignExt szZeroExt szBFEq szBFNEq.
      #[local] Opaque hselectA hrangeA hbinUArr hbinUStr hupds.


      (* Check PC alignment. *)
      unfold loadN in Hrun.
      let T := type of Hrun in let T' := (eval simpl in T) in replace T with T' in Hrun by reflexivity.
      (* simpl in Hrun. *)

      destruct (assert_aligned f1_pc f1) as [[?|] ?] eqn: Hpc_assert_aligned in Hrun. 2: {  discriminate Hrun. }
      destruct (assert_aligned_success _ _ _ _ Hpc_assert_aligned) as [-> PC_ALIGNED]. clear Hpc_assert_aligned.

      rewrite Hf1 in Hrun at 1.
      let T := type of Hrun in let T' := (eval simpl in T) in replace T with T' in Hrun by (reflexivity).

      (* instruction load should succeed in both sides and return equivalent values. *)
      unshelve epose proof (access_mem_rel _ _ _ _ IMEM_REL PC_REL _ _ PC_ALIGNED) as (? & Hload_inst & INST_REL).
      1, 2: rewrite PC_FORMAT; reflexivity.

      rewrite Hload_inst in Hrun.
      let T := type of Hrun in let T' := (eval simpl in T) in replace T with T' in Hrun by (simpl; reflexivity).
      setoid_rewrite INST_REL in Hrun. clear INST_REL Hload_inst.


      (* Simplify Hsf2 & Hrun *)
      let T := type of Hsf2 in let T' := (eval cbv [sznil szUNot szBEq szBNEq szEquiv szSigned szRange szIsZero szBShl szBSar szBSal szBLAnd szBLOr
        szUNor szUXor szUXnor szBFEq szBFNEq szBWEq szBWNEq szBPow szBLt szBLe szBGt szBGe szBAnd szUnsigned szSelect szUMinus szUNeg szUAnd szUNand szUOr szMsb szLsb] in T) in
        replace T with T' in Hsf2 by (cbv [sznil szUNot szBEq szBNEq szEquiv szSigned szRange szIsZero szBShl szBSar szBSal szBLAnd szBLOr
        szUNor szUXor szUXnor szBFEq szBFNEq szBWEq szBWNEq szBPow szBLt szBLe szBGt szBGe szBAnd szUnsigned szSelect szUMinus szUNeg szUAnd szUNand szUOr szMsb szLsb]; reflexivity).

      progress repeat match type of Hsf2 with
      | context [szNorm #{Zpos ?a, _, _}] => replace (szNorm #{Zpos a, _, _}) with (Zpos a) in Hsf2 by reflexivity
      end. (* ~33s *)
      replace (szNorm #{0,32,true}) with 0 in Hsf2 by reflexivity.
      replace (szNorm (szBSub #{32,32,true} #{1,32,true})) with 31 in Hsf2 by reflexivity.
      let T := type of Hsf2 in let T' := (eval cbn in T) in replace T with T' in Hsf2 by (cbn; reflexivity).
      rewrite !sznormZ_bitSlice_fit in Hsf2 by lia.

      set (pc_index := BitOps.bitSlice (szNorm pcv) _ 32) in Hsf2.
      replace (szNormZ (szRange pcv 31 _)) with pc_index in Hrun. 2: { setoid_rewrite sznormZ_bitSlice_fit; [|lia]. reflexivity. }
      set (inst_cur_v := hselectA _ pc_index) in Hsf2, Hrun.
      set (inst_cur_z := szNormZ (hbits inst_cur_v)) in Hrun.
      replace (match inst_cur_v with |HMapBits _ => _ | _ => _ end) with (hbits inst_cur_v) in Hsf2 by reflexivity.
      replace (szNorm (szCastV #{32,32,true} (hbits inst_cur_v))) with inst_cur_z in Hsf2.
      2: { subst inst_cur_v. setoid_rewrite sznorm_cast_hbits_formatted_unsigned; eauto. }

      progress repeat match type of Hsf2 with
      | context [match ?h with | HMapBits b => b | _ => _ end] =>
        replace (match h with | HMapBits b => b | _ => _ end) with (hbits h) in Hsf2 by reflexivity
      end.

      let T := type of Hsf2 in let T' := (eval cbv [szCast'] in T) in replace T with T' in Hsf2 by (cbv [szCast']; reflexivity).
      let T := type of Hsf2 in let T' := (eval cbn in T) in replace T with T' in Hsf2 by (cbn; reflexivity).
      let T := type of Hsf2 in let T' := (eval cbv [szNormZ] in T) in replace T with T' in Hsf2 by (cbv [szNormZ]; reflexivity).
      let T := type of Hsf2 in let T' := (eval cbn in T) in replace T with T' in Hsf2 by (cbn; reflexivity).
      rewrite !mod_bitSlice_fit in Hsf2 by lia.
      progress repeat match type of Hsf2 with
      | context [?a mod ?b] => replace (a mod b) with (a) in Hsf2 by reflexivity
      end. (* ~4s *)
      rewrite !b2z_eqb_0_negb in Hsf2. simpl_bool.
      (* progress repeat rewrite ?Bool.negb_involutive, ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r,
          ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
          ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hsf2. *)

      (* Now, we give names to important values and prove some useful properties about them. *)
      set (decoded := Decode.decode _ inst_cur_z) in Hrun.
      unfold Decode.decode, Utility.Utility.machineIntToShamt, id in decoded. cbn -[inst_cur_z] in decoded.
      set (decode_results := (_ : list Decode.Instruction)) in decoded.

      set (opcode := BitOps.bitSlice inst_cur_z 0 7) in Hsf2, decode_results.
      set (rs1 := BitOps.bitSlice inst_cur_z 15 20) in Hsf2, decode_results.
      set (rs2 := BitOps.bitSlice inst_cur_z 20 25) in Hsf2, decode_results.
      set (rd := BitOps.bitSlice inst_cur_z 7 12) in Hsf2, decode_results.
      set (funct3 := BitOps.bitSlice inst_cur_z 12 15) in Hsf2, decode_results.
      set (funct6 := BitOps.bitSlice inst_cur_z 26 32) in Hsf2, decode_results.
      set (funct7 := BitOps.bitSlice inst_cur_z 25 32) in Hsf2, decode_results.
      set (imm_i := BitOps.bitSlice inst_cur_z 20 32) in Hsf2, decode_results. (* imm12  *)
      set (imm_u := BitOps.bitSlice inst_cur_z 12 32) in Hsf2, decode_results. (* imm20 *)

      set (shamt5 := BitOps.bitSlice inst_cur_z 20 25) in decode_results.
      set (shamt6 := BitOps.bitSlice inst_cur_z 20 26) in decode_results.
      set (shamtHi := BitOps.bitSlice inst_cur_z 25 26) in decode_results.

      replace (BitOps.bitSlice imm_i 0 5) with shamt5 in Hsf2.
      2: { subst shamt5 imm_i. rewrite !BitOps.bitSlice_alt; [|lia..]. unfold BitOps.bitSlice'; cbn.
        rewrite Z.div_1_r. eapply Znumtheory.Zmod_div_mod; [lia..|].
        rewrite Z.pow_add_r with (b := 5) (c := 7); [|lia..].
        eapply Z.divide_factor_l.
      }
      assert (shamtHi = 0 -> shamt6 = shamt5 /\ funct7 = funct6 * 2) as HshamtHi_zero.
      { clear. intros shamtHi_zero. subst shamt5 shamt6 shamtHi funct6 funct7. rewrite !BitOps.bitSlice_alt in *; [|lia..].
        unfold BitOps.bitSlice' in *. cbn in *. change (2 ^ 1) with 2 in shamtHi_zero.
        assert (Z.testbit inst_cur_z 25 = false). { rewrite Z.testbit_eqb; [|lia]. rewrite shamtHi_zero. reflexivity. }
        split.
        - Z.bitblast. subst. simpl_bool. assert (i = 5) as -> by lia. eauto.
        - rewrite <- Z.mul_mod_distr_r; [|lia..].
          replace (2 ^ 6 * 2) with (2 ^ 7) by lia.
          rewrite Z.pow_add_r with (b := 25) (c := 1); [|lia..]. change (2 ^ 1) with 2.
          rewrite Z.mul_comm. rewrite <- Z.div_div; [|lia..].
          rewrite <- Zdiv.Z_div_exact_2; [|lia|eauto].
          reflexivity.
      }
      assert (0 <= shamt5 < 32) as Hshamt5_bound. { eapply BitOps.bitSlice_bounds. }
      assert (0 <= imm_u < 2 ^ 20) as Himm_u_bound. { eapply BitOps.bitSlice_bounds. }


      set (imm_b := Z.lor ((Z.lor ((Z.lor ((Z.shiftl (BitOps.bitSlice inst_cur_z 31 32 mod _) 12 mod _) mod _)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 25 31 mod _) _ mod _) mod _) mod _) mod _)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 8 12 mod _) _ mod _) mod  _) mod _) mod _)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 7 8 mod _) _ mod _) mod _)) in Hsf2.
      set (sbimm12_unsigned := (Z.lor (Z.lor (Z.lor (Z.shiftl (BitOps.bitSlice inst_cur_z 31 32) 12)
                    (Z.shiftl (BitOps.bitSlice inst_cur_z 25 31) 5))
                    (Z.shiftl (BitOps.bitSlice inst_cur_z 8 12) 1))
                    (Z.shiftl (BitOps.bitSlice inst_cur_z 7 8) _))) in decode_results.

      assert (imm_b = sbimm12_unsigned) as <-.
      { clear. subst imm_b sbimm12_unsigned.
        rewrite !mod_bitSlice_small; [|lia..].
        rewrite !Z.mod_mod; [|lia..].
        do 4 match goal with
        | |- context [BitOps.bitSlice inst_cur_z ?l ?r] =>
          let A := fresh A in let c := (eval cbn in (r-l)) in
          set (A := BitOps.bitSlice inst_cur_z l r); assert (0 <= A < 2^c) by eapply BitOps.bitSlice_bounds;
          match goal with
          | |- context [Z.shiftl A ?n] =>
            assert (0 <= Z.shiftl A n < 2^n * 2^c); [(rewrite Z.shiftl_mul_pow2; lia)|];
            rewrite Z.mod_small with (a := Z.shiftl A n) by lia
          end
        end.

        f_equal.

        assert (Z.lor (Z.shiftl A 12) (Z.shiftl A0 5) = (Z.shiftl A 12) + (Z.shiftl A0 5)) as Hlor_add1.
        { eapply BitOps.or_to_plus. Z.bitblast. subst.
          destruct (ZArith_dec.Z_lt_le_dec i 12).
          - rewrite (Z.testbit_neg_r _ (i - 12)); [|lia]. reflexivity.
          - destruct (Z.testbit A0 _) eqn: Hb; [|simpl_bool; reflexivity].
            exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
            assert (2 ^ 7 <= 2 ^ (i - 5)). { apply Z.pow_le_mono_r; lia. } lia.
        }

        rewrite Z.mod_small with (a := (Z.lor (_ A 12) _)) by lia.
        rewrite Z.mod_small; [reflexivity|].

        rewrite BitOps.or_to_plus; [lia|].
        Z.bitblast. subst.
        destruct (ZArith_dec.Z_lt_le_dec i 5).
        - rewrite 2!Z.testbit_neg_r; [|lia..]. reflexivity.
        - destruct (Z.testbit A1 _) eqn: Hb; [|simpl_bool; reflexivity].
          exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
          assert (2 ^ 4 <= 2 ^ (i - 1)). { apply Z.pow_le_mono_r; lia. } lia.
      }

      set (imm_j := (Z.lor ((Z.lor ((Z.lor ((Z.shiftl (BitOps.bitSlice inst_cur_z 31 32 mod 2 ^ 32) 20 mod 2 ^ 32) mod 2 ^ 32)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 21 31 mod 2 ^ 32) 1 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 20 21 mod 2 ^ 32) 11 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32)
                      ((Z.shiftl (BitOps.bitSlice inst_cur_z 12 20 mod 2 ^ 32) 12 mod 2 ^ 32) mod 2 ^ _))) in Hsf2.

      set (jimm20_unsigned := (Z.lor (Z.lor (Z.lor (Z.shiftl (BitOps.bitSlice _ 31 32) 20)
                      (Z.shiftl (BitOps.bitSlice inst_cur_z 21 31) 1))
                      (Z.shiftl (BitOps.bitSlice inst_cur_z 20 21) 11))
                      (Z.shiftl (BitOps.bitSlice inst_cur_z 12 20) 12))) in decode_results.

      assert (imm_j = jimm20_unsigned) as <-.
      { clear. subst imm_j jimm20_unsigned.
        rewrite !mod_bitSlice_small; [|lia..].
        rewrite !Z.mod_mod; [|lia..].
        do 4 match goal with
        | |- context [BitOps.bitSlice inst_cur_z ?l ?r] =>
          let A := fresh A in let c := (eval cbn in (r-l)) in
          set (A := BitOps.bitSlice inst_cur_z l r); assert (0 <= A < 2^c) by eapply BitOps.bitSlice_bounds;
          match goal with
          | |- context [Z.shiftl A ?n] =>
            assert (0 <= Z.shiftl A n < 2^n * 2^c); [(rewrite Z.shiftl_mul_pow2; lia)|];
            rewrite Z.mod_small with (a := Z.shiftl A n) by lia
          end
        end.

        f_equal.

        assert (Z.lor (Z.shiftl A 20) (Z.shiftl A0 1) = (Z.shiftl A 20) + (Z.shiftl A0 1)) as Hlor_add1.
        { eapply BitOps.or_to_plus. Z.bitblast. subst.
          destruct (ZArith_dec.Z_lt_le_dec i 20).
          - rewrite (Z.testbit_neg_r _ (i - 20)); [|lia]. reflexivity.
          - destruct (Z.testbit A0 _) eqn: Hb; [|simpl_bool; reflexivity].
            exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
            assert (2 ^ 19 <= 2 ^ (i - 1)). { apply Z.pow_le_mono_r; lia. } lia.
        }

        rewrite Z.mod_small with (a := (Z.lor (_ A 20) _)) by lia.
        rewrite Z.mod_small; [reflexivity|].

        rewrite BitOps.or_to_plus; [lia|].
        Z.bitblast. subst.
        destruct (ZArith_dec.Z_lt_le_dec i 11).
        { rewrite Z.testbit_neg_r with (n := i - 11); [|lia..]. rewrite Bool.andb_false_r. reflexivity. }
        destruct (ZArith_dec.Z_lt_le_dec i 12).
        { assert (i = 11) as -> by lia. cbn -[Z.testbit].
          rewrite Z.testbit_neg_r with (n := -9); [|lia].
          destruct (Z.testbit A0 _) eqn: Hb; [|simpl_bool; reflexivity].
          exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..]. lia. }
        { destruct (Z.testbit _ (i - 11)) eqn: Hb; [|simpl_bool; reflexivity].
          exfalso.  eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
          assert (2 ^ 1 <= 2 ^ (i - 11)). { apply Z.pow_le_mono_r; lia. } lia. }
      }
      set (simm12 := Z.lor (Z.shiftl funct7 _) rd) in decode_results.
      set (imm_s := Z.lor ((Z.shiftl (funct7 mod 2 ^ _) 5 mod 2 ^ _) mod 2 ^ _) (rd mod 2 ^ _)) in Hsf2.

      assert (0 <= funct7 < 2 ^ 7) as Hfunct7_bound. { eapply BitOps.bitSlice_bounds. }
      assert (0 <= rd < 2 ^ 5) as Hrd_bound. { eapply BitOps.bitSlice_bounds. }

      assert (imm_s = simm12) as ->.
      { subst imm_s simm12.
        rewrite Z.mod_small with (a := funct7) by lia. rewrite Z.mod_small with (a := rd) by lia.
        rewrite !Z.mod_mod by lia.
        f_equal.
        eapply Z.mod_small.
        rewrite Z.shiftl_mul_pow2 by lia. lia.
      }
      assert (0 <= simm12 < 2 ^ 12) as Hsimm12_bound.
      { clear -Hrd_bound Hfunct7_bound. subst simm12. rewrite BitOps.or_to_plus.
        2: { Z.bitblast. subst.
          destruct (ZArith_dec.Z_lt_le_dec i 5).
          { rewrite Z.testbit_neg_r with (n := i - 5) by lia. reflexivity. }
            destruct (Z.testbit _ i) eqn: Hb; [|simpl_bool; reflexivity].
            exfalso. eapply ZLib.Z.testbit_true_nonneg in Hb; [|lia..].
            assert (2 ^ 5 <= 2 ^ i). { apply Z.pow_le_mono_r; lia. } lia.
        }
        rewrite Z.shiftl_mul_pow2; lia.
      }

      set (getRegister rs := szCastV #{32,32,true} (hbits
                                  (if rs =? 0
                                    then HMapBits #{0,32,false}
                                    else hselectA rfv rs))).
      set (rsv1_sz := szCastV #{32,32,true} (hbits (if rs1 =? 0 then _ else _))) in Hsf2. (* = getRegister rs1*)
      set (rsv2_sz := szCastV #{32,32,true} (hbits (if rs2 =? 0 then _ else _))) in Hsf2. (* = getRegister rs2 *)

      (* lemma for processing Machine.getRegister. *)
      assert (forall rs w f1', Machine.getRegister rs f1 = (Some w, f1') ->
        f1' = f1 /\ word.unsigned w = szNormZ (getRegister rs)) as Hget_rsv.
      { intros ??? Hget_rs. eapply access_rf_rel; subst f1; eauto. }
      specialize (Hget_rsv rs1) as Hget_rsv1.
      specialize (Hget_rsv rs2) as Hget_rsv2.
      clear Hget_rsv.

      (* format of the register values. *)
      assert (forall rs, exists z, getRegister rs = #{z, 32, false}) as Hrsv_format.
      { unfold getRegister. intros. destruct (rs =? 0); [eexists; reflexivity|].
        specialize (RF_FORMAT rs). destruct (hselectA rfv rs); try (eexists; reflexivity).
        destruct RF_FORMAT as [? ->]. eexists. reflexivity. }
      specialize (Hrsv_format rs1) as RSV1_FORMAT. destruct RSV1_FORMAT as [rsv1_z RSV1_FORMAT].
      specialize (Hrsv_format rs2) as RSV2_FORMAT. destruct RSV2_FORMAT as [rsv2_z RSV2_FORMAT].
      clear Hrsv_format.

      change (getRegister rs1) with rsv1_sz in Hget_rsv1, RSV1_FORMAT.
      change (getRegister rs2) with rsv2_sz in Hget_rsv2, RSV2_FORMAT.
      clearbody rsv1_sz rsv2_sz.

      (* The calculated value for immediate instructions (rsv1 + imm_i) *)
      set (calculated_sz := szBAdd rsv1_sz  #{imm_i, _, _}) in Hsf2.
      assert (exists z, calculated_sz = #{z, 32, false}) as [calculated_z CALCULATED_FORMAT].
      { subst calculated_sz. rewrite RSV1_FORMAT. cbn. eexists. reflexivity. }

      assert (forall rsv1_w f1', Machine.getRegister rs1 f1 = (Some rsv1_w, f1') ->
        let calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend 12 imm_i)) in
        word.unsigned calculated_w = szNormZ calculated_sz) as CALCULATED_REL.
      { intros ?? Hget_rs1 ?.
        subst calculated_w calculated_sz. cbn.
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL). progress unfold szBin in *.
        rewrite RSV1_FORMAT in RSV1_REL |- *. clear -RSV1_REL word_ok. cbn in *.
        unfold szBin, szNormZ, szBAdd. cbn. unfold szNormS, szNormZ. cbn.
        rewrite word.unsigned_add.
        rewrite RSV1_REL, word.unsigned_of_Z. unfold szNormZ, word.wrap. cbn.
        rewrite Z.add_mod_idemp_r; [|lia].
        repeat f_equal. rewrite Z.mod_small; [auto|].
        apply BitOps.bitSlice_bounds.
      }

      (* The store addresses *)
      set (store_addr_z := szNorm (szBAdd rsv1_sz #{simm12,_,true})) in Hsf2.

      assert (0 <= store_addr_z < 2 ^ 32) as Hstore_addr_z_bound.
      { subst store_addr_z. rewrite RSV1_FORMAT. unfold szNorm, szNormZ; cbn. eapply Z.mod_pos_bound. lia. }

      assert (forall rsv1_w f1', Machine.getRegister rs1 f1 = (Some rsv1_w, f1') ->
        let store_addr_w := word.add rsv1_w (word.of_Z (BitOps.signExtend 12 simm12)) in
        word.unsigned store_addr_w = store_addr_z) as STORE_ADDR_REL.
      { intros ?? Hget_rs1 ?. subst store_addr_w store_addr_z.
      specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        rewrite word.unsigned_add, word.unsigned_of_Z, RSV1_REL.
        rewrite RSV1_FORMAT. unfold word.wrap, szNorm; cbn. unfold szBin; cbn. unfold szNormS, szNormZ; cbn.
        rewrite Z.add_mod_idemp_r by lia. do 3f_equal. rewrite Z.mod_small by lia. reflexivity. }


      (* lemma for processing value loads *)
      assert (forall rsv1_w f1', Machine.getRegister rs1 f1 = (Some rsv1_w, f1') ->
        let calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend 12 imm_i)) in
        word.unsigned calculated_w mod 4 = 0 ->
          exists tup,
            TupleMemory.load_bytes 4 f1_data_mem calculated_w = Some tup /\
            LittleEndian.combine_deprecated 4 tup =
            szNormZ (hbits (hselectA (dmem) (BitOps.bitSlice (szNorm calculated_sz) 2 (32)))))
            as Hload_helper.
      { intros ?? Hget_rs1 ??.
        assert (szof calculated_sz = 32 /\ snof calculated_sz = false) as [LOAD_ADDR_32 LOAD_ADDR_UNSIGNED].
        { subst calculated_sz. rewrite RSV1_FORMAT. eauto. }
        rewrite <- sznormZ_bitSlice_fit; [|lia].
        eapply access_mem_rel; eauto.
      }

      pose (store_ind := store_addr_z / 4).
      replace (BitOps.bitSlice store_addr_z _ 32) with (store_ind) in Hsf2.
      2: { subst store_ind. clear -Hstore_addr_z_bound. rewrite BitOps.bitSlice_alt by lia. unfold BitOps.bitSlice'. cbn. rewrite Z.mod_small; [reflexivity|]. split.
        - eapply Zdiv.Z_div_nonneg_nonneg; lia.
        - eapply Z.div_lt_upper_bound; lia. }


      set (instruction_i := (_ : Decode.InstructionI)) in decode_results.
      set (instruction_csr := (_ : Decode.InstructionCSR)) in decode_results.




      (* the default of getting pc from getNextPc (adding 4 to the pc) maintains PC_REL. *)
      assert (word.unsigned f1_next_pc = szNormZ #{szBin Z.add #{pcv_z,32,false} #{4,32,false},32,false}) as Hpc_simpl.
      { rewrite NEXT_PC, PC_REL, PC_FORMAT. unfold szBin; cbn. unfold szNormZ; cbn. reflexivity. }

      (* Note that next_pc is always set to current_pc + 4 when the instruction execution successfully finishes. See endCycleNormal in RvCore/Machine.v *)
      assert (forall (new_pc : word), word.unsigned (word.add new_pc (word.of_Z 4)) = (word.unsigned new_pc + 4) mod 2 ^ 32) as Hnext_pc_always.
      { intros. rewrite word.unsigned_add, word.unsigned_of_Z. reflexivity. }

      (* PC_REL after branch instructions. *)
      assert (word.unsigned (word.add f1_pc (word.of_Z (BitOps.signExtend 13 imm_b))) = szNormZ #{szBin Z.add #{pcv_z,32,false} #{imm_b mod 2 ^ 13,13,true},32,false}) as Hpc_rel_branch.
      { rewrite word.unsigned_add, word.unsigned_of_Z. rewrite PC_REL, PC_FORMAT.
        unfold word.wrap, szNormS, szNormZ, BitOps.signExtend; cbn.
        rewrite Z.add_mod_idemp_r by lia.
        cbv [szBin szNorm szNormZ szNormS BitOps.signExtend]; cbn.
        rewrite Z.mod_mod, !Z.add_mod_idemp_l by lia.
        reflexivity. }

      (* Show that decode should succeed. *)
      assert (decoded <> Decode.InvalidInstruction inst_cur_z) as DECODED_VALID. { intros ->. discriminate Hrun. }
      destruct (_ (length decode_results) >? 1). { discriminate. }

      let T := type of Hsf2 in let T' := (eval cbv [szNormZ] in T) in replace T with T' in Hsf2 by (cbv [szNormZ]; reflexivity).

      (* Let's do a case analysis for the decoded instruction. *)
      (repeat try match (eval hnf in instruction_i) with
      | context [if ?b then _ else _] => destruct b eqn: CASE; [|clear CASE]
      end);
      repeat (rewrite Bool.andb_true_iff in CASE; (let CASE' := fresh CASE in destruct CASE as [CASE' CASE]));
      cbn in decoded; subst instruction_i decoded; [clear decode_results instruction_csr DECODED_VALID..|];
      repeat match goal with
      | H: ((?x =? ?val) = true) |- _ => unfold val in H; rewrite Z.eqb_eq in H; rewrite H in *
      end;
      (let T := type of Hsf2 in let T' := (eval cbn in T) in replace T with T' in Hsf2 by (cbn; reflexivity));
      cbn [Execute.execute ExecuteI.execute Monads.Bind Machine.translate Machine.DefaultRiscvState Monads.Return Monads.OState_Monad] in Hrun.
      - (* Case: inst = Decode.Lb rd rs1 (BitOps.signExtend 12 imm_i) *)
        (* get rs1's register value (base address). *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        set (loaded_sz := #{_, 8, true}) in Hsf2.
        set (calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend _ imm_i))) in Hrun.
        unfold Machine.loadByte, IsRiscvProgram, loadN, Monads.Bind, Monads.OStateOperations.get, Monads.OState_Monad, Monads.Return in Hrun.

        (* check the alignment of the load address. *)
        destruct (assert_aligned calculated_w f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> LOAD_ALIGNED]. clear Haddr_aligned.

        (* use mem_rel to get relation for the loaded word *)
        specialize (Hload_helper _ _ Hget_rs1 LOAD_ALIGNED) as (loaded_word & Hloaded_word & LOADED_WORD_REL).
        progress fold calculated_w in Hloaded_word.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn -[calculated_w TupleMemory.load_bytes Machine.setRegister] in Hrun.
        destruct (TupleMemory.load_bytes 1 f1_data_mem calculated_w) as [loaded|] eqn: Hload in Hrun. 2: { discriminate Hrun. }
        progress cbn -[Machine.setRegister] in Hrun.

        (* show that the loaded byte is related. *)
        assert (word.wrap (BitOps.signExtend 8 (LittleEndian.combine 1 loaded))
                  = szNormZ (szCastV #{32, 32, true} loaded_sz)) as LOADED_REL.
        { clear -word_ok DMEM_FORMAT Hload Hloaded_word LOADED_WORD_REL.
          subst loaded_sz. set (loaded_word_sz := hbits (hselectA _ _)) in LOADED_WORD_REL |- *.
          cbn. unfold szCast'; cbn. unfold szNormS, szNormZ; cbn.
          replace (szNorm (szCastV #{32, _, _} loaded_word_sz)) with (szNormZ loaded_word_sz).
          2: { subst loaded_word_sz. symmetry. eapply sznorm_cast_hbits_formatted_unsigned; eauto. }
          rewrite <- LOADED_WORD_REL. setoid_rewrite sznormZ_bitSlice_fit; [|lia].
          unfold word.wrap. repeat f_equal.

          (* simplify TupleMemory.load_bytes. *)
          unfold TupleMemory.load_bytes, map.getmany_of_tuple in *. cbn -[calculated_w] in Hloaded_word, Hload.
          do 4 let H := fresh Hget in destruct (map.get f1_data_mem _) eqn: H in Hloaded_word; [|discriminate Hloaded_word].
          rewrite Hget in Hload.
          inversion Hload. inversion Hloaded_word.

          (* simplify goal *)
          rewrite BitOps.bitSlice_alt; [|lia]. unfold BitOps.bitSlice'. cbn.
          change (?a / 2 ^ 0) with (a / 1). rewrite Z.div_1_r.
          rewrite 2!combine_alt. cbn.
          pose proof (byte.unsigned_range b).
          remember (byte.unsigned b) as B eqn: HeqB. clear HeqB.
          rewrite <- Zdiv.Zplus_mod_idemp_r. rewrite !(Z.mul_comm (2 ^ 8)).
          rewrite Z.mod_mul; [|lia]. do 2 (replace (B + _) with B; [|lia]).
          rewrite Z.mod_small; lia.
        }

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* Now we extract the f2 value from Hrun to prove the goal. *)
        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. rewrite word.unsigned_of_Z. eapply LOADED_REL.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Decode.Lh rd rs1 (BitOps.signExtend 12 imm_i) *)
        (* get rs1's register value (base address). *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        set (loaded_sz := #{_, 16, true}) in Hsf2.
        set (calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend _ imm_i))) in Hrun.
        unfold Machine.loadHalf, IsRiscvProgram, loadN, Monads.Bind, Monads.OStateOperations.get, Monads.OState_Monad, Monads.Return in Hrun.

        (* check the alignment of the load address. *)
        destruct (assert_aligned calculated_w f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> LOAD_ALIGNED]. clear Haddr_aligned.

        (* use mem_rel to get relation for the loaded word *)
        specialize (Hload_helper _ _ Hget_rs1 LOAD_ALIGNED) as (loaded_word & Hloaded_word & LOADED_WORD_REL).
        progress fold calculated_w in Hloaded_word.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn -[calculated_w TupleMemory.load_bytes Machine.setRegister] in Hrun.
        destruct (TupleMemory.load_bytes _ f1_data_mem calculated_w) as [loaded|] eqn: Hload in Hrun. 2: { discriminate Hrun. }
        progress cbn -[Machine.setRegister] in Hrun.

        (* show that the loaded half-byte is related. *)
        assert (word.wrap (BitOps.signExtend 16 (LittleEndian.combine 2 loaded))
                  = szNormZ (szCastV #{32, 32, true} loaded_sz)) as LOADED_REL.
        { clear -word_ok DMEM_FORMAT Hload Hloaded_word LOADED_WORD_REL.
          subst loaded_sz. set (loaded_word_sz := hbits (hselectA _ _)) in LOADED_WORD_REL |- *.
          cbn. unfold szCast'; cbn.  unfold szNormS, szNormZ; cbn.
          replace (szNorm (szCastV _ loaded_word_sz)) with (szNormZ loaded_word_sz).
          2: { subst loaded_word_sz. symmetry. eapply sznorm_cast_hbits_formatted_unsigned; eauto. }
          rewrite <- LOADED_WORD_REL. setoid_rewrite sznormZ_bitSlice_fit; [|lia].
          unfold word.wrap. repeat f_equal.

          (* simplify TupleMemory.load_bytes. *)
          unfold TupleMemory.load_bytes, map.getmany_of_tuple in *. cbn -[calculated_w] in Hloaded_word, Hload.
          do 4 let H := fresh Hget in destruct (map.get f1_data_mem _) eqn: H in Hloaded_word; [|discriminate Hloaded_word].
          rewrite Hget, Hget0 in Hload.
          inversion Hload. inversion Hloaded_word.

          (* simplify goal *)
          rewrite BitOps.bitSlice_alt; [|lia]. unfold BitOps.bitSlice'. cbn.
          change (?a / 2 ^ 0) with (a / 1). rewrite Z.div_1_r.
          rewrite 2!combine_alt. cbn.
          pose proof (byte.unsigned_range b).
          pose proof (byte.unsigned_range b0).
          remember (byte.unsigned b) as B eqn: HeqB. clear HeqB.
          remember (byte.unsigned b0) as B0 eqn: HeqB0. clear HeqB0.
          rewrite !Z.mul_add_distr_l. rewrite !Z.mul_assoc. replace (2^8 * 2^8) with (2 ^ 16); [|lia].
          rewrite !Z.add_assoc.
          do 2 (replace (_ * 0) with 0; [|lia]). rewrite !Z.add_0_r.
          rewrite <- Zdiv.Zplus_mod_idemp_r.
          rewrite Znumtheory.Zdivide_mod with (a := 2^16 * _ * _). 2: { rewrite <- Z.mul_assoc. eapply Z.divide_factor_l. }
          rewrite Z.add_0_r.

          rewrite <- Zdiv.Zplus_mod_idemp_r. rewrite Z.mul_comm with (n := (2 ^ 16)).
          rewrite Z.mod_mul; [|lia]. rewrite Z.add_0_r.
          rewrite Z.mod_small; lia.
        }

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* Now we extract the f2 value from Hrun to prove the goal. *)
        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].  rewrite word.unsigned_of_Z. exact LOADED_REL.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.

      - (* Case: inst = Decode.Lw rd rs1 (BitOps.signExtend 12 imm_i) *)
        (* get rs1's register value (base address). *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        set (loaded_sz := szCastV #{32,32,true} (hbits (hselectA dmem _))) in Hsf2.
        set (calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend _ imm_i))) in Hrun.
        unfold Machine.loadWord, IsRiscvProgram, loadN, Monads.Bind, Monads.OStateOperations.get, Monads.OState_Monad, Monads.Return in Hrun.

        (* check the alignment of the load address. *)
        destruct (assert_aligned calculated_w f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> LOAD_ALIGNED]. clear Haddr_aligned.

        (* use mem_rel to get relation for the loaded word *)
        specialize (Hload_helper _ _ Hget_rs1 LOAD_ALIGNED) as (loaded_word & Hloaded_word & LOADED_WORD_REL).
        progress fold calculated_w in Hloaded_word.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn -[calculated_w TupleMemory.load_bytes Machine.setRegister] in Hrun.
        destruct (TupleMemory.load_bytes _ f1_data_mem calculated_w) as [loaded|] eqn: Hload in Hrun. 2: { discriminate Hrun. }
        progress cbn -[Machine.setRegister] in Hrun.

        (* show that the loaded value is related. *)
        assert (word.wrap (BitOps.signExtend 32 (LittleEndian.combine 4 loaded))
                  = szNormZ (szCastV #{32, 32, true} loaded_sz)) as LOADED_REL.
        { subst loaded_sz.
          set (addr := BitOps.bitSlice _ _ _) in LOADED_WORD_REL |- *.
          set (val := (hbits (hselectA dmem addr))).
          replace (szNormZ (_ _ (_ _ val))) with (szNormZ val).
          2: { subst val. specialize (DMEM_FORMAT addr).
            destruct (hselectA dmem addr); eauto.
            destruct DMEM_FORMAT as [? ->]. eauto. }
          subst val. rewrite <- LOADED_WORD_REL. cbn.

          rewrite Hload in Hloaded_word. injection Hloaded_word as <-.
          pose proof (LittleEndian.combine_bound loaded) as Hrange.
          set (a := LittleEndian.combine_deprecated 4 loaded) in Hrange |- *.
          clearbody a. clear -Hrange.

          unfold word.wrap, BitOps.signExtend. cbn.
          rewrite Zdiv.Zminus_mod_idemp_l. replace (a + _ - _) with a; [|lia].
          rewrite Z.mod_small; lia.
        }

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* Now we extract the f2 value from Hrun to prove the goal. *)
        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. rewrite word.unsigned_of_Z. exact LOADED_REL.
        + (* RF_FORMAT *) clear -RF_FORMAT DMEM_FORMAT. subst loaded_sz.
          set (addr := (BitOps.bitSlice (szNorm calculated_sz) 2 32)).
          specialize (DMEM_FORMAT addr). destruct (hselectA dmem addr).
          1,3,4: (eapply is_formatted_update_bits; eauto; reflexivity).
          destruct DMEM_FORMAT as [? ->]. cbn. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Decode.Lbu rd rs1 (BitOps.signExtend 12 imm_i) *)
        (* get rs1's register value (base address). *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        set (loaded_z := BitOps.bitSlice _ 0 8) in Hsf2.
        set (calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend _ imm_i))) in Hrun.
        unfold Machine.loadByte, IsRiscvProgram, loadN, Monads.Bind, Monads.OStateOperations.get, Monads.OState_Monad, Monads.Return in Hrun.

        (* check the alignment of the load address. *)
        destruct (assert_aligned calculated_w f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> LOAD_ALIGNED]. clear Haddr_aligned.

        (* use mem_rel to get relation for the loaded word *)
        specialize (Hload_helper _ _ Hget_rs1 LOAD_ALIGNED) as (loaded_word & Hloaded_word & LOADED_WORD_REL).
        progress fold calculated_w in Hloaded_word.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn -[calculated_w TupleMemory.load_bytes Machine.setRegister] in Hrun.
        destruct (TupleMemory.load_bytes _ f1_data_mem calculated_w) as [loaded|] eqn: Hload in Hrun. 2: { discriminate Hrun. }
        progress cbn -[Machine.setRegister] in Hrun.

        (* show that the loaded byte is related. *)
        assert (word.wrap (LittleEndian.combine 1 loaded)
                  = szNormZ (szCastV #{32,32,true} #{loaded_z,32,false})) as LOADED_REL.
        { unfold szCastV. cbn. clear -word_ok DMEM_FORMAT Hload Hloaded_word LOADED_WORD_REL.
          subst loaded_z. set (loaded_word_sz := hbits (hselectA _ _)) in LOADED_WORD_REL |- *.
          cbn. unfold szCast'; cbn.  unfold szNormS, szNormZ; cbn.
          replace (szNorm (szCastV #{32, _, _} loaded_word_sz)) with (szNormZ loaded_word_sz).
          2: { subst loaded_word_sz. symmetry. eapply sznorm_cast_hbits_formatted_unsigned; eauto. }
          rewrite <- LOADED_WORD_REL.
          unfold word.wrap. repeat f_equal.

          (* simplify TupleMemory.load_bytes. *)
          unfold TupleMemory.load_bytes, map.getmany_of_tuple in *. cbn -[calculated_w] in Hloaded_word, Hload.
          do 4 let H := fresh Hget in destruct (map.get f1_data_mem _) eqn: H in Hloaded_word; [|discriminate Hloaded_word].
          rewrite Hget in Hload.
          inversion Hload. inversion Hloaded_word.

          (* simplify goal *)
          rewrite BitOps.bitSlice_alt; [|lia]. unfold BitOps.bitSlice'. cbn.
          change (?a / 2 ^ 0) with (a / 1). rewrite Z.div_1_r.
          rewrite 2!combine_alt. cbn.
          pose proof (byte.unsigned_range b).
          remember (byte.unsigned b) as B eqn: HeqB. clear HeqB.
          rewrite <- Zdiv.Zplus_mod_idemp_r. rewrite !(Z.mul_comm (2 ^ 8)).
          rewrite Z.mod_mul; [|lia]. do 2 (replace (B + _) with B; [|lia]).
          rewrite Z.mod_small; lia.
        }

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* Now we extract the f2 value from Hrun to prove the goal. *)
        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. rewrite word.unsigned_of_Z. exact LOADED_REL.
        + (* RF_FORMAT *) unfold szCast'. cbn. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Decode.Lhu rd rs1 (BitOps.signExtend 12 imm_i) *)
        (* get rs1's register value (base address). *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        specialize (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        set (loaded_sz := #{BitOps.bitSlice _ 0 16, 32, false}) in Hsf2.
        set (calculated_w := Utility.add rsv1_w (Utility.ZToReg (BitOps.signExtend _ imm_i))) in Hrun.
        unfold Machine.loadHalf, IsRiscvProgram, loadN, Monads.Bind, Monads.OStateOperations.get, Monads.OState_Monad, Monads.Return in Hrun.

        (* check the alignment of the load address. *)
        destruct (assert_aligned calculated_w f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> LOAD_ALIGNED]. clear Haddr_aligned.

        (* use mem_rel to get relation for the loaded word *)
        specialize (Hload_helper _ _ Hget_rs1 LOAD_ALIGNED) as (loaded_word & Hloaded_word & LOADED_WORD_REL).
        progress fold calculated_w in Hloaded_word.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn -[calculated_w TupleMemory.load_bytes Machine.setRegister] in Hrun.
        destruct (TupleMemory.load_bytes _ f1_data_mem calculated_w) as [loaded|] eqn: Hload in Hrun. 2: { discriminate Hrun. }
        progress cbn -[Machine.setRegister] in Hrun.

        (* show that the loaded half-byte is related. *)
        assert (word.wrap (LittleEndian.combine 2 loaded)
                  = szNormZ (szCastV #{32, 32, true} loaded_sz)) as LOADED_REL.
        { clear -word_ok DMEM_FORMAT Hload Hloaded_word LOADED_WORD_REL.
          subst loaded_sz. set (loaded_word_sz := hbits (hselectA _ _)) in LOADED_WORD_REL |- *.
          cbn. unfold szCast'; cbn.  unfold szNormS, szNormZ; cbn.
          replace (szNorm (szCastV _ loaded_word_sz)) with (szNormZ loaded_word_sz).
          2: { subst loaded_word_sz. symmetry. eapply sznorm_cast_hbits_formatted_unsigned; eauto. }
          rewrite <- LOADED_WORD_REL.
          unfold word.wrap. repeat f_equal.

          (* simplify TupleMemory.load_bytes. *)
          unfold TupleMemory.load_bytes, map.getmany_of_tuple in *. cbn -[calculated_w] in Hloaded_word, Hload.
          do 4 let H := fresh Hget in destruct (map.get f1_data_mem _) eqn: H in Hloaded_word; [|discriminate Hloaded_word].
          rewrite Hget, Hget0 in Hload.
          inversion Hload. inversion Hloaded_word.

          (* simplify goal *)
          rewrite BitOps.bitSlice_alt; [|lia]. unfold BitOps.bitSlice'. cbn.
          change (?a / 2 ^ 0) with (a / 1). rewrite Z.div_1_r.
          rewrite 2!combine_alt. cbn.
          pose proof (byte.unsigned_range b).
          pose proof (byte.unsigned_range b0).
          remember (byte.unsigned b) as B eqn: HeqB. clear HeqB.
          remember (byte.unsigned b0) as B0 eqn: HeqB0. clear HeqB0.
          rewrite !Z.mul_add_distr_l. rewrite !Z.mul_assoc. replace (2^8 * 2^8) with (2 ^ 16); [|lia].
          rewrite !Z.add_assoc.
          do 2 (replace (_ * 0) with 0; [|lia]). rewrite !Z.add_0_r.
          rewrite <- Zdiv.Zplus_mod_idemp_r.
          rewrite Znumtheory.Zdivide_mod with (a := 2^16 * _ * _). 2: { rewrite <- Z.mul_assoc. eapply Z.divide_factor_l. }
          rewrite Z.add_0_r.

          rewrite <- Zdiv.Zplus_mod_idemp_r. rewrite Z.mul_comm with (n := (2 ^ 16)).
          rewrite Z.mod_mul; [|lia]. rewrite Z.add_0_r.
          rewrite Z.mod_small; lia.
        }

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* Now we extract the f2 value from Hrun to prove the goal. *)
        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. rewrite word.unsigned_of_Z. exact LOADED_REL.
        + (* RF_FORMAT *) unfold loaded_sz. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Fence. Not supported. *)
        discriminate Hrun.
      - (* Case: inst = Fence_i. no_op. *)
        cbn in Hrun. injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat split; eauto.
      - (* Case: inst = Addi rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        (* process Machine.setRegister *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. setoid_rewrite CALCULATED_REL; [|eauto]. rewrite CALCULATED_FORMAT. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Slti rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) clear -RF_REL RF_REL' word_ok RSV1_FORMAT RSV1_REL.
          set (b1 := Utility.signed_less_than _ _) in RF_REL'.
          set (b2 := _ <? _).
          enough (b1 = b2) as <-. { destruct b1; cbn; (eapply RF_REL'; [eauto..|]; cbn; rewrite word.unsigned_of_Z; reflexivity). }
          subst b1 b2. clear -word_ok RSV1_REL RSV1_FORMAT.
          cbn. rewrite word.signed_lts. rewrite word.signed_of_Z. rewrite word.signed_eq_swrap_unsigned.
          rewrite RSV1_REL.
          unfold word.swrap, szNormS, szNormZ, BitOps.signExtend. rewrite RSV1_FORMAT. cbn.
          f_equal.
          replace (imm_i mod 2 ^ 12) with imm_i. 2: { subst imm_i. rewrite mod_bitSlice_fit; lia. }
          set (A := (imm_i + 2 ^ 11) mod 2 ^ 12).
          set (B := A - 2 ^ 11).
          assert (0 <= A < 2 ^ 12). { eapply Z.mod_pos_bound. lia. }
          rewrite Z.mod_small; [|lia]. lia.
        + (* RF_FORMAT *) dest_if; cbn; eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sltiu rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) clear -RF_REL RF_REL' word_ok RSV1_FORMAT RSV1_REL.
          set (b1 := Utility.ltu _ _) in RF_REL'.
          set (b2 := _ <? _).
          enough (b1 = b2) as <-. { destruct b1; cbn; (eapply RF_REL'; [eauto..|]; cbn; rewrite word.unsigned_of_Z; reflexivity). }
          subst b1 b2. clear -word_ok RSV1_REL RSV1_FORMAT.
          cbn. rewrite word.unsigned_ltu. rewrite word.unsigned_of_Z.
          rewrite RSV1_REL.
          f_equal.
          * rewrite RSV1_FORMAT. reflexivity.
          * unfold word.wrap, szNormS, szNormZ, BitOps.signExtend. cbn.
          replace (imm_i mod 2 ^ 12) with imm_i. 2: { subst imm_i. rewrite mod_bitSlice_fit; lia. }
          reflexivity.
        + (* RF_FORMAT *) dest_if; cbn; eapply is_formatted_update_bits; eauto.
      - (* Case: inst =  Xori rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_xor, word.unsigned_of_Z. rewrite RSV1_REL.
          rewrite RSV1_FORMAT.
          unfold word.wrap, szBXor, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          do 2 f_equal; [|do 2 f_equal].
          * rewrite Zdiv.Zmod_mod. reflexivity.
          * subst imm_i. rewrite mod_bitSlice_fit; lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Ori rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_or, word.unsigned_of_Z. rewrite RSV1_REL.
          rewrite RSV1_FORMAT.
          unfold word.wrap, szBXor, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          do 2 f_equal; [|do 2 f_equal].
          * rewrite Zdiv.Zmod_mod. reflexivity.
          * subst imm_i. rewrite mod_bitSlice_fit; lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Andi rd rs1 imm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_and, word.unsigned_of_Z. rewrite RSV1_REL.
          rewrite RSV1_FORMAT.
          unfold word.wrap, szBXor, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          do 2 f_equal; [|do 2 f_equal].
          * rewrite Zdiv.Zmod_mod. reflexivity.
          * subst imm_i. rewrite mod_bitSlice_fit; lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Slli rd rs1 shamt6 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* the highest bit of shamt6 should have been 0 for the decoded value to be Slli. *)
        rename CASE into shamtHi_zero. rewrite Bool.orb_false_r, Z.eqb_eq in shamtHi_zero.
        specialize (HshamtHi_zero shamtHi_zero) as [-> ->].

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_slu; rewrite word.unsigned_of_Z. 2: { unfold word.wrap. rewrite Z.mod_small; lia. }
          rewrite RSV1_REL. rewrite RSV1_FORMAT.
          unfold word.wrap, szBXor, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          rewrite Z.mod_small with (a := shamt5) by lia. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Srli rd rs1 shamt6 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* the highest bit of shamt6 should have been 0 for the decoded value to be Srli. *)
        rename CASE into shamtHi_zero. rewrite Bool.orb_false_r, Z.eqb_eq in shamtHi_zero.
        specialize (HshamtHi_zero shamtHi_zero) as [-> ->].
        rewrite !Z.mul_0_l in Hsf2. cbn in Hsf2.

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_sru; rewrite word.unsigned_of_Z. 2: { unfold word.wrap. rewrite Z.mod_small; lia. }
          rewrite RSV1_REL. rewrite RSV1_FORMAT.
          unfold word.wrap, szBXor, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          do 2 (rewrite Z.mod_small with (a := shamt5); [|lia]). reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Srai rd rs1 shamt6 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        epose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        (* the highest bit of shamt6 should have been 0 for the decoded value to be Srli. *)
        rename CASE into shamtHi_zero. rewrite Bool.orb_false_r, Z.eqb_eq in shamtHi_zero.
        specialize (HshamtHi_zero shamtHi_zero) as [-> ->].
        change (16 * 2) with 32 in Hsf2. cbn in Hsf2.

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.

          rewrite RSV1_FORMAT.
          (* we first have to change the goal from unsigned equality to signed equality. *)
          unfold word.wrap, szBSar, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          change (?a mod 2 ^ 32) with (word.wrap a).
          rewrite <- word.unsigned_of_Z.
          f_equal. eapply word.signed_inj.

          rewrite word.signed_srs. 2: { rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; lia. }
          rewrite word.signed_of_Z, word.unsigned_of_Z.
          rewrite word.signed_eq_swrap_unsigned. rewrite RSV1_REL, RSV1_FORMAT.
          do 2f_equal. unfold word.wrap. rewrite Z.mod_small; [|lia].
          reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT. reflexivity.
      - (* Case: inst =  Auipc *)
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_add, word.unsigned_of_Z. rewrite PC_REL.
          unfold word.wrap, BitOps.signExtend, szNormZ; cbn.
          rewrite Zdiv.Zplus_mod_idemp_l, Zdiv.Zplus_mod_idemp_r.
          rewrite <- Z.add_sub_swap. rewrite <- Z.add_sub_assoc. rewrite Zdiv.Zplus_mod_idemp_l.
          rewrite Z.mod_small with (a := imm_u); [|lia].
          replace (Z.shiftl imm_u 12 + 2 ^ 31 + (pcv_z - 2 ^ 31)) with (Z.shiftl imm_u 12 + pcv_z) by lia.
          cbv [szBin szNorm szNormZ]; cbn.
          rewrite Z.add_mod_idemp_l,  Z.add_mod_idemp_r by lia.
          f_equal. lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sb rs1 rs2 simm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        cbn in Hrun.

        (* check the alignment of the address. *)
        destruct (assert_aligned _ f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> ADDR_ALIGNED]. clear Haddr_aligned.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn in Hrun.
        destruct (TupleMemory.store_bytes 1 f1_data_mem _) as [f2_data_mem|] eqn: Hstore in Hrun. 2: { discriminate Hrun. }
        unfold TupleMemory.store_bytes in Hstore. destruct (TupleMemory.load_bytes 1 _ _) in Hstore; [|discriminate Hstore].
        unfold TupleMemory.unchecked_store_bytes, map.putmany_of_tuple, LittleEndian.split_deprecated in Hstore. cbn in Hstore.
        injection Hstore as <-.

        progress change (BitOps.bitSlice 0 0 2) with 0 in Hsf2.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
        + (* DMEM_REL *) specialize (STORE_ADDR_REL _ _ Hget_rs1).
          set (store_addr_w := word.add rsv1_w (word.of_Z (BitOps.signExtend 12 simm12))).
          fold store_addr_w in STORE_ADDR_REL, ADDR_ALIGNED. cbn in STORE_ADDR_REL.
           rewrite !mod_bitSlice_small by lia.

          clear -DMEM_REL DMEM_FORMAT STORE_ADDR_REL RSV2_REL RSV2_FORMAT ADDR_ALIGNED word_ok mem_ok.
          set (byte_1_z := (BitOps.bitSlice (szNorm rsv2_sz) 0 8)).
          set (byte_1_b := byte.of_Z (word.unsigned rsv2_w)).

          assert (byte.unsigned byte_1_b = byte_1_z) as BYTE_1_REL.
          { subst byte_1_z byte_1_b. rewrite BitOps.bitSlice_alt by lia. rewrite byte.unsigned_of_Z.
            unfold BitOps.bitSlice', byte.wrap. rewrite RSV2_REL. rewrite Z.div_1_r. rewrite RSV2_FORMAT; reflexivity. }

          assert (store_addr_z = 4 * store_ind) as Hstore_w_ind.
          { subst store_ind. symmetry. rewrite Z.mul_comm. eapply ZLib.Z.div_mul_undo; [lia|]. rewrite <- STORE_ADDR_REL. eauto. }
          clearbody store_ind store_addr_z. rewrite <- STORE_ADDR_REL in *. clear STORE_ADDR_REL.

          intros w ind Hw_ind. specialize (DMEM_REL w ind Hw_ind) as (prev_tup & Hprev_tup & Hprev_tup_combine).

          destruct (Z.eq_dec ind store_ind) as [-> | NEQ].
          * assert (w = store_addr_w) as ->. { eapply word.unsigned_inj. lia. }
            unfold TupleMemory.load_bytes, map.getmany_of_tuple in Hprev_tup. cbn in Hprev_tup.
            do 4 (destruct (map.get _ _) as [?b|] eqn: ?Hb in Hprev_tup; [|discriminate Hprev_tup]).
            eexists.
            (* exists {| pair._1 := byte_1_b; pair._2 := {| pair._1 := b0; pair._2 := {| pair._1 := b1; pair._2 := {| pair._1 := b2; pair._2 := tt |} |} |} |}. *)
            split.
            { (* The word in store_addr_w is same as previous except for that the lowest byte is set to byte_1_b. *)
              unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.
              rewrite map.get_put_same.
              do 3 (rewrite map.get_put_diff; [|
                intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
                rewrite !word.unsigned_add, Hw_ind, word.unsigned_of_Z, Z.mul_comm with (m := store_ind), Zdiv.Z_mod_mult in Heq; unfold word.wrap in Heq;
                replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
                rewrite ?Z.add_mod_idemp_l with (a := store_ind * 4 + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
                (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]);
                rewrite !Z.add_comm with (m := 1) in Heq; rewrite ?Z.add_assoc in Heq by lia;
                rewrite Zdiv.Z_mod_plus_full in Heq; discriminate Heq]).
              cbn.
              rewrite Hb0, Hb1, Hb2. reflexivity.
            }
            { injection Hprev_tup as <-. cbn. rewrite hselectA_single_upd_bits. cbn.
              rewrite combine_alt in Hprev_tup_combine |- *.
              replace (szNorm (szCastV #{32,32,true} _)) with (szNormZ (hbits (hselectA dmem store_ind))).
              2: { specialize (DMEM_FORMAT store_ind). destruct (hselectA _ _); try reflexivity. cbn. destruct DMEM_FORMAT as [? ->]. reflexivity. }
              setoid_rewrite <- Hprev_tup_combine. unfold szNormZ; cbn.
              rewrite Z.add_comm. rewrite <- BYTE_1_REL. rewrite Z.shiftl_mul_pow2 by lia.

              set (B := byte.unsigned b). assert (0 <= B < 2 ^ 8) by eapply byte.unsigned_range.
              set (B0 := byte.unsigned b0). assert (0 <= B0 < 2 ^ 8) by eapply byte.unsigned_range.
              set (B1 := byte.unsigned b1). assert (0 <= B1 < 2 ^ 8) by eapply byte.unsigned_range.
              set (B2 := byte.unsigned b2). assert (0 <= B2 < 2 ^ 8) by eapply byte.unsigned_range.
              set (B' := byte.unsigned byte_1_b). assert (0 <= B' < 2 ^ 8) by eapply byte.unsigned_range.
              set (BS := BitOps.bitSlice _ _ _). assert (0 <= BS < 2 ^ 24) by eapply BitOps.bitSlice_bounds.
              cbv [szBin szNorm szNormZ]; cbn.
              rewrite Z.add_mod_idemp_l by lia.
              rewrite Z.mod_small with (a := B') by lia.
              rewrite Z.mod_small by lia.
              rewrite Z.mul_comm. do 2f_equal.
              subst BS. set (A := _ B0 _).
              assert (0 <= A < 2 ^ 24) by lia.
              rewrite BitOps.bitSlice_alt by lia. unfold BitOps.bitSlice'; cbn.
              rewrite Z.mul_comm. rewrite Zdiv.Z_div_plus by lia.
              assert (B / 2 ^ 8 = 0) as ->. { eapply Zdiv.Zdiv_small. lia. }
              cbn. rewrite Z.mod_small by lia. reflexivity.
            }
          * exists prev_tup. split.
            { unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.
              rewrite 4!map.get_put_diff by
                (* By NEQ *) (intros ->; lia) ||
                (* By comparing mod4 results *)
                (intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
                rewrite !word.unsigned_add, Hw_ind, Hstore_w_ind, word.unsigned_of_Z, Z.mul_comm with (m := store_ind), Zdiv.Z_mod_mult in Heq; unfold word.wrap in Heq;
                replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
                rewrite ?Z.add_mod_idemp_l with (a := 4 * ind + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
                (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]);
                rewrite !Z.add_comm with (m := 1) in Heq; rewrite ?Z.add_assoc in Heq by lia; rewrite Z.mul_comm in Heq;
                rewrite Zdiv.Z_mod_plus_full in Heq; discriminate Heq
                ).

              eexact Hprev_tup. }
            { cbn. rewrite hselectA_single_upd_neq by auto. eexact Hprev_tup_combine. }
        + (* DMEM_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sh rs1 rs2 simm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        cbn in Hrun.

        (* check the alignment of the address. *)
        destruct (assert_aligned _ f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> ADDR_ALIGNED]. clear Haddr_aligned.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn in Hrun.
        destruct (TupleMemory.store_bytes 2 f1_data_mem _) as [f2_data_mem|] eqn: Hstore in Hrun. 2: { discriminate Hrun. }
        unfold TupleMemory.store_bytes in Hstore. destruct (TupleMemory.load_bytes 2 _ _) in Hstore; [|discriminate Hstore].
        unfold TupleMemory.unchecked_store_bytes, map.putmany_of_tuple, LittleEndian.split_deprecated in Hstore. cbn in Hstore.
        injection Hstore as <-.

        progress change (BitOps.bitSlice 1 0 2) with 1 in Hsf2.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
        + (* DMEM_REL *) specialize (STORE_ADDR_REL _ _ Hget_rs1).
          set (store_addr_w := word.add rsv1_w (word.of_Z (BitOps.signExtend 12 simm12))).
          fold store_addr_w in STORE_ADDR_REL, ADDR_ALIGNED. cbn in STORE_ADDR_REL.
           rewrite !mod_bitSlice_small by lia.

          clear -DMEM_REL DMEM_FORMAT STORE_ADDR_REL RSV2_REL RSV2_FORMAT ADDR_ALIGNED word_ok mem_ok.
          set (byte_1_b := byte.of_Z (word.unsigned rsv2_w)).
          set (byte_2_b := byte.of_Z (Z.shiftr (word.unsigned rsv2_w) 8)).

          assert (store_addr_z = 4 * store_ind) as Hstore_w_ind.
          { subst store_ind. symmetry. rewrite Z.mul_comm. eapply ZLib.Z.div_mul_undo; [lia|]. rewrite <- STORE_ADDR_REL. eauto. }
          clearbody store_ind store_addr_z. rewrite <- STORE_ADDR_REL in *. clear STORE_ADDR_REL.

          intros w ind Hw_ind. specialize (DMEM_REL w ind Hw_ind) as (prev_tup & Hprev_tup & Hprev_tup_combine).

          destruct (Z.eq_dec ind store_ind) as [-> | NEQ].
          * assert (w = store_addr_w) as ->. { eapply word.unsigned_inj. lia. }
            unfold TupleMemory.load_bytes, map.getmany_of_tuple in Hprev_tup. cbn in Hprev_tup.
            do 4 (destruct (map.get _ _) as [?b|] eqn: ?Hb in Hprev_tup; [|discriminate Hprev_tup]).
            eexists.
            split.
            { (* The word in store_addr_w is same as previous except for that the lower two bytes. *)
              unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.
              1: rewrite map.get_put_same, map.get_put_diff, map.get_put_same, !map.get_put_diff.
              2-6: intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
              rewrite !word.unsigned_add, Hw_ind, word.unsigned_of_Z, Z.mul_comm with (m := store_ind), ?Zdiv.Z_mod_mult in Heq; unfold word.wrap in Heq;
              replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
              rewrite ?Z.add_mod_idemp_l with (a := store_ind * 4 + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
              (repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]));
              rewrite !Z.add_comm with (m := 1) in Heq; rewrite ?Z.add_assoc in Heq by lia;
              rewrite ?Zdiv.Z_mod_plus_full in Heq; discriminate Heq.

              rewrite Hb1, Hb2. reflexivity.
            }
            { injection Hprev_tup as <-. cbn. rewrite hselectA_single_upd_bits. cbn.
              rewrite combine_alt in Hprev_tup_combine |- *.
              replace (szNorm (szCastV #{32,32,true} _)) with (szNormZ (hbits (hselectA dmem store_ind))).
              2: { specialize (DMEM_FORMAT store_ind). destruct (hselectA _ _); try reflexivity. cbn. destruct DMEM_FORMAT as [? ->]. reflexivity. }
              setoid_rewrite <- Hprev_tup_combine. unfold szNormZ; cbn.
              rewrite Z.shiftl_mul_pow2 by lia.

              (* rewrite Z.add_comm. rewrite <- BYTE_1_REL.  *)

              set (B := byte.unsigned b). assert (0 <= B < 2 ^ 8) by eapply byte.unsigned_range.
              set (B0 := byte.unsigned b0). assert (0 <= B0 < 2 ^ 8) by eapply byte.unsigned_range.
              set (B1 := byte.unsigned b1). assert (0 <= B1 < 2 ^ 8) by eapply byte.unsigned_range.
              set (B2 := byte.unsigned b2). assert (0 <= B2 < 2 ^ 8) by eapply byte.unsigned_range.
              set (BT0 := byte.unsigned byte_1_b). assert (0 <= BT0 < 2 ^ 8) by eapply byte.unsigned_range.
              set (BT1 := byte.unsigned byte_2_b). assert (0 <= BT1 < 2 ^ 8) by eapply byte.unsigned_range.
              replace (B2 + _) with B2 by lia.
              rewrite !Z.mul_add_distr_l, !Z.add_assoc, !Z.mul_assoc.
              set (BS1 := BitOps.bitSlice _ _ _). assert (0 <= BS1 < 2 ^ 16) by eapply BitOps.bitSlice_bounds.
              set (BS2 := BitOps.bitSlice _ _ _). assert (0 <= BS2 < 2 ^ 16) by eapply BitOps.bitSlice_bounds.
              unfold szBin, szNorm, szNormZ; cbn.
              rewrite Z.add_mod_idemp_l by lia.
              rewrite Z.mod_small with (a := BS2) by lia.
              rewrite Z.mod_small by lia.
              assert (BS2 = BT0 + 2 ^ 8 * BT1) as <-.
              { subst BS2 BT0 BT1 byte_1_b byte_2_b. rewrite RSV2_REL. rewrite BitOps.bitSlice_alt by lia. unfold BitOps.bitSlice'.
                rewrite RSV2_FORMAT. unfold szNorm, szNormZ; cbn. rewrite Z.div_1_r.
                set (A := rsv2_z mod 2 ^ 32).
                rewrite !byte.unsigned_of_Z. unfold byte.wrap. rewrite Z.shiftr_div_pow2 by lia.

                unshelve epose proof (Zdiv.Z_div_mod A (2^8) _) as Hdiv; [lia|].
                unfold Z.div, Z.modulo at 2. destruct (Z.div_eucl A (2 ^ 8)) as [q r]. destruct Hdiv as [-> ?].

                unshelve epose proof (Zdiv.Z_div_mod q (2^8) _) as Hdiv; [lia|].
                unfold Z.modulo at 2. destruct (Z.div_eucl q (2 ^ 8)) as [q' r']. destruct Hdiv as [-> ?].
                replace (2 ^ 8 * (2 ^ 8 * q' + r') + r) with (2 ^ 8 * r' + r + q' * 2 ^ 16) by lia.
                rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_mul by lia.
                rewrite Z.mod_small by lia. lia.
              }
              change (2^8 * 2^8) with (2^16). rewrite <- Z.add_assoc. rewrite Z.add_comm with (m := BS2). f_equal.
              replace (2 ^ 16 * B1 + 2 ^ 16 * 2 ^ 8 * B2) with (2 ^ 16 * (B1 + 2 ^ 8 * B2)) by lia. rewrite Z.mul_comm. f_equal.

              subst BS1. rewrite BitOps.bitSlice_alt by lia. unfold BitOps.bitSlice'; cbn.
              replace ((B + 2 ^ 8 * B0 + 2 ^ 8 * 2 ^ 8 * B1 + 2 ^ 8 * 2 ^ 8 * 2 ^ 8 * B2))
                  with (B + 2 ^ 8 * B0 + (B1 + 2^8 * B2) * 2 ^ 16) by lia. rewrite Zdiv.Z_div_plus by lia.
              rewrite Zdiv.Zdiv_small by lia. rewrite Z.mod_small by lia. lia.
            }
          * exists prev_tup. split.
            { unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.

              rewrite !map.get_put_diff.
              9: { (* w = store_addr_w. by NEQ *)intros ->. lia. }
              6: {
                (* w + 1 = store_addr_w + 1. by NEQ *)
                intros Heq.
                apply f_equal with (f:= fun x => word.sub x (word.of_Z 1)) in Heq.
                rewrite !word.word_sub_add_l_same_r in Heq. subst w. lia.
              }
              2-7:
                (* neq by mod 4 comparison *)
                intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
                rewrite !word.unsigned_add, Hw_ind, Hstore_w_ind, word.unsigned_of_Z, ?Z.mul_comm with (n := 4), ?Zdiv.Z_mod_mult in Heq; unfold word.wrap in Heq;
                replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
                rewrite ?Z.add_mod_idemp_l with (a := ind * 4 + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
                (repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]));
                rewrite !Z.add_comm with (m := 1) in Heq; rewrite ?Z.add_assoc in Heq by lia;
                rewrite ?Zdiv.Z_mod_plus_full in Heq; discriminate Heq.

              eexact Hprev_tup. }
            { cbn. rewrite hselectA_single_upd_neq by auto. eexact Hprev_tup_combine. }
        + (* DMEM_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sw rs1 rs2 simm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        cbn in Hrun.

        (* check the alignment of the address. *)
        destruct (assert_aligned _ f1) as [[[]|] ?] eqn: Haddr_aligned in Hrun. 2: { discriminate Hrun. }
        destruct (assert_aligned_success _ _ _ _ Haddr_aligned) as [-> ADDR_ALIGNED]. clear Haddr_aligned.

        (* Simplify some hypotheses. *)
        rewrite Hf1 in Hrun at 1. cbn in Hrun.
        destruct (TupleMemory.store_bytes 4 f1_data_mem _) as [f2_data_mem|] eqn: Hstore in Hrun. 2: { discriminate Hrun. }
        unfold TupleMemory.store_bytes in Hstore. destruct (TupleMemory.load_bytes 4 _ _) in Hstore; [|discriminate Hstore].
        unfold TupleMemory.unchecked_store_bytes, map.putmany_of_tuple, LittleEndian.split_deprecated in Hstore. cbn in Hstore.
        injection Hstore as <-.

        progress change (BitOps.bitSlice 2 0 2) with 2 in Hsf2.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
        + (* DMEM_REL *) specialize (STORE_ADDR_REL _ _ Hget_rs1).
          set (store_addr_w := word.add rsv1_w (word.of_Z (BitOps.signExtend 12 simm12))).
          fold store_addr_w in STORE_ADDR_REL, ADDR_ALIGNED. cbn in STORE_ADDR_REL.

          clear -DMEM_REL DMEM_FORMAT STORE_ADDR_REL RSV2_REL RSV2_FORMAT ADDR_ALIGNED word_ok mem_ok.

          assert (store_addr_z = 4 * store_ind) as Hstore_w_ind.
          { subst store_ind. symmetry. rewrite Z.mul_comm. eapply ZLib.Z.div_mul_undo; [lia|]. rewrite <- STORE_ADDR_REL. eauto. }
          clearbody store_ind store_addr_z. rewrite <- STORE_ADDR_REL in *. clear STORE_ADDR_REL.

          intros w ind Hw_ind. specialize (DMEM_REL w ind Hw_ind) as (prev_tup & Hprev_tup & Hprev_tup_combine).

          destruct (Z.eq_dec ind store_ind) as [-> | NEQ].
          * assert (w = store_addr_w) as ->. { eapply word.unsigned_inj. lia. }
            unfold TupleMemory.load_bytes, map.getmany_of_tuple in Hprev_tup. cbn in Hprev_tup.
            do 4 (destruct (map.get _ _) as [?b|] eqn: ?Hb in Hprev_tup; [|discriminate Hprev_tup]).
            eexists.
            split.
            {
              unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.
              repeat (rewrite map.get_put_same || rewrite map.get_put_diff).
              2-7: intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
              rewrite !word.unsigned_add, Hw_ind, word.unsigned_of_Z, Z.mul_comm with (m := store_ind), ?Zdiv.Z_mod_mult in Heq; unfold word.wrap in Heq;
              replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
              rewrite ?Z.add_mod_idemp_l with (a := store_ind * 4 + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
              (repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]));
              rewrite !Z.add_comm with (m := 1) in Heq; rewrite ?Z.add_assoc in Heq by lia;
              rewrite ?Zdiv.Z_mod_plus_full in Heq; discriminate Heq.
              reflexivity.
            }
            { injection Hprev_tup as <-. cbn. rewrite hselectA_single_upd_bits. cbn.
              rewrite combine_alt. cbn.
              rewrite RSV2_REL. rewrite RSV2_FORMAT. unfold szNormZ; cbn.
              set (A := rsv2_z mod _). assert (0 <= A < 2^32) by (eapply Z.mod_pos_bound; lia).
              rewrite !byte.unsigned_of_Z. unfold byte.wrap.
              rewrite !Z.shiftr_div_pow2 by lia.
              unfold Z.div, Z.modulo.
              unshelve epose proof (Zdiv.Z_div_mod A (2^8) _) as Hdiv; [lia|].
              destruct (Z.div_eucl A (2 ^ 8)) as [q0 r0]. destruct Hdiv as [-> ?].

              unshelve epose proof (Zdiv.Z_div_mod q0 (2^8) _) as Hdiv; [lia|].
              destruct (Z.div_eucl q0 (2 ^ 8)) as [q1 r1]. destruct Hdiv as [-> ?].

              unshelve epose proof (Zdiv.Z_div_mod q1 (2^8) _) as Hdiv; [lia|].
              destruct (Z.div_eucl q1 (2 ^ 8)) as [q2 r2]. destruct Hdiv as [-> ?].

              unshelve epose proof (Zdiv.Z_div_mod q2 (2^8) _) as Hdiv; [lia|].
              destruct (Z.div_eucl q2 (2 ^ 8)) as [q3 r3]. destruct Hdiv as [-> ?].
              lia.
            }
          * exists prev_tup. split.
            { unfold TupleMemory.load_bytes, map.getmany_of_tuple. cbn.

              rewrite !map.get_put_diff.
              17: { (* w = store_addr_w. by NEQ *)intros ->. lia. }
              2, 7, 12:
                (* w + i = store_addr_w + i. by NEQ *)
                intros Heq;
                repeat (apply f_equal with (f:= fun x => word.sub x (word.of_Z 1)) in Heq; rewrite !word.word_sub_add_l_same_r in Heq);
                subst w; lia.

              2-13:
                (* neq by mod 4 comparison *)
                intros Heq;
                repeat (apply f_equal with (f:= fun x => word.sub x (word.of_Z 1)) in Heq; rewrite 2!word.word_sub_add_l_same_r in Heq);

                apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
                rewrite !word.unsigned_add, Hw_ind, Hstore_w_ind, word.unsigned_of_Z in Heq; unfold word.wrap in Heq;
                replace (1 mod 2 ^ 32) with 1 in Heq by reflexivity;
                rewrite ?Z.add_mod_idemp_l with (a := 4 * _ + 1) in Heq by lia; rewrite ?Z.add_mod_idemp_l in Heq by lia;
                (repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]));
                rewrite ?Z.mul_comm with (n := 4) in Heq; rewrite ?Z.add_comm with (m := 1), ?Z.add_assoc in Heq;
                rewrite ?Zdiv.Z_mod_mult in Heq; rewrite ?Zdiv.Z_mod_plus_full in Heq;
                discriminate Heq.

                eexact Hprev_tup. }
            { cbn. rewrite hselectA_single_upd_neq by auto. eexact Hprev_tup_combine. }
        + (* DMEM_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Add rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_add, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT.
          reflexivity.
        + (* RF_FORMAT *) rewrite RSV1_FORMAT, RSV2_FORMAT. cbn. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sub rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_sub, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT.
          reflexivity.
        + (* RF_FORMAT *) rewrite RSV1_FORMAT, RSV2_FORMAT. cbn. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sll rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_slu, RSV1_REL, RSV2_REL; rewrite word.unsigned_of_Z.
          2: { unfold word.wrap. set (A := word.unsigned rsv2_w mod 2 ^ 5).
            assert (0 <= A < 32). { eapply Z.mod_pos_bound; lia. } rewrite Z.mod_small; lia. }
          rewrite RSV1_FORMAT, RSV2_FORMAT.

          cbn. unfold word.wrap, szNormZ; cbn. do 2f_equal.
          rewrite Z.mod_mod by lia.
          rewrite Z.pow_add_r with (b := 5) (c := 27); [|lia..].
          rewrite <- Znumtheory.Zmod_div_mod with (a := rsv2_z); [|lia..|]. 2: eapply Z.divide_factor_l.
          eapply Z.mod_small.
          eenough (0 <= rsv2_z mod 2 ^ 5 < 32) by lia.
          eapply Z.mod_pos_bound; lia.
        + (* RF_FORMAT *) rewrite RSV1_FORMAT, RSV2_FORMAT. cbn. eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Slt rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *)
          set (b1 := Utility.signed_less_than _ _) in RF_REL'.
          set (b2 := _ <? _).
          enough (b1 = b2) as <-. { destruct b1; cbn; (eapply RF_REL'; [eauto..|]; cbn; rewrite word.unsigned_of_Z; reflexivity). }
          subst b1 b2. cbn.
          rewrite word.signed_lts. rewrite !word.signed_eq_swrap_unsigned.
          rewrite RSV1_REL, RSV2_REL.
          unfold word.swrap, szNormS, szNormZ, BitOps.signExtend. rewrite RSV1_FORMAT, RSV2_FORMAT. cbn.
          reflexivity.
        + (* RF_FORMAT *) dest_if; cbn; eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Sltu rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *)
          set (b1 := Utility.ltu _ _) in RF_REL'.
          set (b2 := _ <? _).
          enough (b1 = b2) as <-. { destruct b1; cbn; (eapply RF_REL'; [eauto..|]; cbn; rewrite word.unsigned_of_Z; reflexivity). }
          subst b1 b2.
          cbn. rewrite word.unsigned_ltu, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
        + (* RF_FORMAT *) dest_if; cbn; eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Xor rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          rewrite word.unsigned_xor, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT.
          unfold word.wrap, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          rewrite !Z.mod_mod; [|lia..]. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
      - (* Case: inst = Srl rd rs1 rs2  *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.
          assert (0 <= word.unsigned rsv2_w mod 2 ^ 5 < 32). { eapply Z.mod_pos_bound; lia. }
          rewrite word.unsigned_sru; rewrite word.unsigned_of_Z; unfold word.wrap; rewrite Z.mod_small with (a := word.unsigned _ mod _); [|lia..].
          rewrite RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT.
          unfold word.wrap, szNormZ; cbn. unfold szNormZ; cbn.
          rewrite <- Znumtheory.Zmod_div_mod with (a := rsv2_z) (m := 2 ^ 32); [|lia..|].
          2: { rewrite Z.pow_add_r with (b := 5) (c := 27); [|lia..]. eapply Z.divide_factor_l. }
          rewrite Z.mod_mod; [|lia]. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
      - (* Case: inst = Sra rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|]. cbn.

          rewrite RSV1_FORMAT.
          (* we first have to change the goal from unsigned equality to signed equality. *)
          unfold word.wrap, szBSar, szNormZ; cbn. unfold szNormS, szNormZ; cbn.
          change (?a mod 2 ^ 32) with (word.wrap a).
          rewrite <- word.unsigned_of_Z.
          f_equal. eapply word.signed_inj.

          assert (0 <= word.unsigned rsv2_w mod 2 ^ 5 < 32). { eapply Z.mod_pos_bound; lia. }
          rewrite word.signed_srs. 2: { rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; lia. }
          rewrite word.signed_of_Z, word.unsigned_of_Z.
          rewrite word.signed_eq_swrap_unsigned. rewrite RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT.
          do 2f_equal. unfold word.wrap, szNormZ; cbn.

          rewrite <- Znumtheory.Zmod_div_mod with (a := rsv2_z) (m := 2 ^ 32); [|lia..|].
          2: { rewrite Z.pow_add_r with (b := 5) (c := 27); [|lia..]. eapply Z.divide_factor_l. }

          rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [reflexivity|].
          enough (0 <= rsv2_z mod 2 ^ 5 < 32) by lia.
          eapply Z.mod_pos_bound. lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
      - (* Case: inst = Or rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_or, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT.
          unfold word.wrap, szNormZ; cbn. unfold szNormZ; cbn.
          rewrite !Z.mod_mod; [|lia..]. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
      - (* Case: inst = And rd rs1 rs2 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun.
        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_and, RSV1_REL, RSV2_REL.
          rewrite RSV1_FORMAT, RSV2_FORMAT.
          unfold word.wrap, szNormZ; cbn. unfold szNormZ; cbn.
          rewrite !Z.mod_mod; [|lia..]. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity.
      - (* Case: inst = Lui rd imm20 (= imm_u) *)
        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        cbn in Hrun. injection Hrun as ?. subst f1 f2 sf2 pcv; cbn.
        eexists. repeat ssplit; auto.
        + (* RF_REL *) eapply RF_REL'; [eauto..|].
          cbn. rewrite word.unsigned_of_Z.
          unfold word.wrap, BitOps.signExtend, szNormZ; cbn.
          rewrite Z.mod_small with (a := imm_u) by lia.
          rewrite Zdiv.Zminus_mod_idemp_l. f_equal. lia.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Beq rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := _ rsv1_w rsv2_w) in Hrun.
        set (b2 := _ (szNorm rsv1_sz) (szNorm rsv2_sz)) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.unsigned_eqb, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity. }

        destruct b1.
        1: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Bne rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := _ rsv1_w rsv2_w) in Hrun.
        set (b2 := _ (szNorm rsv1_sz) (szNorm rsv2_sz)) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.unsigned_eqb, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity. }

        destruct b1; cbn in Hrun.
        2: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Blt rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := _ rsv1_w rsv2_w) in Hrun.
        set (b2 := _ <? _) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.signed_lts, !word.signed_eq_swrap_unsigned, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity. }

        destruct b1; cbn in Hrun.
        1: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Bge rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := negb (_ rsv1_w rsv2_w)) in Hrun.
        set (b2 := _ >=? _) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.signed_lts, !word.signed_eq_swrap_unsigned, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. cbn.
          unfold Z.ltb, Z.geb. destruct (_ ?= _); reflexivity. }

        destruct b1; cbn in Hrun.
        1: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Bltu rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := (_ rsv1_w rsv2_w)) in Hrun.
        set (b2 := _ <? _) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.unsigned_ltu, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. reflexivity. }

        destruct b1; cbn in Hrun.
        1: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Bgeu rs1 rs2 sbimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs2 _) as [[rsv2_w|] ?] eqn: Hget_rs2 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv2 _ _ Hget_rs2) as (-> & RSV2_REL).
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        unfold Monads.when in Hrun. cbn in Hrun.
        set (b1 := negb (word.ltu _ rsv2_w)) in Hrun.
        set (b2 := _ >=? _) in Hsf2.

        assert (b1 = b2) as <-.
        { subst b1 b2. rewrite word.unsigned_ltu, RSV1_REL, RSV2_REL. rewrite RSV1_FORMAT, RSV2_FORMAT. cbn.
          unfold Z.ltb, Z.geb. destruct (_ ?= _); reflexivity. }

        destruct b1; cbn in Hrun.
        1: destruct (_ : bool) in Hrun; [discriminate Hrun|].
        all: injection Hrun as ?; subst f1 f2 sf2 pcv; cbn; eexists; (repeat ssplit; auto).
      - (* Case: inst = Jalr rd rs1 oimm12 *)
        destruct (Machine.getRegister (M := Monads.OState RiscvMachine') rs1 _) as [[rsv1_w|] ?] eqn: Hget_rs1 in Hrun; [|discriminate Hrun].
        destruct (Hget_rsv1 _ _ Hget_rs1) as (-> & RSV1_REL).

        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        cbn -[Machine.setRegister] in Hrun.
        destruct (_ : bool) in Hrun; [discriminate Hrun|].

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
        + (* PC_REL *)
          rewrite word.unsigned_and. setoid_rewrite CALCULATED_REL; [|eauto].
          rewrite word.unsigned_xor, !word.unsigned_of_Z.
          rewrite CALCULATED_FORMAT. unfold word.wrap, szNormZ, szUNeg; cbn. unfold szNormZ; cbn.
          rewrite Z.mod_small with (a := 1) by lia. rewrite Z.mod_small with (a := _ - 1) by lia.
          assert (Z.lxor 1 _ = 2 ^ 32 - 2) as -> by reflexivity.
          replace (2 ^ 32 - 1 - 1) with (2 ^ 32 - 2) by lia.
          rewrite !Z.mod_small with (a := _ - 2) by lia. rewrite !Z.mod_mod; [|lia..]. reflexivity.
        + (* RF_REL *) eapply RF_REL'; eauto. rewrite word.unsigned_add, word.unsigned_of_Z. setoid_rewrite <- NEXT_PC. rewrite Hpc_simpl. reflexivity.
        + (* PC_FORMAT *) rewrite CALCULATED_FORMAT. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = Jal rd jimm20 *)
        destruct (Machine.getPC (M := Monads.OState RiscvMachine') f1) as [[pc_w|] ?] eqn: Hget_pc in Hrun; [|discriminate Hrun].
        cbn in Hget_pc. rewrite Hf1 in Hget_pc at 1. cbn in Hget_pc. injection Hget_pc as <- <-.

        cbn -[Machine.setRegister] in Hrun.
        destruct (_ : bool) in Hrun; [discriminate Hrun|].

        destruct (Machine.setRegister (M := Monads.OState RiscvMachine') rd _ f1) as [[[]|] f1_after_set] eqn: Hset_reg in Hrun; [|discriminate Hrun].
        pose proof (setRegister_success _ _ rfv _ _ Hset_reg) as (f2_regs & -> & RF_REL').

        injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
        + (* PC_REL *)
          rewrite word.unsigned_add, word.unsigned_of_Z. rewrite PC_REL.
          cbv [word.wrap szBin szNorm szNormS szNormZ BitOps.signExtend]; cbn.
          rewrite ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mod_mod by lia.
          reflexivity.
        + (* RF_REL *) eapply RF_REL'; eauto. rewrite word.unsigned_add, word.unsigned_of_Z. setoid_rewrite <- NEXT_PC. rewrite Hpc_simpl. reflexivity.
        + (* RF_FORMAT *) eapply is_formatted_update_bits; eauto.
      - (* Case: inst = InvalidI *)
        (* the decoded result is not InstructionI so it should be InstructionCSR. *)
        (* Most CSR instructions are not supported. *)
        (repeat try match (eval hnf in instruction_csr) with
        | context [if ?b then _ else _] => destruct b eqn: CASE; [|clear CASE]
        end);
        repeat (rewrite Bool.andb_true_iff in CASE; (let CASE' := fresh CASE in destruct CASE as [CASE' CASE]));
        repeat match goal with
        | H: ((?x =? ?val) = true) |- _ => unfold val in H; rewrite Z.eqb_eq in H; rewrite H in *
        end;
        cbn in Hsf2; unfold szNormZ in Hsf2; cbn in Hsf2;
        repeat (rewrite mod_bitSlice_fit in Hsf2; [|lia]).
        all : cbn in Hrun; try discriminate Hrun.
        + (* Uret *) injection Hrun as ?. subst f1 f2 sf2 pcv; cbn. eexists. repeat ssplit; auto.
    }

    (* take an inductive step *)
    gstep. subst s2. econstructor. { gfinal. left. eapply CIH. all: eauto. } all: eapply Ord.S_lt.

    Unshelve. all: exact Ord.O.
  Qed. (* 55s *)

End proof.
