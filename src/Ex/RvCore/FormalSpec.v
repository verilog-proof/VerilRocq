From Coq Require Import  ZArith.BinInt Nat Arith.EqNat Arith.PeanoNat Lia.
Require Export Ex.RvCore.Machine.
Require Import riscv.Utility.Utility riscv.Utility.Monads.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
From ITree Require Import ITree.
From FreeSim Require ModSemE.

Require Import riscv.Platform.Run.

Import ITreeNotations.
Module FormalSpec.
Section WithCtx.
  Context {word: Interface.word 32} {BW: Bitwidth 32} {MW : MachineWidth word}.
  Context {Registers: map.map Register word}.
  Context {Mem : map.map word byte}.

  Definition State : Type := RvCore.Machine.RiscvMachine (width := 32).

  Fixpoint zeroed_until (n : nat) : Mem :=
    match n with
    | 0 => map.empty
    | S n => map.put (zeroed_until n) (word.of_Z (Z.of_nat n)) Byte.x00
    end.

  Definition zeroed := zeroed_until (2 ^ 32).
  #[local] Arguments zeroed : simpl never.

  Section ZeroedHelpers.
  Context {mem_ok : map.ok Mem} {word_ok : word.ok word}.
    Lemma zeroed_until_access  n len (w : word) :
      len <= 2 ^ 32 ->
      word.unsigned w = Z.of_nat n ->
      n < len ->
        map.get (zeroed_until len) w = Some Byte.x00.
    Proof.
      intros Hlen_small Hw LT.
      induction len as [|len' IH].
      - lia.
      - destruct (Peano_dec.eq_nat_dec n len') as [->|NEQ].
        + cbn. replace (word.of_Z (Z.of_nat len')) with w. { apply map.get_put_same. }
          remember (Z.of_nat len') as z.
          apply f_equal with (f := word.of_Z (width := 32)) in Hw.
          rewrite word.of_Z_unsigned in Hw. exact Hw.
        + cbn. rewrite map.get_put_diff. { eapply IH; lia. }
          clear -Hw word_ok NEQ Hlen_small. intros H.
          apply f_equal with (f := word.unsigned) in H.
          rewrite word.unsigned_of_Z in H.
          rewrite H in Hw. clear H. unfold word.wrap in Hw.
          rewrite Z.mod_small in Hw. { eapply NEQ. eapply Znat.Nat2Z.inj. eauto. }
          split.
          * eapply Znat.Nat2Z.is_nonneg.
          * replace (2 ^ 32)%Z with (Z.of_nat (2 ^ 32)). 2: { rewrite Znat.Nat2Z.inj_pow. reflexivity. }
            eapply Znat.inj_lt. lia.
    Qed.


    Lemma zeroed_access w :
      map.get zeroed w = Some Byte.x00.
    Proof.
      assert (exists n, word.unsigned w = Z.of_nat n /\ n < 2^32) as (n&?&?).
      { pose proof (word.unsigned_range w) as H.
        remember (word.unsigned w) as v. clear Heqv.
        exists (Z.to_nat v). rewrite Znat.Z2Nat.id; [|lia].
        split; [auto|].
        replace (2 ^ 32) with (Z.to_nat (2 ^ 32)). 2: { rewrite Znat.Z2Nat.inj_pow; [reflexivity|lia..]. }
        eapply Znat.Z2Nat.inj_lt; lia.
      }
      eapply zeroed_until_access; eauto.
    Qed.

    Lemma zeroed_load_bytes n (addr : word) :
      exists tup, TupleMemory.load_bytes n zeroed addr = Some tup /\ LittleEndian.combine n tup = 0%Z.
    Proof.
      unfold TupleMemory.load_bytes, map.getmany_of_tuple.
      remember (TupleMemory.footprint addr n) as addresses eqn: H. clear H addr.
      revert addresses. induction n as [|n' IH].
      - intros. eexists. cbn. eauto.
      - intros. edestruct IH as (addresses' & Haddrs & Hcombine).
        eexists. cbn. rewrite zeroed_access, Haddrs. clear Haddrs.
        split; [reflexivity|].
        unfold LittleEndian.combine_deprecated. cbn -[Z.shiftl].
        setoid_rewrite Hcombine. reflexivity.
    Qed.

  End ZeroedHelpers.

  Definition initial_state (initial_imem: Mem): State := {|
    getRegs := map.empty;
    getPc := ZToReg 0;
    getNextPc := ZToReg 4;
    getInstMem := initial_imem;
    getDataMem := zeroed;
  |}.

  Definition run1: OState State unit :=
    fun (s : State) => Run.run1 (RVM := RvCore.Machine.IsRiscvProgramWithLeakage) (RVS := Machine.DefaultRiscvState) Decode.RV32I s.

  (* A successful leakage calculation leaves the functional execution unchanged. *)
  Lemma run1_success s s' :
    run1 s = (Some tt, s') ->
    Bind Machine.getPC (fun pc =>
      Bind (Machine.loadWord Fetch pc) (fun inst =>
        Bind (Execute.execute (Decode.decode Decode.RV32I (LittleEndian.combine 4 inst)))
          (fun _ => Machine.endCycleNormal))) s = (Some tt, s').
  Proof.
    unfold run1, Run.run1.
    cbn [Bind Return OState_Monad Machine.getPC Machine.leakEvent Machine.RVP
         IsRiscvProgramWithLeakage IsRiscvProgram OStateOperations.get].
    destruct (Machine.loadWord (RiscvProgram := IsRiscvProgram) Fetch (getPc s) s)
      as [[inst|] loaded_state]; [|discriminate].
    pose proof (leakage_preserves_state
      (Decode.decode Decode.RV32I (LittleEndian.combine 4 inst)) loaded_state) as Hstate.
    destruct (LeakageOfInstr.leakage_of_instr
      (Machine.getRegister (RiscvProgram := IsRiscvProgram))
      (Decode.decode Decode.RV32I (LittleEndian.combine 4 inst)) loaded_state)
      as [event leaked_state].
    cbn in Hstate. subst leaked_state.
    destruct event; [auto|discriminate].
  Qed.

  (* input/output events of a RISC-V cpu. *)
  Variant riscv_ioE : Type -> Type :=
  | Output (pc : Z) : riscv_ioE unit.

  #[local] Open Scope itree_scope.
  Definition riscv_itree_with_state : State -> itree (riscv_ioE +' ModSemE.eventE) void :=
      rec-fix riscv_itree_with_state' state :=
        let (ret, state') := run1 state in
        match ret with
        | None => ModSemE.triggerUB (* Error leads to UB *)
        | Some tt =>
          trigger (Output (word.unsigned state.(getPc))) ;; (* emit the executed pc. *)
          riscv_itree_with_state' state'
        end.
  Definition riscv_itree initial_imem := riscv_itree_with_state (initial_state initial_imem).

  Definition formal_initial_imem initial_imem: Mem :=
    List.fold_right (fun iv mem =>
      let addr := word.of_Z (4 * fst iv) in
      let bytes := LittleEndian.split 4 (snd iv) in
      TupleMemory.unchecked_store_bytes 4 mem addr bytes
    ) zeroed initial_imem.
End WithCtx.

#[global] Arguments zeroed_until _ _ n : simpl never.
#[global] Arguments zeroed _ _ : simpl never.

End FormalSpec.
