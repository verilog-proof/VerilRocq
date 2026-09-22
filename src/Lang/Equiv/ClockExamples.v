Require Import Coq.Lists.List Coq.Arith.PeanoNat Coq.ZArith.BinInt Coq.micromega.Lia.
Import ListNotations.
Require Import Lib.Lib Lang.Syntax Lang.Semantics Standard TrsProc ProcUpdGraph StfStd
  UpdGraph RankedGraph SourceShape ResetInjection GraphStructure ModuleEquivalence
  ModuleBridge ClockSampling UpdateCompletion ClockEquivalence.

Set Implicit Arguments.

Module SwapRegisters.
  #[local] Instance ids: vid_t_c := {| vid_t := nat |}.
  #[local] Instance idops: vid_ops := {| vid_eq_dec := Nat.eq_dec |}.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  Definition block (dst src: nat): VModuleItem :=
    VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemCommon
      (VModuleCommonItemAlways VAlwaysFF (VStatementO
        (VStatementProcTimingControl
          (VProcTimingControlEvent (VEventControlExpr (VEventExprExpr (Some VPosedge) (VExprId 2%nat))))
          (VStatementItemNonblockingAssign (VExprId dst) (VExprId src))))))).
  Definition outPort (id: nat): VAnsiPortDecl :=
    VAnsiPortDeclVar (Some (VVarPortHeaderO (Some VPortDirectionOutput)
      (VDataTypeIntVec VLogic VPackedDimsNil))) id.
  Definition circuit: VModuleDecl := VModuleDeclAnsi 3%nat VParamPortsNil
    (VAnsiPortDeclsCons (outPort 0%nat) (VAnsiPortDeclsOne (outPort 1%nat)))
    (VModuleItemsCons (block 0%nat 1%nat) (VModuleItemsOne (block 1%nat 0%nat))).
  Definition ds: Decls := declsVModuleDecl circuit.
  Definition fs: Funcs := fmapEmpty.
  Definition ms: MTrss := fmapEmpty.
  Definition ps: Processes := moduleProcs ds ms circuit.
  Definition state (a b: SZ): State := HMapStr [(0%nat,HMapBits a);(1%nat,HMapBits b)].
  Definition flops (a b: SZ): list InitState := [[(0%nat,HMapBits a)];[(1%nat,HMapBits b)]].
  Definition rows (a b: SZ): list (Process * InitState) := combine ps (flops b a).

  Lemma circuit_flat: FlatModule circuit.
  Proof. split; [reflexivity|split; repeat constructor]. Qed.

  Lemma source_swap: forall a b,
    TrsProcsRep ds fs ms (procs ps) (initState (ipsAll ps [] (flops a b)))
      (state a b) (state b a).
  Proof. intros; apply TrsProcsFix; reflexivity. Qed.

  Lemma swap_plan: forall a b, ClockPlan ds fs ms (state a b) (rows a b).
  Proof.
    intros; constructor.
    - split; [discriminate|exists HMapEmpty; split; reflexivity].
    - constructor; [split; [discriminate|exists HMapEmpty; split; reflexivity]|constructor].
  Qed.

  Lemma swap_disjoint: forall a b, SamplesDisjoint (flops a b).
  Proof. intros; cbn; repeat split; intros; intuition congruence. Qed.

  Example swap_flops_computed: forall a b, TrsF ds fs ms ps [] (flops a b) (flops b a).
  Proof.
    intros a b.
    apply (clock_samples_computed (rows:=rows a b) (s:=state a b)).
    - exists (state b a); apply source_swap.
    - apply swap_plan.
    - apply swap_disjoint.
  Qed.

  (** The executable evaluator samples both right-hand sides before either
      old register value changes. Its full IFF pair is fixed after two sweeps. *)
  Example executable_swap: forall a b,
    trsM_iff_rep ds fs HMapEmpty ms circuit (state a b,HMapEmpty) 2 =
      Sret (state a b,state b a).
  Proof. reflexivity. Qed.

  Example executable_swap_lfp: forall a b,
    LFP (state a b,HMapEmpty) (trsVModuleDecl_IFF ds fs HMapEmpty ms circuit)
      (state a b,state b a).
  Proof.
    intros; apply (proj1 (flat_module_lfp ds fs ms circuit circuit_flat _ _ _)).
    apply source_swap.
  Qed.

  (** This checks all active-region schedules. An NBA result cannot overwrite
      the other process's slot. *)
  Example clock_preserves_both_samples: forall a b t nba,
    ExecActiveRegion ds fs ms (procs ps) (state a b) (clkR (procs ps)) t nba ->
    t = state a b /\ nba = flopsR (flops b a).
  Proof.
    intros a b t nba Hrun.
    exact (clock_active_inv (swap_plan a b) Hrun).
  Qed.

  Example empty_nba_cannot_complete: forall a b t,
    ~ ExecActiveRegion ds fs ms (procs ps) (state a b) (clkR (procs ps)) t (nilR (procs ps)).
  Proof.
    intros a b t Hrun; destruct (clock_preserves_both_samples Hrun) as [_ Heq]; discriminate.
  Qed.

  Definition boundary (bindings: InitState): unode :=
    {| keys := map fst bindings; deps := []; updOnce := true; updDone := true;
       updf := fun _ => HMapStr bindings |}.
  Definition graph (_: InitState) (bindings: list InitState): ugraph := map boundary ([]::bindings).
  Definition VI (ins: InitState): Prop := ins = [].
  Definition VF (bindings: list InitState): Prop := exists a b, bindings = flops a b.
  Definition domain (s: State): Prop := exists a b, s = state a b.
  Definition flopMask (un: unode): bool := match keys un with [] => false | _ => true end.

  Lemma key_shape: forall a b, HMapStrKeysWf (state a b) [0%nat;1%nat].
  Proof.
    intros; split; [reflexivity|].
    intros [|[|i]] [|[|j]] Hneq k1 k2 Hn1 Hn2;
      try (destruct i; discriminate); try (destruct j; discriminate);
      try discriminate; inversion Hn1; inversion Hn2; subst; congruence.
  Qed.

  Lemma process_active_empty: forall proc, In proc (procs ps) -> forall s u,
    trsProc ds fs ms proc s = Sret u -> fst u = HMapEmpty.
  Proof.
    intros proc [Hp|[Hp|[Hp|[]]]] s u Hrun; subst proc.
    - inversion Hrun; reflexivity.
    - cbn in Hrun.
      match goal with Hrun: context [ctxEval ?d ?f ?ct ?cp ?st ?nw ?p ?e] |- _ =>
        destruct (ctxEval d f ct cp st nw p e)
      end; inversion Hrun; reflexivity.
    - cbn in Hrun.
      match goal with Hrun: context [ctxEval ?d ?f ?ct ?cp ?st ?nw ?p ?e] |- _ =>
        destruct (ctxEval d f ct cp st nw p e)
      end; inversion Hrun; reflexivity.
  Qed.

  Lemma graph_unique: forall a b, UGraphUnique (graph [] (flops a b)).
  Proof.
    intros a b [|[|[|i]]] [|[|[|j]]] Hneq un1 un2 Hn1 Hn2 key Hk1 Hk2;
      try (exfalso; apply Hneq; reflexivity);
      try (destruct i; discriminate); try (destruct j; discriminate); try discriminate;
      inversion Hn1; inversion Hn2; subst; simpl in *; intuition congruence.
  Qed.

  Lemma graph_domain: forall a b, GraphDomain (graph [] (flops a b)) domain.
  Proof.
    intros a b; split.
    - intros s [c [d ->]]. unfold UGraphUpdfAt; cbn [graph flops map].
      repeat constructor; unfold UNodeUpdfConst; simpl; intros; intuition subst; reflexivity.
    - intros current s next s' Hsame [c [d ->]] Hstep.
      inversion Hstep; subst.
      assert (Hin: In un (ug1 ++ un :: ug2)) by (apply in_or_app; right; left; reflexivity).
      destruct (Forall2_In_right Hsame un Hin) as [original [Ho [_ [_ Hfun]]]].
      destruct Ho as [<-|[<-|[<-|[]]]]; simpl in Hfun; rewrite <-Hfun;
        unfold domain; [exists c,d|exists a,d|exists c,b]; reflexivity.
  Qed.

  Lemma graph_source: forall a b,
    SourceGraph ds fs ms (procs ps) (fun _ => 0%nat) domain
      (graph [] (flops a b)) (state a b).
  Proof.
    intros a b; constructor.
    - apply graph_unique.
    - assert (Hkeys: forall bindings, UNodeKeysOk (boundary bindings)).
      { intros bindings st; right; exists bindings; split; reflexivity. }
      do 3 (constructor; [apply Hkeys|]); constructor.
    - intros un [<-|[<-|[<-|[]]]] dep Hdep; contradiction.
    - do 3 (constructor; [right; split; [reflexivity|]; split; [reflexivity|];
        intros st u Hrun; eapply process_active_empty; [|exact Hrun]; simpl; auto|]); constructor.
    - apply graph_domain.
    - exists a,b; reflexivity.
    - repeat constructor; simpl; intros; intuition subst; try discriminate.
    - repeat constructor; simpl; intros; intuition subst; reflexivity.
    - exact (proj2 (key_shape a b)).
  Qed.

  Lemma graph_standard: forall a b, UGraphStd ds fs ms (graph [] (flops a b)) (procs ps).
  Proof.
    intros a b.
    change (UGraphStd ds fs ms
      [getUNode ds fs ms (Hold []) getProcInputClk;
       getUNode ds fs ms (Hold [(0%nat,HMapBits a)]) (hd getProcInputClk ps);
       getUNode ds fs ms (Hold [(1%nat,HMapBits b)]) (hd getProcInputClk (tl ps))] (procs ps)).
    assert (Hb: forall bindings proc, trig_stv (proc_trig proc) = [] ->
      UNodeStd ds fs ms (getUNode ds fs ms (Hold bindings) proc) proc).
    { intros bindings proc Hnil; exact (proj2 (boundary_role_std ds fs ms bindings proc Hnil)). }
    do 3 (constructor; [apply Hb; reflexivity|]); constructor.
  Qed.

  Lemma module_wf: ModuleWf ds fs ms ps VI VF.
  Proof.
    refine {| module_rank := fun _ => 0%nat; module_domain := domain; module_graph := graph;
      module_input_mask := fun _ _ _ _ => false;
      module_flop_mask := fun _ _ _ => flopMask |}.
    - repeat constructor; left; reflexivity.
    - intros ins fl -> [a [b ->]]; apply graph_source.
    - intros ins fl -> [a [b ->]]; apply graph_standard.
    - intros ins fl -> [a [b ->]] s [c [d ->]].
      exists [0%nat;1%nat]; split; [apply key_shape|].
      intros key [<-|[<-|[]]]; eexists; split; [right; left; reflexivity|left; reflexivity
                                         |right; right; left; reflexivity|left; reflexivity].
    - intros ins0 fl0 ins1 fl1 -> [a [b ->]] -> [c [d ->]].
      do 2 eexists; repeat split; reflexivity.
    - intros ins0 ins1 fl -> -> [a [b ->]]; constructor;
        repeat constructor; simpl; intros; try contradiction; reflexivity.
    - intros ins fl0 fl1 -> [a [b ->]] [c [d ->]]; constructor;
        repeat constructor; simpl; intros; try discriminate; try contradiction; reflexivity.
  Qed.

  Lemma clock_wf: ClockWf ds fs ms ps VI VF.
  Proof.
    apply clock_wf_of_full_outputs.
    intros ins fl s -> [a [b ->]] Hs.
    assert (Hs0: StateOf ds fs ms ps [] (flops a b) (state a b))
      by (exists (state b a); apply source_swap).
    pose proof (StateOf_det Hs Hs0) as ->.
    exists (rows a b); split; [reflexivity|]; split.
    - apply clock_plan_outputs; apply swap_plan.
    - split; [reflexivity|exists b,a; reflexivity].
  Qed.

  Example swap_clock_result: forall a b final,
    TrsClock ds fs ms ps (state a b) final <-> final = state b a.
  Proof.
    intros a b final.
    assert (Hstart: StateOf ds fs ms ps [] (flops a b) (state a b))
      by (exists (state b a); apply source_swap).
    assert (Hfinish: StateOf ds fs ms ps [] (flops b a) (state b a))
      by (exists (state a b); apply source_swap).
    pose proof (@module_flops_ready _ _ _ _ ds fs ms ps VI VF module_wf
      [] (flops a b) (flops b a) eq_refl
      (ex_intro _ a (ex_intro _ b eq_refl))
      (ex_intro _ b (ex_intro _ a eq_refl)) (state a b) Hstart) as Hready.
    split.
    - intros Hclock.
      pose proof (proj1 (clock_slot_iff_injection (swap_plan a b) final) Hclock) as Hinject.
      pose proof (proj2 (injection_equiv Hready final) Hinject) as Hfinal.
      exact (StateOf_det Hfinal Hfinish).
    - intros ->. apply (proj2 (clock_slot_iff_injection (swap_plan a b) (state b a))).
      exact (proj1 (injection_equiv Hready (state b a)) Hfinish).
  Qed.

  Example clock_rejects_unsampled_flops: forall a b,
    a <> b -> ~ TrsClock ds fs ms ps (state a b) (state a b).
  Proof.
    intros a b Hneq Hclock. apply swap_clock_result in Hclock.
    inversion Hclock; contradiction.
  Qed.

  Example full_executable_clock_equivalence: forall a b,
    exists next, VF next /\ ExecutableTrsF ds fs ms circuit [] (flops a b) next /\
      forall final, ExecutableStateOf ds fs ms circuit [] next final <->
      exists mid, TrsI ds fs ms ps (state a b) mid [] /\ TrsClock ds fs ms ps mid final.
  Proof.
    intros a b.
    apply (@executable_clock_equiv _ _ _ _ ds fs ms circuit VI VF circuit_flat
      module_wf clock_wf [] [] (flops a b) eq_refl eq_refl).
    - exists a,b; reflexivity.
    - exists (state b a); apply executable_swap_lfp.
  Qed.
End SwapRegisters.
