Require Import Coq.Lists.List Coq.Arith.PeanoNat Coq.micromega.Lia.
Import ListNotations.
Require Import Lib.Lib Lang.Syntax Lang.Semantics Standard TrsProc ProcUpdGraph
  StfStd UpdGraph RankedGraph SourceShape ResetInjection GraphStructure
  ModuleEquivalence ModuleBridge ClockSampling UpdateCompletion ClockEquivalence.

Set Implicit Arguments.

Module RegisterWithComb.
  #[local] Instance ids: vid_t_c := {| vid_t := nat |}.
  #[local] Instance idops: vid_ops := {| vid_eq_dec := Nat.eq_dec |}.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  Definition port (dir: VPortDirection) (id: nat): VAnsiPortDecl :=
    VAnsiPortDeclVar (Some (VVarPortHeaderO (Some dir)
      (VDataTypeIntVec VLogic VPackedDimsNil))) id.
  Definition ports := VAnsiPortDeclsCons (port VPortDirectionInput 0%nat)
    (VAnsiPortDeclsCons (port VPortDirectionInput 1%nat)
      (VAnsiPortDeclsCons (port VPortDirectionOutput 2%nat)
        (VAnsiPortDeclsOne (port VPortDirectionOutput 3%nat)))).
  Definition item (c: @VModuleCommonItem nat): @VModuleItem nat :=
    VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemCommon c)).
  (** [always_comb y = q; always_ff @(posedge clk) q <= d;] *)
  Definition comb_body := VStatementItemBlockingAssignNormal (VExprId 3%nat) (VExprId 2%nat).
  Definition ff_body := VStatementProcTimingControl
    (VProcTimingControlEvent (VEventControlExpr
      (VEventExprExpr (Some VPosedge) (VExprId 1%nat))))
    (VStatementItemNonblockingAssign (VExprId 2%nat) (VExprId 0%nat)).
  Definition circuit := VModuleDeclAnsi 4%nat VParamPortsNil ports
    (VModuleItemsCons (item (VModuleCommonItemAlways VAlwaysComb (VStatementO comb_body)))
      (VModuleItemsOne (item (VModuleCommonItemAlways VAlwaysFF (VStatementO ff_body))))).
  Definition ds := declsVModuleDecl circuit.
  Definition fs: Funcs := fmapEmpty.
  Definition ms: MTrss := fmapEmpty.
  Definition ps := moduleProcs ds ms circuit.
  Definition comb := hd getProcInputClk ps.
  Definition ff := hd getProcInputClk (tl ps).
  Definition inputs (d: SZ): InitState := [(0%nat,HMapBits d);(1%nat,HMapBits szF0)].
  Definition flops (q: SZ): list InitState := [[];[(2%nat,HMapBits q)]].
  Definition state (d q: SZ) (y: option SZ): State :=
    HMapStr (inputs d ++ [(2%nat,HMapBits q)] ++
      match y with None => [] | Some v => [(3%nat,HMapBits v)] end).
  Definition settled (d q: SZ): State := state d q (Some q).
  Definition VI (ins: InitState): Prop := exists d, ins = inputs d.
  Definition VF (fl: list InitState): Prop := exists q, fl = flops q.
  Definition domain (s: State): Prop := exists d q y, s = state d q y.

  Lemma circuit_flat: FlatModule circuit.
  Proof. split; [reflexivity|repeat constructor]. Qed.

  Lemma ff_active_empty: forall s u, trsProc ds fs ms ff s = Sret u -> fst u = HMapEmpty.
  Proof. intros s u Hrun; cbn in Hrun; unfold ctxEval, ctxfind in Hrun;
    cbn in Hrun; destruct (haccessO s 0%nat); inversion Hrun; reflexivity. Qed.

  Definition copy_update (s: State): State :=
    match haccessO s 2%nat with
    | Some v => HMapStr [(3%nat,v)]
    | None => HMapEmpty
    end.
  Definition copy_node: unode :=
    {| keys := [3%nat]; deps := [2%nat]; updOnce := false; updDone := false;
       updf := copy_update |}.
  Definition boundary (bindings: InitState): unode :=
    {| keys := map fst bindings; deps := []; updOnce := true; updDone := true;
       updf := fun _ => HMapStr bindings |}.
  Definition graph (ins: InitState) (fl: list InitState): ugraph :=
    [boundary ins; copy_node; boundary (nth 1 fl [])].
  Definition rank (key: nat): nat := if Nat.eqb key 3 then 1 else 0.
  Definition inputMask (un: unode): bool := match keys un with 0%nat :: _ => true | _ => false end.
  Definition flopMask (un: unode): bool := match keys un with 2%nat :: _ => true | _ => false end.

  Lemma copy_actual: forall s,
    copy_update s = match trsProc ds fs ms comb s with Sret u => fst u | Fail _ => HMapEmpty end.
  Proof. intros s; unfold copy_update; cbn; unfold ctxEval, ctxfind; cbn;
    destruct (haccessO s 2%nat); reflexivity. Qed.

  Lemma copy_keys: UNodeKeysOk copy_node.
  Proof. intros s; unfold copy_node, copy_update; simpl; destruct (haccessO s 2%nat).
    - right; eexists; split; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma copy_const: UNodeUpdfConst copy_node.
  Proof.
    intros s t Heq; specialize (Heq 2%nat (or_introl eq_refl)).
    destruct s, t; simpl in Heq |- *; unfold copy_update; simpl;
      try reflexivity; try (rewrite Heq; reflexivity).
    all: repeat match type of Heq with context [haccessV ?xs 2%nat] =>
      destruct (haccessV xs 2%nat) end; simpl in *; congruence.
  Qed.

  Lemma copy_source: ProcSourceWf ds fs ms comb.
  Proof.
    split; intros s; cbn; unfold ctxEval, ctxfind; cbn;
      destruct (haccessO s 2%nat) eqn:Hread; simpl.
    - intros [|[|i]] [|[|j]] Hneq k l Hi Hj; try discriminate;
        try (destruct i; discriminate); try (destruct j; discriminate);
        inversion Hi; inversion Hj; subst; congruence.
    - exact I.
    - split; [discriminate|constructor; [cbn [hfind hmove]; rewrite Hread; discriminate|constructor]].
    - exists 2%nat; split; [left; reflexivity|cbn [hfind hmove]; rewrite Hread; reflexivity].
  Qed.

  Lemma source_state: forall d q,
    StateOf ds fs ms ps (inputs d) (flops q) (settled d q).
  Proof.
    intros; exists (HMapStr (nth 1 (flops d) [])).
    eapply TrsProcsNext; [apply TrsProcsFix; reflexivity|reflexivity].
  Qed.

  Lemma key_shape: forall d q y,
    HMapStrKeysWf (state d q y) ([0%nat;1%nat;2%nat] ++
      match y with None => [] | Some _ => [3%nat] end).
  Proof.
    intros; destruct y; split; [reflexivity| |reflexivity|];
      intros [|[|[|[|i]]]] [|[|[|[|j]]]] Hneq k l Hi Hj;
      try (destruct i; discriminate); try (destruct j; discriminate);
      try discriminate; inversion Hi; inversion Hj; subst; congruence.
  Qed.

  Lemma graph_unique: forall d q, UGraphUnique (graph (inputs d) (flops q)).
  Proof.
    intros d q [|[|[|i]]] [|[|[|j]]] Hneq un un' Hi Hj key Hk Hk';
      try (exfalso; apply Hneq; reflexivity);
      try (destruct i; discriminate); try (destruct j; discriminate); try discriminate;
      inversion Hi; inversion Hj; subst; simpl in *; intuition congruence.
  Qed.

  Lemma graph_domain: forall d q, GraphDomain (graph (inputs d) (flops q)) domain.
  Proof.
    intros d q; split.
    - intros s [d' [q' [y ->]]]. unfold UGraphUpdfAt; cbn [graph].
      constructor.
      + split; [intros v [<-|[<-|[]]]; destruct y; reflexivity|intros t u Heq; reflexivity].
      + constructor.
        * split; [intros v [<-|[]]; destruct y; reflexivity|exact copy_const].
        * constructor; [split; [intros v [<-|[]]; destruct y; reflexivity|intros t u Heq; reflexivity]|constructor].
    - intros current s next s' Hsame [d' [q' [y ->]]] Hstep.
      inversion Hstep; subst.
      assert (Hin: In un (ug1 ++ un :: ug2)) by (apply in_or_app; right; left; reflexivity).
      destruct (Forall2_In_right Hsame un Hin) as [original [Ho [_ [_ Hfun]]]].
      destruct Ho as [<-|[<-|[<-|[]]]]; simpl in Hfun; rewrite <-Hfun; unfold domain.
      + exists d,q',y; destruct y; reflexivity.
      + exists d',q',(Some q'); destruct y; reflexivity.
      + exists d',q,y; destruct y; reflexivity.
  Qed.

  Lemma graph_source: forall d q,
    SourceGraph ds fs ms (procs ps) rank domain
      (graph (inputs d) (flops q)) (state d q None).
  Proof.
    intros d q; constructor.
    - apply graph_unique.
    - constructor; [intros s; right; eexists; split; reflexivity|].
      constructor; [apply copy_keys|].
      constructor; [intros s; right; eexists; split; reflexivity|constructor].
    - intros un [<-|[<-|[<-|[]]]] dep Hdep; try contradiction.
      destruct Hdep as [<-|[]]; exists (boundary [(2%nat,HMapBits q)]).
      split; [right; right; left; reflexivity|]; split; [left; reflexivity|change (0 < 1); lia].
    - constructor; [right; repeat split; intros st u Heval; inversion Heval; reflexivity|].
      constructor; [left; split; [split; [apply copy_keys|]; split; [discriminate|];
        split; [reflexivity|apply copy_actual]|apply copy_source]|].
      constructor; [right; split; [reflexivity|]; split; [reflexivity|apply ff_active_empty]|constructor].
    - apply graph_domain.
    - exists d,q,None; reflexivity.
    - repeat constructor; simpl; intros; intuition subst; try discriminate; reflexivity.
    - apply Forall_forall; intros un [<-|[<-|[<-|[]]]] Hdone;
        simpl in Hdone; try discriminate; split; [reflexivity| |reflexivity|];
        intros v Hv; simpl in Hv; intuition subst; reflexivity.
    - exact (proj2 (key_shape d q None)).
  Qed.

  Lemma graph_standard: forall d q,
    UGraphStd ds fs ms (graph (inputs d) (flops q)) (procs ps).
  Proof.
    intros d q; constructor.
    - exact (proj2 (boundary_role_std ds fs ms (inputs d) getProcInputClk eq_refl)).
    - constructor.
      + split; [apply copy_keys|]; split.
        * intros upd Hmap Hnone s; apply copy_const; intros key [<-|[]].
          apply genEvalEvent_None in Hnone.
          pose proof (@Forall_In nat _ _ Hnone 2%nat (or_introl eq_refl)) as Habsent.
          cbn beta in Habsent.
          apply hfind_hupds_absent; [exact Hmap|].
          destruct (hfind [@HEltVid ids 2%nat] upd); [contradiction|reflexivity].
        * split; [reflexivity|intros; apply copy_actual].
      + constructor.
        * exact (proj2 (boundary_role_std ds fs ms [(2%nat,HMapBits q)] ff eq_refl)).
        * constructor.
  Qed.
  Lemma other_active_empty: forall i p, nth_error (procs ps) i = Some p ->
    i <> 1 -> forall s u, trsProc ds fs ms p s = Sret u -> fst u = HMapEmpty.
  Proof.
    intros [|[|[|i]]] p Hi Hneq s u Hrun; try (exfalso; apply Hneq; reflexivity);
      try (destruct i; discriminate); inversion Hi; subst.
    - inversion Hrun; reflexivity.
    - eapply ff_active_empty; exact Hrun.
  Qed.

  Lemma module_wf: ModuleWf ds fs ms ps VI VF.
  Proof.
    refine {| module_rank := rank; module_domain := domain; module_graph := graph;
      module_input_mask := fun _ _ _ => inputMask;
      module_flop_mask := fun _ _ _ => flopMask |}.
    - apply Forall_forall; intros p [<-|[<-|[<-|[]]]] s u Hrun.
      + inversion Hrun; exact I.
      + change (trsProc ds fs ms comb s = Sret u) in Hrun.
        pose proof (copy_actual s) as Heq; rewrite Hrun in Heq; simpl in Heq.
        rewrite <-Heq; unfold copy_update; destruct (haccessO s 2%nat); exact I.
      + rewrite (ff_active_empty s Hrun); exact I.
    - intros i j p p' Hneq Hi Hj s u Hu t v Hv.
      destruct (Nat.eq_dec i 1) as [->|Hother].
      + rewrite (other_active_empty Hj ltac:(congruence) t Hv).
        destruct (fst u); exact I.
      + rewrite (other_active_empty Hi Hother s Hu); exact I.
    - constructor; [left; reflexivity|].
      constructor; [right; apply copy_source|].
      constructor; [left; reflexivity|constructor].
    - intros ins fl [d ->] [q ->]; apply graph_source.
    - intros ins fl [d ->] [q ->]; apply graph_standard.
    - intros ins fl [d ->] [q ->] s [d' [q' [y ->]]].
      eexists; split; [apply key_shape|].
      intros key Hin; destruct y; simpl in Hin;
        repeat destruct Hin as [<-|Hin]; try contradiction;
        first [exists (boundary (inputs d)); split; [left; reflexivity|simpl; auto; fail]
              |exists copy_node; split; [right; left; reflexivity|left; reflexivity]
              |exists (boundary (nth 1 (flops q) [])); split;
                [right; right; left; reflexivity|left; reflexivity]].
    - intros ins0 fl0 ins1 fl1 [d0 ->] [q0 ->] [d1 ->] [q1 ->].
      do 2 eexists; repeat split; reflexivity.
    - intros ins0 ins1 fl [d0 ->] [d1 ->] [q ->]; constructor;
        repeat constructor; simpl; intros; try discriminate; try contradiction; reflexivity.
    - intros ins fl0 fl1 [d ->] [q0 ->] [q1 ->]; constructor;
        repeat constructor; simpl; intros; try discriminate; try contradiction; reflexivity.
  Qed.

  Definition rows (d: SZ): list (Process * InitState) :=
    [(comb,[]);(ff,[(2%nat,HMapBits d)])].

  Lemma clock_wf: ClockWf ds fs ms ps VI VF.
  Proof.
    apply clock_wf_of_outputs; [exact module_wf|].
    intros ins fl s [d ->] [q ->] Hs.
    pose proof (StateOf_det Hs (source_state d q)) as ->.
    exists (rows d),(flops d); split; [reflexivity|]; split.
    - constructor; [split; reflexivity|].
      constructor; [split; [discriminate|exists HMapEmpty; reflexivity]|constructor].
    - split; [cbn; repeat split; intros; contradiction|].
      split; [reflexivity|]; split; [exists d; reflexivity|].
      constructor; apply completion_refl.
  Qed.

  Example clock_result: forall d q final,
    TrsClock ds fs ms ps (settled d q) final <-> final = settled d d.
  Proof.
    intros d q final.
    pose proof (@module_flops_ready _ _ _ _ ds fs ms ps VI VF module_wf
      (inputs d) (flops q) (flops d) (ex_intro _ d eq_refl)
      (ex_intro _ q eq_refl) (ex_intro _ d eq_refl) (settled d q)
      (source_state d q)) as Hready.
    assert (Hp: ClockPlan ds fs ms (settled d q) (rows d)).
    { eapply module_clock_plan; [exact module_wf|exists d; reflexivity|exists q; reflexivity
        |apply source_state|reflexivity|].
      constructor; [split; reflexivity|].
      constructor; [split; [discriminate|exists HMapEmpty; reflexivity]|constructor]. }
    rewrite (clock_slot_iff_injection Hp final).
    change (ExecTimeSlot ds fs ms (procs ps) (settled d q)
      (initsR ([]::flops d)) (nilR (procs ps)) final <-> final = settled d d).
    split.
    - intros Hrun; apply (proj2 (injection_equiv Hready final)) in Hrun.
      exact (StateOf_det Hrun (source_state d d)).
    - intros ->; apply (proj1 (injection_equiv Hready _)); apply source_state.
  Qed.

  Example full_executable_clock_equivalence: forall d0 d1 q,
    exists next, VF next /\ ExecutableTrsF ds fs ms circuit (inputs d1) (flops q) next /\
      forall final, ExecutableStateOf ds fs ms circuit (inputs d1) next final <->
      exists mid, TrsI ds fs ms ps (settled d0 q) mid (inputs d1) /\
        TrsClock ds fs ms ps mid final.
  Proof.
    intros d0 d1 q.
    apply (@executable_clock_equiv _ _ _ _ ds fs ms circuit VI VF circuit_flat
      module_wf clock_wf (inputs d0) (inputs d1) (flops q)).
    - exists d0; reflexivity.
    - exists d1; reflexivity.
    - exists q; reflexivity.
    - apply (proj2 (executable_state_iff ds fs ms circuit circuit_flat _ _ _)); apply source_state.
  Qed.
End RegisterWithComb.
