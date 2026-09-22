Require Import Coq.Lists.List Coq.Arith.PeanoNat Coq.ZArith.BinInt Coq.micromega.Lia.
Import ListNotations.
Require Import Lib.Lib Lang.Syntax Lang.Semantics Standard TrsProc ProcUpdGraph
  StfStd UpdGraph RankedGraph SourceShape ResetInjection GraphStructure
  ModuleEquivalence ModuleBridge ClockSampling UpdateCompletion ClockEquivalence.

Set Implicit Arguments.

Module EnabledRegister.
  #[local] Instance ids: vid_t_c := {| vid_t := nat |}.
  #[local] Instance idops: vid_ops := {| vid_eq_dec := Nat.eq_dec |}.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  Definition port (dir: VPortDirection) (id: nat): VAnsiPortDecl :=
    VAnsiPortDeclVar (Some (VVarPortHeaderO (Some dir)
      (VDataTypeIntVec VLogic VPackedDimsNil))) id.
  Definition ports := VAnsiPortDeclsCons (port VPortDirectionInput 0%nat)
    (VAnsiPortDeclsCons (port VPortDirectionInput 1%nat)
      (VAnsiPortDeclsCons (port VPortDirectionInput 3%nat)
        (VAnsiPortDeclsOne (port VPortDirectionOutput 2%nat)))).

  (** [always_ff @(posedge clk) if (en) q <= d;] has one writer,
      one clock, and only nonblocking assignments. *)
  Definition body := VStatementCond (VExprId 0%nat)
    (Some (VStatementItemNonblockingAssign (VExprId 2%nat) (VExprId 1%nat))) None.
  Definition item := VModuleItemNonPort (VNonPortModuleOrGenerateItem
    (VModuleOrGenerateItemCommon (VModuleCommonItemAlways VAlwaysFF (VStatementO
      (VStatementProcTimingControl
        (VProcTimingControlEvent (VEventControlExpr
          (VEventExprExpr (Some VPosedge) (VExprId 3%nat)))) body))))).
  Definition circuit := VModuleDeclAnsi 4%nat VParamPortsNil ports (VModuleItemsOne item).
  Definition ds := declsVModuleDecl circuit.
  Definition fs: Funcs := fmapEmpty.
  Definition ms: MTrss := fmapEmpty.
  Definition ps := moduleProcs ds ms circuit.
  Definition proc := hd getProcInputClk ps.
  Definition inputs_enabled (en: bool) (d: SZ): InitState :=
    [(0%nat,HMapBits (if en then szF1 else szF0));(1%nat,HMapBits d);(3%nat,HMapBits szF0)].
  Definition inputs := inputs_enabled false.
  Definition flops (q: SZ): list InitState := [[(2%nat,HMapBits q)]].
  Definition state_enabled (en: bool) (q d: SZ): State :=
    HMapStr (inputs_enabled en d ++ concat (flops q)).
  Definition state := state_enabled false.
  Definition skipped: State := HMapStr [(2%nat,HMapEmpty)].
  Definition VI (ins: InitState): Prop := exists en d, ins = inputs_enabled en d.
  Definition VF (fl: list InitState): Prop := exists q, fl = flops q.

  Lemma circuit_flat: FlatModule circuit.
  Proof. split; [reflexivity|repeat constructor]. Qed.

  Example disabled_evaluation: forall q d,
    trsProc ds fs ms proc (state q d) = Sret (HMapEmpty,skipped).
  Proof. reflexivity. Qed.

  Example disabled_source: forall q d,
    StateOf ds fs ms ps (inputs d) (flops q) (state q d).
  Proof. intros; exists skipped; apply TrsProcsFix; reflexivity. Qed.

  Example disabled_executable: forall q d,
    trsM_iff_rep ds fs HMapEmpty ms circuit (state q d,HMapEmpty) 2 =
      Sret (state q d,skipped).
  Proof. reflexivity. Qed.

  (** The executable transition applies the update to the old register state. *)
  Example disabled_next_holds: forall q d,
    trsNext (HMapStr (concat (flops q)))
      (trsM_IFF circuit (trsM_iff_rep ds fs HMapEmpty ms circuit
        (state q d,HMapEmpty) 2)) =
      (HMapStr (concat (flops q)),HMapStr [(2%nat,HMapBits q)]).
  Proof. reflexivity. Qed.

  Lemma disabled_sample: forall q d bindings,
    ClockSample ds fs ms (state q d) (proc,bindings) ->
    bindings = [(2%nat,HMapEmpty)].
  Proof.
    intros q d bindings [_ [active [Heval _]]].
    rewrite disabled_evaluation in Heval; inversion Heval; reflexivity.
  Qed.

  Definition updates (en: bool) (d: SZ): InitState :=
    [(2%nat,if en then HMapBits d else HMapEmpty)].
  Definition rows (en: bool) (d: SZ): list (Process * InitState) := [(proc,updates en d)].
  Definition next_value (en: bool) (q d: SZ): SZ := if en then d else q.

  Lemma enabled_source: forall en q d,
    StateOf ds fs ms ps (inputs_enabled en d) (flops q) (state_enabled en q d).
  Proof. intros; exists (HMapStr (updates en d)); apply TrsProcsFix; destruct en; reflexivity. Qed.

  Lemma enabled_plan: forall en q d,
    ClockPlan ds fs ms (state_enabled en q d) (rows en d).
  Proof.
    intros; constructor; [|constructor].
    split; [discriminate|exists HMapEmpty; split; destruct en; reflexivity].
  Qed.

  Lemma process_active_empty: forall p, In p (procs ps) -> forall s u,
    trsProc ds fs ms p s = Sret u -> fst u = HMapEmpty.
  Proof.
    intros p [Hp|[Hp|[]]] s u Hrun; subst p.
    - inversion Hrun; reflexivity.
    - cbn in Hrun; destruct (haccessO s 0%nat); cbn in Hrun; try discriminate.
      match type of Hrun with
      | context [ctxEval ?ds ?fs ?ct ?cp ?st ?nw ?path ?expr] =>
          destruct (ctxEval ds fs ct cp st nw path expr); cbn in Hrun
      end; inversion Hrun; reflexivity.
  Qed.

  Lemma enabled_completion: forall en q d,
    UpdateCompletion ds fs ms (procs ps) (state_enabled en q d)
      [[];updates en d] ([]::flops (next_value en q d)).
  Proof.
    intros en q d.
    refine {| completion_domain := fun s =>
      s = state_enabled en q d \/ s = state_enabled en (next_value en q d) d |}.
    - left; reflexivity.
    - repeat constructor.
    - intros a b [Heq|[Heq|[]]] s [-> | ->]; inversion Heq; subst; destruct en; reflexivity.
    - intros a [<-|[<-|[<-|[<-|[]]]]] s [-> | ->]; destruct en;
        cbn [next_value updates]; first [left; reflexivity|right; reflexivity].
    - intros p Hin t s active nba Ht Hs Heval.
      pose proof (process_active_empty Hin t Heval) as Heq; simpl in Heq; subst active.
      rewrite hupds_empty; exact Hs.
  Qed.

  Lemma clock_wf: ClockWf ds fs ms ps VI VF.
  Proof.
    intros ins fl s [en [d ->]] [q ->] Hs.
    pose proof (StateOf_det Hs (enabled_source en q d)) as ->.
    exists (rows en d),(flops (next_value en q d)).
    split; [reflexivity|]; split; [apply clock_plan_outputs; apply enabled_plan|].
    split; [destruct en; reflexivity|]; split.
    - exists (next_value en q d); reflexivity.
    - constructor; apply enabled_completion.
  Qed.

  Definition boundary (bindings: InitState): unode :=
    {| keys := map fst bindings; deps := []; updOnce := true; updDone := true;
       updf := fun _ => HMapStr bindings |}.
  Definition graph (ins: InitState) (bindings: list InitState): ugraph := map boundary (ins::bindings).
  Definition domain (s: State): Prop := exists en q d, s = state_enabled en q d.
  Definition inputMask (un: unode): bool := match keys un with 0%nat :: _ => true | _ => false end.
  Definition flopMask (un: unode): bool := match keys un with 2%nat :: _ => true | _ => false end.

  Lemma key_shape: forall en q d, HMapStrKeysWf (state_enabled en q d) [0%nat;1%nat;3%nat;2%nat].
  Proof.
    intros; split; [reflexivity|].
    intros [|[|[|[|i]]]] [|[|[|[|j]]]] Hneq k1 k2 Hn1 Hn2;
      try (destruct i; discriminate); try (destruct j; discriminate);
      try discriminate; inversion Hn1; inversion Hn2; subst; congruence.
  Qed.

  Lemma graph_unique: forall en q d, UGraphUnique (graph (inputs_enabled en d) (flops q)).
  Proof.
    intros en q d [|[|i]] [|[|j]] Hneq un1 un2 Hn1 Hn2 key Hk1 Hk2;
      try (exfalso; apply Hneq; reflexivity);
      try (destruct i; discriminate); try (destruct j; discriminate); try discriminate;
      inversion Hn1; inversion Hn2; subst; simpl in *; intuition congruence.
  Qed.

  Lemma graph_domain: forall en q d, GraphDomain (graph (inputs_enabled en d) (flops q)) domain.
  Proof.
    intros en q d; split.
    - intros s [en' [q' [d' ->]]]. unfold UGraphUpdfAt; cbn [graph flops map].
      repeat constructor; unfold UNodeUpdfConst; simpl; intros; intuition subst; reflexivity.
    - intros current s next s' Hsame [en' [q' [d' ->]]] Hstep.
      inversion Hstep; subst.
      assert (Hin: In un (ug1 ++ un :: ug2)) by (apply in_or_app; right; left; reflexivity).
      destruct (Forall2_In_right Hsame un Hin) as [original [Ho [_ [_ Hfun]]]].
      destruct Ho as [<-|[<-|[]]]; simpl in Hfun; rewrite <-Hfun;
        unfold domain; [exists en,q',d|exists en',q,d']; reflexivity.
  Qed.

  Lemma graph_source: forall en q d,
    SourceGraph ds fs ms (procs ps) (fun _ => 0%nat) domain
      (graph (inputs_enabled en d) (flops q)) (state_enabled en q d).
  Proof.
    intros en q d; constructor.
    - apply graph_unique.
    - assert (Hkeys: forall bindings, UNodeKeysOk (boundary bindings)).
      { intros bindings st; right; exists bindings; split; reflexivity. }
      do 2 (constructor; [apply Hkeys|]); constructor.
    - intros un [<-|[<-|[]]] dep Hdep; contradiction.
    - do 2 (constructor; [right; split; [reflexivity|]; split; [reflexivity|];
        intros st u Hrun; eapply process_active_empty; [|exact Hrun]; simpl; auto|]); constructor.
    - apply graph_domain.
    - exists en,q,d; reflexivity.
    - repeat constructor; simpl; intros; intuition subst; try discriminate.
    - repeat constructor; simpl; intros; intuition subst; reflexivity.
    - exact (proj2 (key_shape en q d)).
  Qed.

  Lemma graph_standard: forall en q d,
    UGraphStd ds fs ms (graph (inputs_enabled en d) (flops q)) (procs ps).
  Proof.
    intros en q d.
    change (UGraphStd ds fs ms
      [getUNode ds fs ms (Hold (inputs_enabled en d)) getProcInputClk;
       getUNode ds fs ms (Hold [(2%nat,HMapBits q)]) proc] (procs ps)).
    assert (Hb: forall bindings p, trig_stv (proc_trig p) = [] ->
      UNodeStd ds fs ms (getUNode ds fs ms (Hold bindings) p) p).
    { intros bindings p Hnil; exact (proj2 (boundary_role_std ds fs ms bindings p Hnil)). }
    do 2 (constructor; [apply Hb; reflexivity|]); constructor.
  Qed.

  Lemma module_wf: ModuleWf ds fs ms ps VI VF.
  Proof.
    refine {| module_rank := fun _ => 0%nat; module_domain := domain; module_graph := graph;
      module_input_mask := fun _ _ _ => inputMask;
      module_flop_mask := fun _ _ _ => flopMask |}.
    - repeat constructor; left; reflexivity.
    - intros ins fl [en [d ->]] [q ->]; apply graph_source.
    - intros ins fl [en [d ->]] [q ->]; apply graph_standard.
    - intros ins fl [en [d ->]] [q ->] s [en' [q' [d' ->]]].
      exists [0%nat;1%nat;3%nat;2%nat]; split; [apply key_shape|].
      intros key [<-|[<-|[<-|[<-|[]]]]];
        eexists; split; [left; reflexivity|left; reflexivity
                       |left; reflexivity|right; left; reflexivity
                       |left; reflexivity|right; right; left; reflexivity
                       |right; left; reflexivity|left; reflexivity].
    - intros ins0 fl0 ins1 fl1 [en0 [d0 ->]] [q0 ->] [en1 [d1 ->]] [q1 ->].
      do 2 eexists; repeat split; reflexivity.
    - intros ins0 ins1 fl [en0 [d0 ->]] [en1 [d1 ->]] [q ->]; constructor;
        repeat constructor; simpl; intros; try discriminate; try contradiction; reflexivity.
    - intros ins fl0 fl1 [en [d ->]] [q0 ->] [q1 ->]; constructor;
        repeat constructor; simpl; intros; try discriminate; try contradiction; reflexivity.
  Qed.

  Example executable_next: forall en q d,
    ExecutableTrsF ds fs ms circuit (inputs_enabled en d) (flops q) (flops (next_value en q d)).
  Proof.
    intros en q d; apply (proj2 (executable_flops_iff ds fs ms circuit circuit_flat _ _ _)).
    exists (state_enabled en q d),(HMapStr (updates en d)); split.
    - apply TrsProcsFix; destruct en; reflexivity.
    - destruct en; reflexivity.
  Qed.

  Example clock_result: forall en q d final,
    TrsClock ds fs ms ps (state_enabled en q d) final <->
      final = state_enabled en (next_value en q d) d.
  Proof.
    intros en q d final.
    pose proof (@module_flops_ready _ _ _ _ ds fs ms ps VI VF module_wf
      (inputs_enabled en d) (flops q) (flops (next_value en q d))
      (ex_intro _ en (ex_intro _ d eq_refl)) (ex_intro _ q eq_refl)
      (ex_intro _ (next_value en q d) eq_refl) (state_enabled en q d)
      (enabled_source en q d)) as Hready.
    split.
    - intros Hclock.
      pose proof (proj1 (clock_slot_iff_injection (enabled_plan en q d) final) Hclock) as Hraw.
      pose proof (proj1 (completion_slot_iff (enabled_completion en q d) final) Hraw) as Hfull.
      pose proof (proj2 (injection_equiv Hready final) Hfull) as Hfinal.
      exact (StateOf_det Hfinal (enabled_source en (next_value en q d) d)).
    - intros ->. apply (proj2 (clock_slot_iff_injection (enabled_plan en q d) _)).
      apply (proj2 (completion_slot_iff (enabled_completion en q d) _)).
      apply (proj1 (injection_equiv Hready _)); apply enabled_source.
  Qed.

  Example disabled_clock_holds: forall q d final,
    TrsClock ds fs ms ps (state_enabled false q d) final <->
      final = state_enabled false q d.
  Proof. intros; apply clock_result. Qed.

  Example enabled_clock_loads: forall q d final,
    TrsClock ds fs ms ps (state_enabled true q d) final <->
      final = state_enabled true d d.
  Proof. intros; apply clock_result. Qed.

  Example full_executable_clock_equivalence: forall en0 en1 q d0 d1,
    exists next, VF next /\ ExecutableTrsF ds fs ms circuit (inputs_enabled en1 d1) (flops q) next /\
      forall final, ExecutableStateOf ds fs ms circuit (inputs_enabled en1 d1) next final <->
      exists mid, TrsI ds fs ms ps (state_enabled en0 q d0) mid (inputs_enabled en1 d1) /\
        TrsClock ds fs ms ps mid final.
  Proof.
    intros en0 en1 q d0 d1.
    apply (@executable_clock_equiv _ _ _ _ ds fs ms circuit VI VF circuit_flat
      module_wf clock_wf (inputs_enabled en0 d0) (inputs_enabled en1 d1) (flops q)).
    - exists en0,d0; reflexivity.
    - exists en1,d1; reflexivity.
    - exists q; reflexivity.
    - apply (proj2 (executable_state_iff ds fs ms circuit circuit_flat _ _ _)); apply enabled_source.
  Qed.

  (** Reads exclude the variables written within an always_comb block. *)
  Definition copy := VStatementItemBlockingAssignNormal (VExprId 2%nat) (VExprId 1%nat).
  Example copy_sensitivity: getSLStatement ds [] copy = [1%nat].
  Proof. reflexivity. Qed.
  Example copy_input_triggers:
    genEvalEvent (EventUpd (HMapStr [(1%nat,HMapBits szF1)]))
      {| proc_trig := TrigStv (getSLStatement ds [] copy);
         proc_pos := []; proc_evu := EvalUnitAlways true copy |} =
      Some (EventEval true [] (EvalUnitAlways true copy)).
  Proof. reflexivity. Qed.
End EnabledRegister.

Module IndexedRead.
  Import EnabledRegister.
  #[local] Existing Instance ids.
  #[local] Existing Instance idops.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  Definition expr := VExprPriSelect (VExprId 1%nat) (VExprId 0%nat).
  Definition body := VStatementItemBlockingAssignNormal (VExprId 2%nat) expr.
  Definition proc: Process :=
    {| proc_trig := TrigStv (getSLStatement ds [] body);
       proc_pos := []; proc_evu := EvalUnitAlways true body |}.

  Example sensitivity: getSLStatement ds [] body = [1%nat;0%nat].
  Proof. reflexivity. Qed.

  Example index_update_triggers:
    genEvalEvent (EventUpd (HMapStr [(0%nat,HMapBits szF1)])) proc =
      Some (EventEval true [] (EvalUnitAlways true body)).
  Proof. reflexivity. Qed.

  (** Both operands are required by the executable expression evaluator. *)
  Lemma process_source: ProcSourceWf ds fs ms proc.
  Proof.
    split; intros s; cbn; unfold ctxEval, ctxfind; cbn;
      destruct (haccessO s 1%nat) eqn:Ha; cbn.
    - destruct (haccessO s 0%nat) eqn:Hi; cbn; [|exact I].
      intros [|[|i]] [|[|j]] Hneq k l Hk Hl; try discriminate;
        try (destruct i; discriminate); try (destruct j; discriminate); congruence.
    - exact I.
    - destruct (haccessO s 0%nat) eqn:Hi; cbn.
      + split; [discriminate|]. constructor; [cbn [hfind hmove]; rewrite Ha; discriminate|].
        constructor; [cbn [hfind hmove]; rewrite Hi; discriminate|constructor].
      + exists 0%nat; split; [right; left; reflexivity|cbn [hfind hmove]; rewrite Hi; reflexivity].
    - exists 1%nat; split; [left; reflexivity|cbn [hfind hmove]; rewrite Ha; reflexivity].
  Qed.

  Definition selected_lvalue := VExprPriSelect (VExprId 2%nat) (VExprId 0%nat).
  Definition selected_write := VStatementItemBlockingAssignNormal selected_lvalue (VExprId 1%nat).

  Example lvalue_reads_index: getSLStatement ds [] selected_write = [0%nat;1%nat].
  Proof. reflexivity. Qed.
  Example lvalue_writes_base: getSLStatementWrites ds [] selected_write = [2%nat].
  Proof. reflexivity. Qed.
  Example continuous_lvalue_reads_index:
    map (fun p => trig_stv (proc_trig p))
      (getProcsAssign ds [] (VAssignO selected_lvalue (VExprId 1%nat))) = [[0%nat;1%nat]].
  Proof. reflexivity. Qed.

  Definition child: MTrs :=
    {| mtrs_input_vids := [10%nat]; mtrs_output_vids := [11%nat];
       mtrs_func := fun _ _ => (HMapEmpty,HMapEmpty) |}.
  Definition child_instance := VModuleInsOne 12%nat VParamValueAssignsNil
    (VHierInsOne 13%nat (VPortConnsNamed
      (VNamedPortConnsCons (VNamedPortConnE 10%nat (VExprId 1%nat))
        (VNamedPortConnsOne (VNamedPortConnE 11%nat selected_lvalue))))).
  Example instance_writes_output_base:
    getWritesModuleIns ds (fun _ => Sret child) [] child_instance = [2%nat].
  Proof. reflexivity. Qed.

  Definition selected_ff: Process :=
    {| proc_trig := TrigClk; proc_pos := [];
       proc_evu := EvalUnitAlways false
         (VStatementItemNonblockingAssign selected_lvalue (VExprId 1%nat)) |}.

  Example selected_ff_update: forall q d,
    trsProc ds fs ms selected_ff (state q d) =
      Sret (HMapEmpty,HMapStr [(2%nat,HMapArr [(0%Z,HMapBits d)])]).
  Proof. reflexivity. Qed.

  Definition zero: @VExpr nat := VExprPriLiteral (VPriLiteralUU VZeros).
  Definition packed_ports := VAnsiPortDeclsCons (port VPortDirectionInput 0%nat)
    (VAnsiPortDeclsCons (port VPortDirectionInput 1%nat)
      (VAnsiPortDeclsCons (port VPortDirectionInput 3%nat)
        (VAnsiPortDeclsOne (VAnsiPortDeclVar (Some (VVarPortHeaderO
          (Some VPortDirectionOutput)
          (VDataTypeIntVec VLogic (VPackedDimsOne (VDimRange zero zero))))) 2%nat)))).
  Definition packed_circuit := VModuleDeclAnsi 4%nat VParamPortsNil packed_ports
    (VModuleItemsOne (VModuleItemNonPort (VNonPortModuleOrGenerateItem
      (VModuleOrGenerateItemCommon (VModuleCommonItemAlways VAlwaysFF (VStatementO
        (VStatementProcTimingControl
          (VProcTimingControlEvent (VEventControlExpr
            (VEventExprExpr (Some VPosedge) (VExprId 3%nat))))
          (VStatementItemNonblockingAssign selected_lvalue (VExprId 1%nat))))))))).

  (** The current merge leaves a packed bit value unchanged on an array
      update. Thus this selection needs an evaluator repair for packed bits. *)
  Example packed_bit_update_ignored:
    fst (trsNext (HMapStr [(2%nat,HMapBits szF0)])
      (trsM_IFF packed_circuit (trsM_iff_rep (declsVModuleDecl packed_circuit) fs HMapEmpty ms
        packed_circuit (state szF0 szF1,HMapEmpty) 2))) = HMapStr [(2%nat,HMapBits szF0)].
  Proof. reflexivity. Qed.
End IndexedRead.

Module GroupedCombinationalChain.
  Import EnabledRegister.
  #[local] Existing Instance ids.
  #[local] Existing Instance idops.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  (** The signal dependencies are [a -> x -> y -> z]. The first block
      groups [x = a] and [z = y]; the second block assigns [y = x]. *)
  Definition first_body := VStatementSeqBlock
    [VStatementItemBlockingAssignNormal (VExprId 1%nat) (VExprId 0%nat);
     VStatementItemBlockingAssignNormal (VExprId 3%nat) (VExprId 2%nat)].
  Definition second_body := VStatementItemBlockingAssignNormal (VExprId 2%nat) (VExprId 1%nat).
  Definition ports := VAnsiPortDeclsCons (port VPortDirectionInput 0%nat)
    (VAnsiPortDeclsCons (port VPortDirectionOutput 1%nat)
      (VAnsiPortDeclsCons (port VPortDirectionOutput 2%nat)
        (VAnsiPortDeclsOne (port VPortDirectionOutput 3%nat)))).
  Definition item (body: @VStatementItem nat): @VModuleItem nat :=
    VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemCommon
      (VModuleCommonItemAlways VAlwaysComb (VStatementO body)))).
  Definition circuit := VModuleDeclAnsi 4%nat VParamPortsNil ports
    (VModuleItemsCons (item first_body) (VModuleItemsOne (item second_body))).
  Definition ds := declsVModuleDecl circuit.
  Definition first: Process :=
    {| proc_trig := TrigStv (getSLStatement ds [] first_body);
       proc_pos := []; proc_evu := EvalUnitAlways true first_body |}.
  Definition second: Process :=
    {| proc_trig := TrigStv (getSLStatement ds [] second_body);
       proc_pos := []; proc_evu := EvalUnitAlways true second_body |}.
  Definition graph: ugraph :=
    [getUNode ds fs ms (Hold [(0%nat,HMapBits szF0)]) getProcInputClk;
     getUNode ds fs ms (Compute [1%nat;3%nat] false) first;
     getUNode ds fs ms (Compute [2%nat] false) second].

  Lemma no_process_ranking: forall rank, ~ RankedGraph rank graph.
  Proof.
    intros rank Hr.
    destruct (Hr _ (or_intror (or_introl eq_refl)) 2%nat
      (or_intror (or_introl eq_refl))) as [p [Hp [Hkey Hlt]]].
    destruct Hp as [<-|[<-|[<-|[]]]]; cbn in Hkey;
      try (exfalso; intuition congruence).
    destruct (Hr _ (or_intror (or_intror (or_introl eq_refl))) 1%nat
      (or_introl eq_refl)) as [p [Hp [Hkey' Hlt']]].
    destruct Hp as [<-|[<-|[<-|[]]]]; cbn in Hkey';
      try (exfalso; intuition congruence).
    change (rank 2%nat < rank 1%nat) in Hlt.
    change (rank 1%nat < rank 2%nat) in Hlt'; lia.
  Qed.

  Definition seed: State := HMapStr [(0%nat,HMapBits szF0)].

  (** A whole-block failure discards [x = a] when [y] is still absent. *)
  Example first_block_undriven: trsProc ds fs ms first seed = Fail TrsUndriven.
  Proof. reflexivity. Qed.
  Example second_block_undriven: trsProc ds fs ms second seed = Fail TrsUndriven.
  Proof. reflexivity. Qed.
  Example source_stuck_at_seed:
    trsProcs ds fs ms [first;second] (seed,HMapEmpty) = Sret (seed,HMapEmpty).
  Proof. reflexivity. Qed.

  Example executable_stuck_at_seed: forall n,
    trsM_iff_rep ds fs HMapEmpty ms circuit (seed,HMapEmpty) n = Sret (seed,HMapEmpty).
  Proof. induction n; [reflexivity|cbn [trsM_iff_rep]; rewrite IHn; reflexivity]. Qed.
End GroupedCombinationalChain.
