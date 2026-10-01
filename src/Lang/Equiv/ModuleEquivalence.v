Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard TrsProc UpdGraph ProcUpdGraph StfUpdGraph
  StfStd RankedGraph SourceProgress SourceShape StdProgress ResetGraph WeightedRank
  GraphStructure ResetInjection GraphInjection.

Set Implicit Arguments.

Section ModuleEquivalence.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Record SourceGraph (ps: Processes) (rank: vid_t -> nat) (P: State -> Prop)
    (ug: ugraph) (seed: State): Prop := {
    source_unique: UGraphUnique ug;
    source_keys: UGraphKeysOk ug;
    source_ranked: RankedGraph rank ug;
    source_processes: UGraphSource decls funcs mtrss ug ps;
    source_domain: GraphDomain ug P;
    source_initial_domain: P seed;
    source_initial_nodes: UGraphSt seed ug;
    source_initial_equations: UpdfSub ug seed;
    source_initial_wf: HMapStrEmptyWf seed
  }.

  Lemma source_exists: forall ps rank P ug seed,
    SourceGraph ps rank P ug seed ->
    exists target flops, TrsProcsRep decls funcs mtrss ps seed target flops.
  Proof.
    intros ps rank P ug seed [Hu Hk Hr Hsource Hdomain HP Hst Hsub Hwf].
    eapply source_progress; try eassumption; eapply ranked_deps; eassumption.
  Qed.

  Lemma source_result: forall ps rank P ug seed,
    ProcsWfUpd decls funcs mtrss ps -> ProcsWfDet decls funcs mtrss ps ->
    SourceGraph ps rank P ug seed -> forall target flops,
    TrsProcsRep decls funcs mtrss ps seed target flops ->
    P target /\ GraphEquations ug target /\ UGraphStWf target ug.
  Proof.
    intros ps rank P ug seed Hpu Hpd [Hu Hk Hr Hsource Hdomain HP Hst Hsub Hwf] target flops Hrun.
    assert (Hd: UGraphDepsOk ug) by (eapply ranked_deps; eassumption).
    destruct (TrsProcsRep_graph_result ug seed Hpu Hpd (P := P) Hrun Hwf
      HP Hsub Hk Hdomain Hd Hu Hsource Hst) as [final [Htrace [Hfull [Hstf HwfF]]]].
    destruct (graph_domain_trace Hdomain Htrace (SameGraph_refl ug) Hu Hk HP Hsub) as [HPf Hsubf].
    pose proof (EvalUGraphTrs_same Htrace) as Hsame.
    assert (Hrf: RankedGraph rank final) by (eapply SameGraph_ranked; eassumption).
    assert (Huf: UGraphUnique final) by (eapply EvalUGraphTrs_UGraphUnique; eassumption).
    assert (Hcomplete: UGraphUpdCompl final).
    { eapply Forall_impl; [|exact Hfull]; intros un [Hcomp _]; exact Hcomp. }
    split; [exact HPf|]; split.
    - eapply SameGraph_equations; [exact Hsame|].
      eapply ranked_complete_equations; eassumption.
    - assert (Hdone: Forall (fun un => updDone un = true) final)
        by (eapply ranked_complete_done; eassumption).
      eapply wiring_present; [apply wiring_sym; apply same_wiring; exact Hsame|].
      apply Forall_forall; intros un Hin.
      pose proof (Forall_In Hstf un Hin) as [_ [Hpresent _]].
      exact (Hpresent (Forall_In Hdone un Hin)).
  Qed.

  Definition StateShape (ug: ugraph) (P: State -> Prop): Prop :=
    forall s, P s -> exists schema, HMapStrKeysWf s schema /\
      forall key, In key schema -> exists un, In un ug /\ In key (keys un).

  Lemma same_shape: forall s target schema,
    SameStrKeys s target -> HMapStrKeysWf s schema -> HMapStrKeysWf target schema.
  Proof.
    intros s target schema [xs [ys [Hs [Ht Hkeys]]]] Hshape; subst s target.
    destruct Hshape as [Hschema Huniq]; split; [rewrite <-Hkeys; exact Hschema|exact Huniq].
  Qed.

  (** Both source runs and the standard slot are constructed from graph and
      process contracts. The only relation between configurations replaces
      constant boundary functions; it does not assume an execution result. *)
  Theorem source_injection_ready: forall mprocs rank P old ug ins0 flops0 ins flops
    inits injected,
    ProcsWfUpd decls funcs mtrss (procs mprocs) ->
    ProcsWfDet decls funcs mtrss (procs mprocs) ->
    Forall (fun proc => trig_stv (proc_trig proc) = [] \/
      ProcSourceWf decls funcs mtrss proc) (procs mprocs) ->
    SourceGraph (procs mprocs) rank P old (initState (ipsAll mprocs ins0 flops0)) ->
    SourceGraph (procs mprocs) rank P ug (initState (ipsAll mprocs ins flops)) ->
    UGraphStd decls funcs mtrss ug (procs mprocs) ->
    StateShape ug P ->
    SameStrKeys (initState (ipsAll mprocs ins0 flops0)) (initState (ipsAll mprocs ins flops)) ->
    GraphChange old ug inits injected ->
    forall s, StateOf decls funcs mtrss mprocs ins0 flops0 s ->
    InjectionReady decls funcs mtrss mprocs s inits ins flops.
  Proof.
    intros mprocs rank P old ug ins0 flops0 ins flops inits injected Hpu Hpd Hlocal
      Hold Hnew Hstd Hshape Hseed Hchange s [f0 Hrun0].
    destruct (source_result Hpu Hpd Hold Hrun0) as [HP0 [Heq0 Hp0]].
    destruct (source_exists Hnew) as [target [ft Hrun]].
    destruct (source_result Hpu Hpd Hnew Hrun) as [HPt [Heqt Hpt]].
    destruct (Hshape s HP0) as [schema [Hschema Hcover]].
    assert (Htshape: HMapStrKeysWf target schema).
    { eapply same_shape; [|exact Hschema].
      eapply source_result_keys; [exact (source_processes Hold)|exact Hrun0|exact Hrun|exact Hseed]. }
    set (reset := resetGraph rank ug injected).
    pose proof (reset_same rank ug injected) as Hsame.
    pose proof (source_unique Hnew) as Hu; pose proof (source_keys Hnew) as Hk.
    pose proof (source_ranked Hnew) as Hr; pose proof (source_domain Hnew) as Hdomain.
    destruct (reset_initial (decls := decls) (funcs := funcs) (mtrss := mtrss)
      Hr Hu Hchange Hstd Heq0) as [Hinit Hsub].
    assert (Hkr: UGraphKeysOk reset) by (eapply same_keys_ok; eassumption).
    assert (Hrr: RankedGraph rank reset) by (eapply SameGraph_ranked; eassumption).
    assert (Hpr: UGraphStWf s reset).
    { eapply wiring_present; [apply same_wiring; exact Hsame|].
      eapply wiring_present; [exact (change_wiring Hchange)|exact Hp0]. }
    assert (Hdomainr: GraphDomain reset P) by (eapply SameGraph_domain; eassumption).
    assert (Hprogress: exists result, ExecTimeSlot decls funcs mtrss (procs mprocs)
      s (initsR inits) (nilR (procs mprocs)) result).
    { eapply standard_slot_progress with (cost := rankCost rank reset)
        (P := CompleteDomain reset P) (ug := reset).
      - apply ranked_schedule; [exact Hrr|exact (proj1 Hinit)].
      - eapply complete_process_progress; [exact Hrr| |exact Hlocal].
        eapply same_std; eassumption.
      - exact Hkr.
      - exact Hinit.
      - apply complete_domain; assumption.
      - split; [exact HP0|split; [exact Hpr|exists schema; exact Hschema]].
      - exact Hsub.
      - pose proof (Forall2_length (change_slots Hchange)) as Hlen.
        pose proof (Forall2_length Hstd) as Hps; congruence. }
    apply injection_graph_ready.
    refine {| injection_graph := reset; injection_domain := P;
      injection_rank := rank; injection_schema := schema; injection_target := target;
      injection_graph_ok := Hinit; injection_keys := Hkr; injection_acyclic := Hrr;
      injection_domain_ok := Hdomainr; injection_domain_initial := HP0;
      injection_sub := Hsub; injection_present := Hpr; injection_shape := Hschema;
      injection_target_shape := Htshape; injection_progress := Hprogress |}.
    - eapply domain_const; eassumption.
    - intros key Hin; eapply wiring_covered; [apply same_wiring; exact Hsame|apply Hcover; exact Hin].
    - exists ft; exact Hrun.
    - eapply SameGraph_equations; [apply SameGraph_sym; exact Hsame|exact Heqt].
  Qed.
  Record ModuleWf (mprocs: Processes) (ValidInputs: InitState -> Prop)
    (ValidFlops: list InitState -> Prop): Type := {
    module_rank: vid_t -> nat;
    module_domain: State -> Prop;
    module_graph: InitState -> list InitState -> ugraph;
    module_updates: ProcsWfUpd decls funcs mtrss (procs mprocs);
    module_deterministic: ProcsWfDet decls funcs mtrss (procs mprocs);
    module_processes: Forall (fun proc => trig_stv (proc_trig proc) = [] \/
      ProcSourceWf decls funcs mtrss proc) (procs mprocs);
    module_sources: forall ins flops, ValidInputs ins -> ValidFlops flops ->
      SourceGraph (procs mprocs) module_rank module_domain (module_graph ins flops)
        (initState (ipsAll mprocs ins flops));
    module_standard: forall ins flops, ValidInputs ins -> ValidFlops flops ->
      UGraphStd decls funcs mtrss (module_graph ins flops) (procs mprocs);
    module_shape: forall ins flops, ValidInputs ins -> ValidFlops flops ->
      StateShape (module_graph ins flops) module_domain;
    module_seed_keys: forall ins0 flops0 ins1 flops1,
      ValidInputs ins0 -> ValidFlops flops0 -> ValidInputs ins1 -> ValidFlops flops1 ->
      SameStrKeys (initState (ipsAll mprocs ins0 flops0))
        (initState (ipsAll mprocs ins1 flops1));
    module_input_mask: InitState -> InitState -> list InitState -> unode -> bool;
    module_input_change: forall ins0 ins1 flops,
      ValidInputs ins0 -> ValidInputs ins1 -> ValidFlops flops ->
      GraphChange (module_graph ins0 flops) (module_graph ins1 flops)
        (ins1 :: map (fun _ => []) mprocs) (module_input_mask ins0 ins1 flops);
    module_flop_mask: InitState -> list InitState -> list InitState -> unode -> bool;
    module_flop_change: forall ins flops0 flops1,
      ValidInputs ins -> ValidFlops flops0 -> ValidFlops flops1 ->
      GraphChange (module_graph ins flops0) (module_graph ins flops1)
        ([] :: flops1) (module_flop_mask ins flops0 flops1)
  }.

  Theorem module_state_exists: forall mprocs VI VF,
    ModuleWf mprocs VI VF -> forall ins flops, VI ins -> VF flops ->
    exists s, StateOf decls funcs mtrss mprocs ins flops s.
  Proof.
    intros mprocs VI VF M ins flops Hi Hf.
    destruct (source_exists (module_sources M ins flops Hi Hf)) as [s [f Hrun]].
    exists s,f; exact Hrun.
  Qed.

  (** At a source fixed point each process preserves the active state.
      This follows from its graph equations and unique output keys. *)
  Lemma module_process_settled: forall mprocs VI VF (M: ModuleWf mprocs VI VF)
    ins flops s, VI ins -> VF flops -> StateOf decls funcs mtrss mprocs ins flops s ->
    forall proc, In proc (procs mprocs) -> forall active nba,
      trsProc decls funcs mtrss proc s = Sret (active,nba) ->
      hmergeR s active = s.
  Proof.
    intros mprocs VI VF M ins flops s Hi Hf [computed Hrun] proc Hin active nba Heval.
    pose proof (module_sources M ins flops Hi Hf) as Hsource.
    destruct (source_result (module_updates M) (module_deterministic M) Hsource Hrun)
      as [HP [Heq Hpresent]].
    destruct (Forall2_In_right (source_processes Hsource) proc Hin)
      as [un [Hun Hlocal]].
    destruct Hlocal as [[[Hkeys [_ [_ Hfun]]] _]|[_ [_ Hempty]]].
    - specialize (Hfun s); rewrite Heval in Hfun; simpl in Hfun.
      destruct (Hkeys s) as [Hempty|[vs [Hvs Hks]]].
      + rewrite <-Hfun, Hempty; apply hmergeR_empty.
      + rewrite <-Hfun, Hvs.
        destruct (module_shape M ins flops Hi Hf s HP) as [schema [Hshape _]].
        destruct s; try contradiction.
        destruct Hshape as [<- Huniq]. apply hmergeR_absorbed; [exact Huniq|].
        intros key Hkey; rewrite <-Hvs; apply Heq; [exact Hun|rewrite Hks; exact Hkey].
    - specialize (Hempty s (active,nba) Heval); simpl in Hempty.
      subst active; apply hmergeR_empty.
  Qed.

  Lemma module_inputs_ready: forall mprocs VI VF (M: ModuleWf mprocs VI VF)
    ins0 ins1 flops,
    VI ins0 -> VI ins1 -> VF flops -> forall s,
    StateOf decls funcs mtrss mprocs ins0 flops s ->
    InjectionReady decls funcs mtrss mprocs s
      (ins1 :: map (fun _ => []) mprocs) ins1 flops.
  Proof.
    intros mprocs VI VF M ins0 ins1 flops Hi0 Hi1 Hf s Hs.
    eapply source_injection_ready with
      (old := module_graph M ins0 flops) (ug := module_graph M ins1 flops)
      (injected := module_input_mask M ins0 ins1 flops); [| | | | | | | | |exact Hs].
    - exact (module_updates M).
    - exact (module_deterministic M).
    - exact (module_processes M).
    - apply (module_sources M); assumption.
    - apply (module_sources M); assumption.
    - apply (module_standard M); assumption.
    - apply (module_shape M); assumption.
    - apply (module_seed_keys M); assumption.
    - apply (module_input_change M); assumption.
  Qed.

  Lemma module_flops_ready: forall mprocs VI VF (M: ModuleWf mprocs VI VF)
    ins flops0 flops1,
    VI ins -> VF flops0 -> VF flops1 -> forall s,
    StateOf decls funcs mtrss mprocs ins flops0 s ->
    InjectionReady decls funcs mtrss mprocs s ([] :: flops1) ins flops1.
  Proof.
    intros mprocs VI VF M ins flops0 flops1 Hi Hf0 Hf1 s Hs.
    eapply source_injection_ready with
      (old := module_graph M ins flops0) (ug := module_graph M ins flops1)
      (injected := module_flop_mask M ins flops0 flops1); [| | | | | | | | |exact Hs].
    - exact (module_updates M).
    - exact (module_deterministic M).
    - exact (module_processes M).
    - apply (module_sources M); assumption.
    - apply (module_sources M); assumption.
    - apply (module_standard M); assumption.
    - apply (module_shape M); assumption.
    - apply (module_seed_keys M); assumption.
    - apply (module_flop_change M); assumption.
  Qed.

  Theorem stf_std_equiv_module: forall mprocs VI VF,
    ModuleWf mprocs VI VF -> forall ins0 ins1 flops0 flops1,
    VI ins0 -> VI ins1 -> VF flops0 -> VF flops1 ->
    forall st0, StateOf decls funcs mtrss mprocs ins0 flops0 st0 -> forall stf,
    StateOf decls funcs mtrss mprocs ins1 flops1 stf <->
    exists mid, TrsI decls funcs mtrss mprocs st0 mid ins1 /\
      TrsC decls funcs mtrss mprocs mid stf flops1.
  Proof.
    intros mprocs VI VF M ins0 ins1 flops0 flops1 Hi0 Hi1 Hf0 Hf1 st0 Hstart stf.
    eapply stf_std_equiv; [| |exact Hstart].
    - intros s Hs; exact (@module_inputs_ready mprocs VI VF M ins0 ins1 flops0 Hi0 Hi1 Hf0 s Hs).
    - intros s Hs; exact (@module_flops_ready mprocs VI VF M ins1 flops0 flops1 Hi1 Hf0 Hf1 s Hs).
  Qed.
End ModuleEquivalence.
