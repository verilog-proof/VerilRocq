Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard UpdGraph ProcUpdGraph StdUpdGraph RankedGraph StfStd.

Set Implicit Arguments.

Section GraphInjection.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Lemma keys_wf_find_none: forall s schema,
    HMapStrKeysWf s schema -> forall key, ~ In key schema ->
    hfind [HEltVid key] s = None.
  Proof.
    intros s schema Hwf key Hout; destruct s; try contradiction.
    destruct Hwf as [Hkeys _]; subst schema; simpl.
    pose proof (haccessV_Some str key) as [Hin _].
    destruct (haccessV str key); [exfalso; apply Hout; apply Hin; discriminate|reflexivity].
  Qed.

  (** The domain specifies states on which process updates overwrite their
   * output bindings. A source execution supplies the target fixed point;
   * its graph equations determine the result of every terminating schedule. *)
  Record InjectionGraph (mprocs: Processes) (st0: State)
    (inits: list InitState) (ins: InitState) (flops: list InitState): Type := {
    injection_graph: ugraph;
    injection_domain: State -> Prop;
    injection_rank: vid_t -> nat;
    injection_schema: list vid_t;
    injection_target: State;
    injection_graph_ok: UGraphOk decls funcs mtrss injection_graph (procs mprocs)
      (initsR inits) st0;
    injection_keys: UGraphKeysOk injection_graph;
    injection_const: Forall UNodeUpdfConst injection_graph;
    injection_acyclic: RankedGraph injection_rank injection_graph;
    injection_covered: forall key, In key injection_schema ->
      exists un, In un injection_graph /\ In key (keys un);
    injection_domain_ok: GraphDomain injection_graph injection_domain;
    injection_domain_initial: injection_domain st0;
    injection_sub: UpdfSub injection_graph st0;
    injection_present: UGraphStWf st0 injection_graph;
    injection_shape: HMapStrKeysWf st0 injection_schema;
    injection_source: StateOf decls funcs mtrss mprocs ins flops injection_target;
    injection_target_shape: HMapStrKeysWf injection_target injection_schema;
    injection_equations: GraphEquations injection_graph injection_target;
    injection_progress: exists s, ExecTimeSlot decls funcs mtrss (procs mprocs)
      st0 (initsR inits) (nilR (procs mprocs)) s
  }.

  Theorem injection_graph_ready: forall mprocs st0 inits ins flops,
    InjectionGraph mprocs st0 inits ins flops ->
    InjectionReady decls funcs mtrss mprocs st0 inits ins flops.
  Proof.
    intros mprocs st0 inits ins flops
      [ug P rank schema target Hinit Hkeys Hconst Hrank Hcover Hdomain
        HP Hsub Hpresent Hshape Hsource Htarget Heq Hprogress].
    destruct Hinit as [Hu [Hupd [Hstd Hevents]]].
    split; [|exact Hprogress].
    exists (fun s act => exists current,
      EvalUGraphTrs ug st0 current s /\
      UGraphOk decls funcs mtrss current (procs mprocs) act s).
    split.
    - exists ug; split; [constructor|repeat split; assumption].
    - split.
      + intros s act s' act' [current [Hrun [Huc [Hupc [Hsc Hec]]]]] Hstep.
        assert (Hall: Forall (fun _: Process => True) (procs mprocs))
          by (apply Forall_forall; intros; exact I).
        destruct (ExecEvent_imp_EvalUGraphTrs Hall Hstep eq_refl eq_refl
          Huc Hupc Hsc Hec) as [next [Hnext [Hun [Hupn [Hsn Hen]]]]].
        exists next; split.
        * eapply EvalUGraphTrs_trs; eassumption.
        * repeat split; assumption.
      + intros s [current [Hrun [Huc [Hupc [Hsc Hec]]]]].
        pose proof (EvalUGraphTrs_same Hrun) as Hsame.
        destruct (graph_domain_trace Hdomain Hrun (SameGraph_refl ug)
          Hu Hkeys HP Hsub) as [_ Hsubf].
        assert (Heqf: GraphEquations ug s).
        { eapply SameGraph_equations; [exact Hsame|].
          eapply ranked_complete_equations; [|exact Huc| |exact Hsubf].
          - eapply SameGraph_ranked; eassumption.
          - eapply graph_empty_queue_complete; exact Hec. }
        destruct (EvalUGraphTrs_UGraphStWf_KeysWf Hkeys schema Hshape Hpresent Hrun)
          as [_ Hshapef].
        assert (Hs: s = target).
        { eapply HMapStrKeysWf_hfind_eq; [exact Hshapef|exact Htarget|].
          intros key; destruct (in_dec vid_eq_dec key schema) as [Hin|Hout].
          - destruct (Hcover key Hin) as [un [Hun Hkey]].
            eapply graph_equations_unique; eassumption.
          - rewrite (keys_wf_find_none s schema Hshapef key Hout),
              (keys_wf_find_none target schema Htarget key Hout); reflexivity. }
        subst s; exact Hsource.
  Qed.
  Theorem stf_std_equiv_graph: forall mprocs ins0 ins1 flops0 flops1,
    (forall s, StateOf decls funcs mtrss mprocs ins0 flops0 s ->
      InjectionGraph mprocs s (ins1 :: List.map (fun _ => nil) mprocs) ins1 flops0) ->
    (forall s, StateOf decls funcs mtrss mprocs ins1 flops0 s ->
      InjectionGraph mprocs s (nil :: flops1) ins1 flops1) ->
    forall st0, StateOf decls funcs mtrss mprocs ins0 flops0 st0 -> forall stf,
    StateOf decls funcs mtrss mprocs ins1 flops1 stf <->
    exists mid, TrsI decls funcs mtrss mprocs st0 mid ins1 /\
      TrsC decls funcs mtrss mprocs mid stf flops1.
  Proof.
    intros mprocs ins0 ins1 flops0 flops1 Hi Hc st0 Hstart stf.
    eapply stf_std_equiv; [| |exact Hstart].
    - intros s Hs; apply injection_graph_ready; apply Hi; exact Hs.
    - intros s Hs; apply injection_graph_ready; apply Hc; exact Hs.
  Qed.
End GraphInjection.
