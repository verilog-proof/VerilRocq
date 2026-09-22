Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Syntax Lang.Analysis Lang.Semantics Standard TrsProc ProcUpdGraph StfStd
  ModuleEquivalence ModuleBridge ClockSampling UpdateCompletion.

Set Implicit Arguments.

Section ClockEquivalence.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition sampleUpdate (bindings: InitState): State :=
    match bindings with [] => HMapEmpty | _ => HMapStr bindings end.

  Fixpoint sampleFold (inits: list InitState): State :=
    match inits with [] => HMapEmpty | bindings :: rest =>
      hmergeR (sampleUpdate bindings) (sampleFold rest) end.

  Fixpoint SamplesDisjoint (inits: list InitState): Prop :=
    match inits with [] => True | bindings :: rest =>
      HDisj (HMapStr bindings) (HMapStr (concat rest)) /\ SamplesDisjoint rest end.

  Lemma keys_unique_app_right: forall xs ys,
    KeysUnique (xs ++ ys) -> KeysUnique ys.
  Proof.
    induction xs; intros ys Hu; [exact Hu|].
    apply IHxs; eapply KeysUnique_cons; exact Hu.
  Qed.

  Lemma keys_unique_app_disjoint: forall xs ys,
    KeysUnique (xs ++ ys) -> forall key, In key xs -> In key ys -> False.
  Proof.
    induction xs as [|x xs IH]; intros ys Hu key Hin Hrest; [contradiction|].
    destruct Hin as [<-|Hin].
    - apply (KeysUnique_cons_not_In Hu); apply in_or_app; right; exact Hrest.
    - eapply IH; [eapply KeysUnique_cons; exact Hu|exact Hin|exact Hrest].
  Qed.

  Lemma samples_disjoint_of_unique: forall inits,
    KeysUnique (map fst (concat inits)) -> SamplesDisjoint inits.
  Proof.
    induction inits as [|bindings rest IH]; intros Hu; [exact I|].
    cbn [concat] in Hu; rewrite map_app in Hu; split.
    - exact (keys_unique_app_disjoint (map fst bindings) (map fst (concat rest)) Hu).
    - apply IH; eapply keys_unique_app_right; exact Hu.
  Qed.

  Lemma concat_binding_keys: forall raw full: list InitState,
    Forall2 (fun a b => map fst a = map fst b) raw full ->
    map fst (concat raw) = map fst (concat full).
  Proof.
    intros raw full Hkeys; induction Hkeys as [|a b raw full Hab Hkeys IH]; [reflexivity|].
    cbn [concat]; rewrite !map_app, Hab, IH; reflexivity.
  Qed.

  Lemma hmergeR_empty_left: forall s, hmergeR HMapEmpty s = s.
  Proof. destruct s; reflexivity. Qed.

  Lemma sample_fold_repr: forall inits,
    SamplesDisjoint inits ->
    (sampleFold inits = HMapEmpty /\ concat inits = []) \/
    sampleFold inits = HMapStr (concat inits).
  Proof.
    induction inits as [|bindings rest IH]; intros Hsep; [left; auto|].
    destruct Hsep as [Hd Hrest]. destruct bindings as [|binding bindings].
    - cbn [sampleFold sampleUpdate concat app]; rewrite hmergeR_empty_left; apply IH; exact Hrest.
    - cbn [sampleFold sampleUpdate concat app]; destruct (IH Hrest) as [[Heq Hnil]|Heq]; rewrite Heq.
      + rewrite hmergeR_empty, Hnil, app_nil_r; right; reflexivity.
      + rewrite hmergeR_str_disj by exact Hd; right; reflexivity.
  Qed.

  Lemma samples_fold_disjoint: forall bindings rest,
    SamplesDisjoint (bindings::rest) ->
    HDisj (sampleUpdate bindings) (sampleFold rest).
  Proof.
    intros bindings rest [Hd Hr]. destruct bindings; [exact I|].
    destruct (sample_fold_repr rest Hr) as [[Heq _]|Heq]; rewrite Heq; [exact I|exact Hd].
  Qed.

  Lemma clock_sample_sweep: forall s rows,
    ClockPlan decls funcs mtrss s rows -> SamplesDisjoint (map snd rows) -> forall base,
    trsProcs decls funcs mtrss (map fst rows) (s,base) =
      Sret (s,hmergeR base (sampleFold (map snd rows))).
  Proof.
    intros s rows Hp; induction Hp as [|[proc bindings] rows Hsample Hp IH]; intros Hsep base.
    - simpl; rewrite hmergeR_empty; reflexivity.
    - pose proof (samples_fold_disjoint Hsep) as Hdisj.
      destruct Hsep as [Hd Hsep]. unfold ClockSample in Hsample; simpl in *.
      destruct (trig_clk (proc_trig proc)) eqn:Hclk.
      + destruct Hsample as [Hnonempty [active [Hex Hsteady]]].
        cbn [map fst snd trsProcs]; rewrite Hex.
        unfold iffupds; simpl; rewrite Hsteady, IH by exact Hsep.
        destruct bindings; [contradiction|]. simpl in *.
        rewrite hmergeR_assoc; [reflexivity|exact I|exact Hdisj].
      + destruct Hsample as [-> Hsteady].
        cbn [map fst snd trsProcs].
        destruct (trsProc decls funcs mtrss proc s) as [[a n]|err];
          unfold iffupds; simpl in *.
        * destruct Hsteady as [Hsteady ->]. rewrite Hsteady, hmergeR_empty, IH by exact Hsep.
          destruct (sampleFold (map snd rows)); reflexivity.
        * rewrite !hmergeR_empty, IH by exact Hsep.
          destruct (sampleFold (map snd rows)); reflexivity.
  Qed.

  Lemma sample_fold_observed: forall inits,
    SamplesDisjoint inits -> HSEquiv (sampleFold inits) (HMapStr (concat inits)).
  Proof.
    intros inits Hsep; destruct (sample_fold_repr inits Hsep) as [[Heq Hnil]|Heq]; rewrite Heq.
    - rewrite Hnil. split; intros p Hnonempty v Hfind; destruct p as [|he rest]; [contradiction| |contradiction|];
        destruct he; discriminate.
    - split; apply HSub_refl.
  Qed.

  Lemma combineIps_bindings: forall inits ps,
    length inits = length ps -> map fst (combineIps inits ps) = inits.
  Proof.
    induction inits as [|bindings rest IH]; intros [|proc ps] Hlen; try discriminate;
      simpl; [reflexivity|f_equal; apply IH; simpl in Hlen; congruence].
  Qed.

  Lemma sampled_flop_state: forall rows,
    initState (ipsFlops (map fst rows) (map snd rows)) = HMapStr (concat (map snd rows)).
  Proof.
    intros rows; unfold initState, ipsFlops; simpl.
    rewrite combineIps_bindings by (rewrite !map_length; reflexivity); reflexivity.
  Qed.

  Lemma source_terminal: forall ps seed final flops,
    TrsProcsRep decls funcs mtrss ps seed final flops ->
    trsProcs decls funcs mtrss ps (final,HMapEmpty) = Sret (final,flops).
  Proof. induction 1; assumption. Qed.

  Lemma sampled_source_result: forall ins flops s rows,
    StateOf decls funcs mtrss (map fst rows) ins flops s ->
    ClockPlan decls funcs mtrss s rows -> SamplesDisjoint (map snd rows) ->
    TrsProcsRep decls funcs mtrss (procs (map fst rows))
      (initState (ipsAll (map fst rows) ins flops)) s (sampleFold (map snd rows)).
  Proof.
    intros ins flops s rows [computed Hrun] Hp Hsep.
    pose proof (source_terminal Hrun) as Hterminal.
    assert (Hsweep: trsProcs decls funcs mtrss (procs (map fst rows)) (s,HMapEmpty) =
      Sret (s,sampleFold (map snd rows))).
    { unfold procs; cbn [trsProcs trsProc execEvalEvent getProcInputClk proc_pos proc_evu fst snd].
      unfold iffupds; simpl; rewrite hmergeR_empty.
      rewrite clock_sample_sweep by assumption. rewrite hmergeR_empty_left; reflexivity. }
    assert (Heq: @Sret (State * State) TrsFail (s,computed) = Sret (s,sampleFold (map snd rows))).
    { etransitivity; [symmetry; exact Hterminal|exact Hsweep]. }
    injection Heq as Heq; subst computed; exact Hrun.
  Qed.

  Theorem clock_samples_computed: forall ins flops s rows,
    StateOf decls funcs mtrss (map fst rows) ins flops s ->
    ClockPlan decls funcs mtrss s rows -> SamplesDisjoint (map snd rows) ->
    TrsF decls funcs mtrss (map fst rows) ins flops (map snd rows).
  Proof.
    intros ins flops s rows Hrun Hp Hsep.
    exists s,(sampleFold (map snd rows)); split.
    - eapply sampled_source_result; eassumption.
    - rewrite sampled_flop_state; apply sample_fold_observed; exact Hsep.
  Qed.

  (** A transition applies the computed delta to the old register state,
      exactly as [trsNext] does. *)
  Definition TrsNextF (mprocs: Processes) (ins: InitState)
    (flops next: list InitState): Prop :=
    exists s computed,
      TrsProcsRep decls funcs mtrss (procs mprocs)
        (initState (ipsAll mprocs ins flops)) s computed /\
      hupds (initState (ipsFlops mprocs flops)) computed = initState (ipsFlops mprocs next).

  (** Only the NBA outputs need to be specified here. Active-state stability
      is derived from [ModuleWf], including for combinational processes. *)
  Definition ClockOutput (s: State) (row: Process * InitState): Prop :=
    let (proc, bindings) := row in
    if trig_clk (proc_trig proc) then
      bindings <> [] /\ exists active,
        trsProc decls funcs mtrss proc s = Sret (active,HMapStr bindings)
    else bindings = [] /\
      match trsProc decls funcs mtrss proc s with
      | Sret (_,nba) => nba = HMapEmpty
      | Fail _ => True
      end.

  Lemma clock_plan_outputs: forall s rows,
    ClockPlan decls funcs mtrss s rows -> Forall (ClockOutput s) rows.
  Proof.
    intros s rows Hplan; eapply Forall_impl; [|exact Hplan].
    intros [proc bindings] Hsample; unfold ClockSample in Hsample; unfold ClockOutput; simpl in *.
    destruct (trig_clk (proc_trig proc)).
    - destruct Hsample as [Hne [active [Heval _]]]; split; [exact Hne|eauto].
    - destruct Hsample as [-> Hsample]; split; [reflexivity|].
      destruct (trsProc decls funcs mtrss proc s) as [[active nba]|err];
        [exact (proj2 Hsample)|exact I].
  Qed.

  (** [ModuleWf] supplies active-state stability and unique state keys.
      Completion preserves those keys, so sample disjointness is derived.
      Only the merged next register state must satisfy [VF]. *)
  Definition ClockWf (mprocs: Processes) (VI: InitState -> Prop)
    (VF: list InitState -> Prop): Prop :=
    forall ins flops s, VI ins -> VF flops ->
      StateOf decls funcs mtrss mprocs ins flops s ->
      exists rows next, map fst rows = mprocs /\ Forall (ClockOutput s) rows /\
        hupds (initState (ipsFlops mprocs flops)) (sampleFold (map snd rows)) =
          initState (ipsFlops mprocs next) /\ VF next /\
        inhabited (UpdateCompletion decls funcs mtrss (procs mprocs) s
          ([] :: map snd rows) ([] :: next)).

  Lemma module_clock_plan: forall mprocs VI VF (M: ModuleWf decls funcs mtrss mprocs VI VF)
    ins flops s rows, VI ins -> VF flops ->
    StateOf decls funcs mtrss mprocs ins flops s -> map fst rows = mprocs ->
    Forall (ClockOutput s) rows -> ClockPlan decls funcs mtrss s rows.
  Proof.
    intros mprocs VI VF M ins flops s rows Hi Hf Hs Hrows Hout.
    apply Forall_forall; intros [proc bindings] Hin.
    pose proof (Forall_In Hout (proc,bindings) Hin) as Ho.
    assert (Hp: In proc (procs mprocs)).
    { right; rewrite <-Hrows; apply in_map_iff; exists (proc,bindings); auto. }
    pose proof (@module_process_settled _ _ _ _ decls funcs mtrss mprocs VI VF
      M ins flops s Hi Hf Hs proc Hp) as Hsteady.
    unfold ClockOutput in Ho; unfold ClockSample; simpl in *.
    destruct (trig_clk (proc_trig proc)).
    - destruct Ho as [Hne [active Heval]]. split; [exact Hne|].
      exists active; split; [exact Heval|].
      eapply Hsteady; exact Heval.
    - destruct Ho as [-> Hnba]; split; [reflexivity|].
      destruct (trsProc decls funcs mtrss proc s) as [[active nba]|err] eqn:Heval;
        [split; [eapply Hsteady; reflexivity|exact Hnba]|exact I].
  Qed.

  Lemma module_samples_disjoint: forall mprocs VI VF
    (M: ModuleWf decls funcs mtrss mprocs VI VF) ins next rows s,
    VI ins -> VF next -> map fst rows = mprocs ->
    UpdateCompletion decls funcs mtrss (procs mprocs) s
      ([] :: map snd rows) ([] :: next) -> SamplesDisjoint (map snd rows).
  Proof.
    intros mprocs VI VF M ins next rows s Hi Hnext Hrows C.
    pose proof (completion_keys C) as Hkeys.
    pose proof (Forall2_length Hkeys) as Hlen.
    assert (Hlength: length next = length mprocs).
    { simpl in Hlen; rewrite map_length in Hlen.
      rewrite <-Hrows, map_length; injection Hlen as Hlen; symmetry; exact Hlen. }
    pose proof (source_initial_wf (module_sources M ins next Hi Hnext)) as Hunique.
    change (KeysUnique (map fst (ins ++ concat (map fst (combineIps next mprocs))))) in Hunique.
    rewrite combineIps_bindings in Hunique by exact Hlength.
    rewrite map_app in Hunique.
    pose proof (concat_binding_keys Hkeys) as Heq; cbn [concat app] in Heq.
    apply samples_disjoint_of_unique; rewrite Heq.
    eapply keys_unique_app_right; exact Hunique.
  Qed.

  (** Complete register outputs need no separate completion certificate. *)
  Theorem clock_wf_of_full_outputs: forall mprocs VI VF,
    (forall ins flops s, VI ins -> VF flops ->
      StateOf decls funcs mtrss mprocs ins flops s ->
      exists rows, map fst rows = mprocs /\ Forall (ClockOutput s) rows /\
        hupds (initState (ipsFlops mprocs flops)) (sampleFold (map snd rows)) =
          initState (ipsFlops mprocs (map snd rows)) /\ VF (map snd rows)) ->
    ClockWf mprocs VI VF.
  Proof.
    intros mprocs VI VF Houtputs ins flops s Hi Hf Hs.
    destruct (Houtputs ins flops s Hi Hf Hs)
      as [rows [Hrows [Hout [Hnext Hvalid]]]].
    exists rows,(map snd rows); split; [exact Hrows|]; split; [exact Hout|].
    split; [exact Hnext|]; split; [exact Hvalid|].
    constructor; apply completion_refl.
  Qed.

  Definition TrsClock (mprocs: Processes) (s t: State): Prop :=
    ExecTimeSlot decls funcs mtrss (procs mprocs)
      s (clkR (procs mprocs)) (nilR (procs mprocs)) t.

  Theorem clock_std_equiv_module: forall mprocs VI VF,
    ModuleWf decls funcs mtrss mprocs VI VF -> ClockWf mprocs VI VF ->
    forall ins0 ins1 flops0, VI ins0 -> VI ins1 -> VF flops0 ->
    forall st0, StateOf decls funcs mtrss mprocs ins0 flops0 st0 ->
    exists flops1, VF flops1 /\ TrsNextF mprocs ins1 flops0 flops1 /\
      forall stf,
      StateOf decls funcs mtrss mprocs ins1 flops1 stf <->
      exists mid, TrsI decls funcs mtrss mprocs st0 mid ins1 /\ TrsClock mprocs mid stf.
  Proof.
    intros mprocs VI VF M Hclock ins0 ins1 flops0 Hi0 Hi1 Hf0 st0 Hstart.
    destruct (@module_state_exists _ _ _ _ decls funcs mtrss mprocs VI VF
      M ins1 flops0 Hi1 Hf0) as [mid Hmid].
    destruct (Hclock ins1 flops0 mid Hi1 Hf0 Hmid)
      as [rows [next [Hrows [Hout [Hnext [Hf1 [C]]]]]]].
    pose proof (module_clock_plan M Hi1 Hf0 Hmid Hrows Hout) as Hplan.
    pose proof (@module_samples_disjoint mprocs VI VF M ins1 next rows mid Hi1 Hf1 Hrows C) as Hsep.
    subst mprocs.
    pose proof (@module_inputs_ready _ _ _ _ decls funcs mtrss (map fst rows) VI VF
      M ins0 ins1 flops0 Hi0 Hi1 Hf0 st0 Hstart) as Hinputs.
    pose proof (@module_flops_ready _ _ _ _ decls funcs mtrss (map fst rows) VI VF
      M ins1 flops0 next Hi1 Hf0 Hf1 mid Hmid) as Hflops.
    exists next; split; [exact Hf1|]; split.
    - exists mid,(sampleFold (map snd rows)); split;
        [eapply sampled_source_result; eassumption|exact Hnext].
    - intros stf; split.
      + intros Hfinal; exists mid; split.
        * exact (proj1 (injection_equiv Hinputs mid) Hmid).
        * apply (proj2 (clock_slot_iff_injection Hplan stf)).
          apply (proj2 (completion_slot_iff C stf)).
          exact (proj1 (injection_equiv Hflops stf) Hfinal).
      + intros [mid' [Hi Hc]].
        pose proof (proj2 (injection_equiv Hinputs mid') Hi) as Hmid'.
        pose proof (StateOf_det Hmid Hmid') as Heq; subst mid'.
        apply (proj2 (injection_equiv Hflops stf)).
        apply (proj1 (completion_slot_iff C stf)).
        exact (proj1 (clock_slot_iff_injection Hplan stf) Hc).
  Qed.

  Definition moduleProcs (m: @VModuleDecl vid_t): Processes := tl (getProcs decls mtrss m).

  Lemma module_procs: forall m, getProcs decls mtrss m = procs (moduleProcs m).
  Proof. intros []; reflexivity. Qed.

  Definition ExecutableStateOf (m: @VModuleDecl vid_t) (ins: InitState)
    (flops: list InitState) (s: State): Prop :=
    exists computed,
      LFP (initState (ipsAll (moduleProcs m) ins flops),HMapEmpty)
        (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) (s,computed).

  (** The source transition includes [trsNext]'s merge with the old registers. *)
  Definition ExecutableTrsF (m: @VModuleDecl vid_t) (ins: InitState)
    (flops next: list InitState): Prop :=
    exists s computed,
      LFP (initState (ipsAll (moduleProcs m) ins flops),HMapEmpty)
        (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) (s,computed) /\
      fst (trsNext (initState (ipsFlops (moduleProcs m) flops))
        (trsM_IFF m (Sret (s,computed)))) = initState (ipsFlops (moduleProcs m) next).

  Lemma executable_state_iff: forall m, FlatModule m -> forall ins flops s,
    ExecutableStateOf m ins flops s <-> StateOf decls funcs mtrss (moduleProcs m) ins flops s.
  Proof.
    intros m Hflat ins flops s; unfold ExecutableStateOf, StateOf.
    split; intros [computed Hrun]; exists computed.
    - rewrite <-module_procs. apply (proj2 (flat_module_lfp decls funcs mtrss m Hflat _ _ _)); exact Hrun.
    - apply (proj1 (flat_module_lfp decls funcs mtrss m Hflat _ _ _)).
      rewrite module_procs; exact Hrun.
  Qed.

  Lemma executable_flops_iff: forall m, FlatModule m -> forall ins flops next,
    ExecutableTrsF m ins flops next <-> TrsNextF (moduleProcs m) ins flops next.
  Proof.
    intros m Hflat ins flops next; unfold ExecutableTrsF, TrsNextF.
    unfold trsNext, trsM_IFF; destruct (getIOIds m); simpl.
    split; intros [s [computed [Hrun Heq]]]; exists s,computed; split; [|exact Heq| |exact Heq].
    - rewrite <-module_procs. apply (proj2 (flat_module_lfp decls funcs mtrss m Hflat _ _ _)); exact Hrun.
    - apply (proj1 (flat_module_lfp decls funcs mtrss m Hflat _ _ _)).
      rewrite module_procs; exact Hrun.
  Qed.

  (** Both sides refer to the supplied module: the source uses its executable
      transfer function, and the standard side executes its input and clock
      event regions. Partial updates are merged with the old register values
      before the next source state is reconstructed. *)
  Theorem executable_clock_equiv: forall m VI VF,
    FlatModule m -> ModuleWf decls funcs mtrss (moduleProcs m) VI VF ->
    ClockWf (moduleProcs m) VI VF -> forall ins0 ins1 flops0,
    VI ins0 -> VI ins1 -> VF flops0 -> forall st0,
    ExecutableStateOf m ins0 flops0 st0 ->
    exists flops1, VF flops1 /\ ExecutableTrsF m ins1 flops0 flops1 /\
      forall stf, ExecutableStateOf m ins1 flops1 stf <->
      exists mid,
        ExecTimeSlot decls funcs mtrss (getProcs decls mtrss m)
          st0 (inputsR (getProcs decls mtrss m) ins1) (nilR (getProcs decls mtrss m)) mid /\
        ExecTimeSlot decls funcs mtrss (getProcs decls mtrss m)
          mid (clkR (getProcs decls mtrss m)) (nilR (getProcs decls mtrss m)) stf.
  Proof.
    intros m VI VF Hflat M Hclock ins0 ins1 flops0 Hi0 Hi1 Hf0 st0 Hstart.
    apply (proj1 (executable_state_iff m Hflat _ _ _)) in Hstart.
    destruct (@clock_std_equiv_module (moduleProcs m) VI VF M Hclock ins0 ins1 flops0 Hi0 Hi1 Hf0 st0 Hstart)
      as [flops1 [Hf1 [Hcomputed Hequiv]]].
    exists flops1; split; [exact Hf1|]; split.
    - apply (proj2 (executable_flops_iff m Hflat _ _ _)); exact Hcomputed.
    - intros stf; rewrite executable_state_iff by exact Hflat.
      rewrite module_procs; exact (Hequiv stf).
  Qed.
End ClockEquivalence.
