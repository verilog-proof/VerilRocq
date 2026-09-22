Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.Wf_nat Coq.micromega.Lia.
Require Import Lib.Lib Lang.Semantics Standard TrsProc UpdGraph ProcUpdGraph StdUpdGraph RankedGraph.

Set Implicit Arguments.

Section StdProgress.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition nodeCost (cost: vid_t -> nat) (un: unode): nat :=
    match keys un with [] => 1 | key :: _ => cost key end.

  Definition eventCost (weight: nat) (event: option Event): nat :=
    match event with
    | Some (EventUpd _) => weight
    | Some (EventEval _ _ _) => 2 * weight
    | _ => 0
    end.

  Fixpoint queueCost (cost: vid_t -> nat) (ug: ugraph) (events: Region): nat :=
    match ug, events with
    | un :: rest, event :: events => eventCost (nodeCost cost un) event + queueCost cost rest events
    | _, _ => 0
    end.

  Definition hasEdge (parent child: unode): bool :=
    existsb (fun dep => existsb (vid_eqb dep) (keys parent)) (deps child).

  Definition broadcastCost (cost: vid_t -> nat) (parent: unode) (ug: ugraph): nat :=
    fold_right (fun child n => (if hasEdge parent child then 2 * nodeCost cost child else 0) + n) 0 ug.

  Definition ScheduleCosts (cost: vid_t -> nat) (ug: ugraph): Prop :=
    Forall (fun un => broadcastCost cost un ug < nodeCost cost un) ug.

  Definition QueueEvent (proc: Process) (event: option Event): Prop :=
    match event with
    | None => True
    | Some (EventUpd upd) => upd <> HMapEmpty
    | Some (EventEval true pos evu) =>
        pos = proc_pos proc /\ evu = proc_evu proc /\ trig_stv (proc_trig proc) <> []
    | _ => False
    end.

  Definition ValidQueue (procs: Processes) (events: Region): Prop :=
    Forall2 QueueEvent procs events.

  Lemma queueCost_app: forall cost ug1 events1,
    length ug1 = length events1 -> forall ug2 events2,
    queueCost cost (ug1 ++ ug2) (events1 ++ events2) =
      queueCost cost ug1 events1 + queueCost cost ug2 events2.
  Proof.
    intros cost ug1; induction ug1 as [|un rest IH]; intros events1 Hlen ug2 events2.
    - destruct events1; [reflexivity|discriminate].
    - destruct events1; [discriminate|]; simpl in Hlen; inversion Hlen.
      simpl; rewrite IH by assumption; lia.
  Qed.

  Lemma broadcastCost_app: forall cost parent ug1 ug2,
    broadcastCost cost parent (ug1 ++ ug2) =
      broadcastCost cost parent ug1 + broadcastCost cost parent ug2.
  Proof.
    intros cost parent ug1; induction ug1; intros ug2; simpl; [reflexivity|rewrite IHug1; lia].
  Qed.

  Lemma SameGraph_queueCost: forall cost ug current,
    SameGraph ug current -> forall events, queueCost cost ug events = queueCost cost current events.
  Proof.
    intros cost ug current Hsame; induction Hsame; intros events; destruct events; try reflexivity.
    destruct H3 as [Hkeys _]; simpl; unfold nodeCost; rewrite Hkeys, IHHsame; reflexivity.
  Qed.

  Lemma SameGraph_broadcastCost: forall cost ug current,
    SameGraph ug current -> forall parent parent',
    keys parent = keys parent' -> broadcastCost cost parent ug = broadcastCost cost parent' current.
  Proof.
    intros cost ug current Hsame; induction Hsame; intros parent parent' Hparent; [reflexivity|].
    destruct H3 as [Hkeys [Hdeps _]].
    simpl; unfold hasEdge, nodeCost; rewrite Hparent, Hkeys, Hdeps.
    rewrite (IHHsame parent parent' Hparent); reflexivity.
  Qed.

  Lemma SameGraph_schedule: forall cost ug current,
    SameGraph ug current -> ScheduleCosts cost ug -> ScheduleCosts cost current.
  Proof.
    intros cost ug current Hsame Hcost; unfold ScheduleCosts in *.
    rewrite Forall_forall in *; intros un Hin.
    pose proof (SameGraph_sym Hsame) as Hback.
    eapply Forall2_In_left in Hback; [|exact Hin].
    destruct Hback as [original [Ho [Hkeys _]]].
    specialize (Hcost original Ho); unfold nodeCost in *; rewrite Hkeys.
    rewrite <-(SameGraph_broadcastCost cost Hsame original un (eq_sym Hkeys)); exact Hcost.
  Qed.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition ProcessProgress (P: State -> Prop) (procs: Processes): Prop :=
    forall proc, In proc procs -> trig_stv (proc_trig proc) <> [] -> forall s, P s ->
      exists acts nbas, trsProc decls funcs mtrss proc s = Sret (acts,nbas) /\ acts <> HMapEmpty.

  Lemma generated_edge: forall parent child proc s upd ev,
    UNodeKeysOk parent -> updf parent s = upd -> upd <> HMapEmpty ->
    UNodeStd decls funcs mtrss child proc ->
    genEvalEvent (EventUpd upd) proc = Some ev -> hasEdge parent child = true.
  Proof.
    intros parent child proc s upd ev Hkeys Hupd Hnonempty [_ [_ [Hdeps _]]] Hgen.
    unfold genEvalEvent in Hgen.
    destruct (existsb (fun v => match hfind [HEltVid v] upd with Some _ => true | None => false end)
      (trig_stv (proc_trig proc))) eqn:Hfires; [|discriminate].
    apply existsb_exists in Hfires; destruct Hfires as [dep [Hin Hfind]].
    unfold hasEdge; rewrite Hdeps; apply existsb_exists; exists dep; split; [exact Hin|].
    apply existsb_exists; exists dep; split; [|apply vid_eqb_refl].
    apply (proj1 (UNodeKeysOk_prop Hkeys s ltac:(rewrite Hupd; exact Hnonempty) dep)).
    rewrite Hupd; destruct (hfind [HEltVid dep] upd); [discriminate|discriminate].
  Qed.

  Lemma generated_cost: forall cost parent s upd,
    UNodeKeysOk parent -> updf parent s = upd -> upd <> HMapEmpty ->
    forall procs before after, GenEvalEvents (EventUpd upd) procs before after ->
    forall ug, UGraphStd decls funcs mtrss ug procs ->
    queueCost cost ug after <= queueCost cost ug before + broadcastCost cost parent ug.
  Proof.
    intros cost parent s upd Hkeys Hupd Hnonempty procs before after Hgen.
    induction Hgen; intros ug Hstd; inversion Hstd; subst; [reflexivity|].
    specialize (IHHgen _ H8).
    destruct (genEvalEvent (EventUpd (updf parent s)) proc) as [event|] eqn:HgenEvent.
    - assert (Hedge: hasEdge parent x = true).
      { eapply generated_edge with (s := s) (upd := updf parent s) (proc := proc) (ev := event);
          eassumption || reflexivity. }
      pose proof HgenEvent as Hevent; apply genEvalEvent_Some in Hevent; subst event.
      simpl; rewrite Hedge; simpl; lia.
    - simpl; destruct (hasEdge parent x); simpl; lia.
  Qed.

  Lemma generated_event_valid: forall upd proc event,
    genEvalEvent (EventUpd upd) proc = Some event -> QueueEvent proc (Some event).
  Proof.
    intros upd proc event Hgen; pose proof Hgen as Hevent.
    apply genEvalEvent_Some in Hevent; subst event.
    split; [reflexivity|]; split; [reflexivity|].
    intros Hempty; unfold genEvalEvent in Hgen; rewrite Hempty in Hgen; discriminate.
  Qed.

  Lemma generate_valid_queue: forall upd procs events,
    ValidQueue procs events -> exists next,
    GenEvalEvents (EventUpd upd) procs events next /\ ValidQueue procs next.
  Proof.
    intros upd procs events Hvalid; induction Hvalid.
    - exists []; split; constructor.
    - destruct IHHvalid as [next [Hgen Hnext]].
      exists (match genEvalEvent (EventUpd upd) x with Some event => Some event | None => y end :: next).
      split.
      + econstructor; [reflexivity|exact Hgen].
      + constructor; [|exact Hnext].
        destruct (genEvalEvent (EventUpd upd) x) eqn:Hevent; [eapply generated_event_valid; eassumption|exact H3].
  Qed.

  Lemma valid_queue_cases: forall procs events,
    ValidQueue procs events -> events = nilR procs \/
    exists ps1 proc ps2 es1 event es2,
      procs = ps1 ++ proc :: ps2 /\ events = es1 ++ Some event :: es2 /\
      ValidQueue ps1 es1 /\ QueueEvent proc (Some event) /\ ValidQueue ps2 es2.
  Proof.
    intros procs events Hvalid; induction Hvalid.
    - left; reflexivity.
    - destruct y as [event|].
      + right; exists [], x, l, [], event, l'; repeat split; try assumption; constructor.
      + destruct IHHvalid as [Heq|[ps1 [proc [ps2 [es1 [event [es2 [Hps [Hes Hrest]]]]]]]]].
        * left; simpl; rewrite Heq; reflexivity.
        * right; subst l l'; exists (x :: ps1), proc, ps2, (None :: es1), event, es2.
          split; [reflexivity|]; split; [reflexivity|].
          destruct Hrest as [Hbefore [Hselected Hafter]].
          split; [constructor; [exact I|exact Hbefore]|split; assumption].
  Qed.

  Lemma relation_slot: forall (A B: Type) (R: A -> B -> Prop)
    (left: list A) item right (before: list B) event after,
    length left = length before ->
    Forall2 R (left ++ item :: right) (before ++ event :: after) ->
    Forall2 R left before /\ R item event /\ Forall2 R right after.
  Proof.
    intros A B R left item right before event after Hlen Hrel.
    apply Forall2_app_length_inv in Hrel; [|exact Hlen].
    destruct Hrel as [Hleft Hright]; inversion Hright; subst; repeat split; assumption.
  Qed.

  Lemma update_cost: forall cost ug1 parent ug2 ps1 ps2 s upd es1 es2 next1 next2,
    ScheduleCosts cost (ug1 ++ parent :: ug2) ->
    UNodeKeysOk parent -> updf parent s = upd -> upd <> HMapEmpty ->
    UGraphStd decls funcs mtrss ug1 ps1 -> UGraphStd decls funcs mtrss ug2 ps2 ->
    GenEvalEvents (EventUpd upd) ps1 es1 next1 ->
    GenEvalEvents (EventUpd upd) ps2 es2 next2 ->
    queueCost cost (ug1 ++ parent :: ug2) (next1 ++ None :: next2) <
    queueCost cost (ug1 ++ parent :: ug2) (es1 ++ Some (EventUpd upd) :: es2).
  Proof.
    intros cost ug1 parent ug2 ps1 ps2 s upd es1 es2 next1 next2
      Hcost Hkeys Hupd Hnonempty Hstd1 Hstd2 Hgen1 Hgen2.
    pose proof (Forall2_length Hstd1) as Hlen.
    destruct (GenEvalEvents_length Hgen1) as [Hbefore Hafter].
    rewrite !queueCost_app by congruence; simpl.
    pose proof (generated_cost cost s Hkeys Hupd Hnonempty Hgen1 Hstd1) as Hleft.
    pose proof (generated_cost cost s Hkeys Hupd Hnonempty Hgen2 Hstd2) as Hright.
    unfold ScheduleCosts in Hcost; rewrite Forall_forall in Hcost.
    specialize (Hcost parent ltac:(apply in_or_app; right; left; reflexivity)).
    rewrite broadcastCost_app in Hcost; simpl in Hcost.
    destruct (hasEdge parent parent); simpl in Hcost; lia.
  Qed.

  Lemma relation_split_right: forall (A B: Type) (R: A -> B -> Prop)
    values before item after,
    Forall2 R values (before ++ item :: after) ->
    exists left value right, values = left ++ value :: right /\
      Forall2 R left before /\ R value item /\ Forall2 R right after.
  Proof.
    intros A B R values before item after Hrel.
    apply Forall2_app_inv_r in Hrel.
    destruct Hrel as [left [rest [Hleft [Hrest Heq]]]]; subst values.
    inversion Hrest; subst; exists left, x, l; repeat split; assumption || reflexivity.
  Qed.

  Lemma active_event_progress: forall cost P procs ug s events,
    ScheduleCosts cost ug -> ProcessProgress P procs -> P s ->
    UGraphStd decls funcs mtrss ug procs -> UGraphEventsStOk decls funcs mtrss ug events s ->
    ValidQueue procs events ->
    events = nilR procs \/ exists s' events',
      ExecEvent decls funcs mtrss procs s events (nilR procs) s' events' (nilR procs) /\
      ValidQueue procs events' /\ queueCost cost ug events' < queueCost cost ug events.
  Proof.
    intros cost P procs ug s events Hcost Hprogress HP Hstd Hevents Hvalid.
    destruct (valid_queue_cases Hvalid) as [Hempty|Hslot]; [left; exact Hempty|right].
    destruct Hslot as (ps1 & proc & ps2 & es1 & event & es2 & Hps & Hes & Hv1 & Hselected & Hv2).
    subst procs events.
    destruct (relation_split_right ps1 proc ps2 Hstd) as [ug1 [un [ug2 [Hug [Hstd1 [Hnode Hstd2]]]]]]; subst ug.
    assert (Hlen: length ug1 = length es1).
    { pose proof (Forall2_length Hstd1); pose proof (Forall2_length Hv1); congruence. }
    destruct (@relation_slot unode (option Event) _ ug1 un ug2 es1 (Some event) es2 Hlen Hevents) as [_ [Hevent _]].
    destruct event as [|upd|active pos evu]; [contradiction| |].
    - destruct Hevent as [[Hupd _] _].
      destruct (generate_valid_queue upd Hv1) as [next1 [Hgen1 Hnext1]].
      destruct (generate_valid_queue upd Hv2) as [next2 [Hgen2 Hnext2]].
      exists (hupds s upd), (next1 ++ None :: next2); split.
      + eapply ExecEventUpdClk; [exact Hgen1|exact Hgen2|reflexivity|reflexivity|exact Hselected].
      + split.
        * apply Forall2_app; [exact Hnext1|constructor; [exact I|exact Hnext2]].
        * eapply update_cost; try eassumption; exact (proj1 Hnode).
    - destruct active; [|contradiction].
      destruct Hselected as [Hpos [Hevu Htrigger]]; subst pos evu.
      destruct (Hprogress proc ltac:(apply in_or_app; right; left; reflexivity) Htrigger s HP)
        as [acts [nbas [Heval Hnonempty]]].
      exists s, (es1 ++ Some (EventUpd acts) :: es2); split.
      + eapply ExecEventEvalActive; [exact Heval|].
        eapply ExecEventRegionStep with (region1 := es1) (region2 := es2); reflexivity.
      + split.
        * apply Forall2_app; [exact Hv1|constructor; [exact Hnonempty|exact Hv2]].
        * rewrite !queueCost_app by exact Hlen; simpl.
          unfold ScheduleCosts in Hcost; rewrite Forall_forall in Hcost.
          specialize (Hcost un ltac:(apply in_or_app; right; left; reflexivity)); lia.
  Qed.

  Theorem standard_active_progress: forall cost P procs ug s events,
    ScheduleCosts cost ug -> ProcessProgress P procs ->
    UGraphKeysOk ug -> UGraphOk decls funcs mtrss ug procs events s ->
    GraphDomain ug P -> P s -> UpdfSub ug s -> ValidQueue procs events ->
    exists final, ExecEvents decls funcs mtrss procs s events (nilR procs)
      final (nilR procs) (nilR procs).
  Proof.
    intros cost P procs.
    assert (Hbounded: forall n ug s events, queueCost cost ug events = n ->
      ScheduleCosts cost ug -> ProcessProgress P procs ->
      UGraphKeysOk ug -> UGraphOk decls funcs mtrss ug procs events s ->
      GraphDomain ug P -> P s -> UpdfSub ug s -> ValidQueue procs events ->
      exists final, ExecEvents decls funcs mtrss procs s events (nilR procs)
        final (nilR procs) (nilR procs)).
    { induction n using lt_wf_ind; intros ug s events Hn Hcost Hprogress Hkeys
        [Hu [Hupd [Hstd Hevents]]] Hdomain HP Hsub Hvalid.
      destruct (active_event_progress Hcost Hprogress HP Hstd Hevents Hvalid)
        as [Hempty|[s' [events' [Hstep [Hvalid' Hlt]]]]].
      - subst events; exists s; constructor.
      - assert (Hall: Forall (fun _: Process => True) procs)
          by (apply Forall_forall; intros; exact I).
        destruct (ExecEvent_imp_EvalUGraphTrs Hall Hstep eq_refl eq_refl Hu Hupd Hstd Hevents)
          as [next [Htrace [Hun [Hupn [Hstdn Heventsn]]]]].
        pose proof (EvalUGraphTrs_same Htrace) as Hsame.
        destruct (graph_domain_trace Hdomain Htrace (SameGraph_refl ug)
          Hu Hkeys HP Hsub) as [HPn Hsubn].
        assert (Hcostn: ScheduleCosts cost next) by (eapply SameGraph_schedule; eassumption).
        assert (Hkeysn: UGraphKeysOk next) by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
        assert (Hdomainn: GraphDomain next P) by (eapply SameGraph_domain; eassumption).
        assert (Hokn: UGraphOk decls funcs mtrss next procs events' s') by (repeat split; assumption).
        assert (Hsmaller: queueCost cost next events' < n).
        { rewrite <-(SameGraph_queueCost cost Hsame), <-Hn; exact Hlt. }
        destruct (H3 _ Hsmaller next s' events' eq_refl Hcostn Hprogress
          Hkeysn Hokn Hdomainn HPn Hsubn Hvalid') as [final Hrest].
        exists final; eapply ExecEventsStep; eassumption. }
    intros ug s events; eapply Hbounded; reflexivity.
  Qed.

  Lemma inits_valid_queue: forall procs inits,
    length procs = length inits -> ValidQueue procs (initsR inits).
  Proof.
    induction procs as [|proc procs IH]; intros inits Hlen; destruct inits; try discriminate.
    - constructor.
    - constructor; [destruct i; [exact I|discriminate]|apply IH; simpl in Hlen; congruence].
  Qed.

  Theorem standard_slot_progress: forall cost P procs ug s inits,
    ScheduleCosts cost ug -> ProcessProgress P procs ->
    UGraphKeysOk ug -> UGraphOk decls funcs mtrss ug procs (initsR inits) s ->
    GraphDomain ug P -> P s -> UpdfSub ug s -> length procs = length inits ->
    exists final, ExecTimeSlot decls funcs mtrss procs s (initsR inits) (nilR procs) final.
  Proof.
    intros cost P procs ug s inits Hcost Hprogress Hkeys Hok Hdomain HP Hsub Hlen.
    pose proof (inits_valid_queue procs inits Hlen) as Hvalid.
    destruct (valid_queue_cases Hvalid) as [Hempty|Hnonempty].
    - exists s; rewrite Hempty; constructor.
    - destruct (standard_active_progress Hcost Hprogress Hkeys Hok Hdomain HP Hsub Hvalid)
        as [final Hrun].
      exists final; eapply ExecTimeSlotActive; [|exact Hrun|constructor].
      destruct Hnonempty as (ps1 & proc & ps2 & es1 & event & es2 & Hps & Hes & Hrest).
      intros Heq; rewrite Heq in Hes.
      assert (Hin: In (Some event) (nilR procs)) by (rewrite Hes; apply in_or_app; right; left; reflexivity).
      apply in_map_iff in Hin; destruct Hin as [p [Heq' _]]; discriminate.
  Qed.
End StdProgress.
