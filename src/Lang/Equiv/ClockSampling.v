Require Import Coq.Lists.List Coq.Arith.Wf_nat Coq.micromega.Lia.
Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard TrsProc ProcUpdGraph StfStd.

Set Implicit Arguments.

Section ClockSampling.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition ClockSample (s: State) (row: Process * InitState): Prop :=
    let (proc, bindings) := row in
    if trig_clk (proc_trig proc) then
      bindings <> [] /\ exists active,
        trsProc decls funcs mtrss proc s = Sret (active,HMapStr bindings) /\
        hmergeR s active = s
    else bindings = [] /\
      match trsProc decls funcs mtrss proc s with
      | Sret (active,nbas) => hmergeR s active = s /\ nbas = HMapEmpty
      | Fail _ => True
      end.

  Definition ClockPlan (s: State) (rows: list (Process * InitState)): Prop :=
    Forall (ClockSample s) rows.

  Definition bindingEvent (bindings: InitState): option Event :=
    match bindings with [] => None | _ => Some (EventUpd (HMapStr bindings)) end.

  Definition clockPending (rows: list (Process * InitState)): Region :=
    map (fun row => if trig_clk (proc_trig (fst row))
      then Some (EventEval false (proc_pos (fst row)) (proc_evu (fst row))) else None) rows.

  Inductive ClockCell (row: Process * InitState): option Event -> option Event -> Prop :=
  | ClockCellPending:
      trig_clk (proc_trig (fst row)) = true ->
      ClockCell row (Some (EventEval false (proc_pos (fst row)) (proc_evu (fst row)))) None
  | ClockCellDone: ClockCell row None (bindingEvent (snd row)).

  Inductive ClockQueue: list (Process * InitState) -> Region -> Region -> Prop :=
  | ClockQueueNil: ClockQueue [] [] []
  | ClockQueueCons: forall row rows act nba acts nbas,
      ClockCell row act nba -> ClockQueue rows acts nbas ->
      ClockQueue (row :: rows) (act :: acts) (nba :: nbas).

  Lemma clock_queue_lengths: forall rows act nba,
    ClockQueue rows act nba -> length rows = length act /\ length act = length nba.
  Proof. induction 1; simpl; intuition. Qed.

  Lemma clock_queue_app: forall rows1 act1 nba1 rows2 act2 nba2,
    ClockQueue rows1 act1 nba1 -> ClockQueue rows2 act2 nba2 ->
    ClockQueue (rows1 ++ rows2) (act1 ++ act2) (nba1 ++ nba2).
  Proof. induction 1; simpl; intros; [assumption|constructor; auto]. Qed.

  Lemma clock_queue_split: forall act1 nba1,
    length act1 = length nba1 -> forall rows act2 nba2,
    ClockQueue rows (act1 ++ act2) (nba1 ++ nba2) ->
    exists rows1 rows2, rows = rows1 ++ rows2 /\
      ClockQueue rows1 act1 nba1 /\ ClockQueue rows2 act2 nba2.
  Proof.
    induction act1 as [|a act1 IH]; intros [|b nba1] Hlen rows act2 nba2;
      simpl in Hlen; try discriminate; intros Hq.
    - exists [],rows; simpl; repeat split; auto using ClockQueueNil.
    - inversion Hq; subst.
      match goal with Htail: ClockQueue _ (act1 ++ act2) (nba1 ++ nba2) |- _ =>
        destruct (IH nba1 ltac:(lia) _ _ _ Htail) as [r1 [r2 [Hr [Hq1 Hq2]]]]
      end.
      subst; exists (row :: r1),r2; simpl; repeat split; auto using ClockQueueCons.
  Qed.

  Lemma clock_queue_events: forall rows act nba,
    ClockQueue rows act nba ->
    Forall (fun ev => match ev with None | Some (EventEval false _ _) => True | _ => False end) act.
  Proof. induction 1; constructor; [destruct H3; exact I|assumption]. Qed.

  Lemma clock_queue_done: forall rows act nba,
    ClockQueue rows act nba -> act = nilR (map fst rows) -> nba = initsR (map snd rows).
  Proof.
    induction 1; simpl; intros Heq; [reflexivity|].
    inversion Heq; subst. inversion H3; subst.
    unfold initsR; simpl; fold (initsR (map snd rows)).
    rewrite IHClockQueue by reflexivity; reflexivity.
  Qed.

  Lemma clock_queue_initial: forall s rows,
    ClockPlan s rows -> ClockQueue rows (clockPending rows) (nilR (map fst rows)).
  Proof.
    intros s rows Hplan; induction Hplan; [constructor|].
    destruct x as [proc bindings]; unfold ClockSample in H3; simpl in *.
    unfold clockPending, nilR in *; simpl; constructor; [|exact IHHplan].
    destruct (trig_clk (proc_trig proc)) eqn:Hclk.
    - constructor; exact Hclk.
    - destruct H3 as [-> _]; constructor.
  Qed.

  Lemma clock_queue_step: forall s rows act nba,
    ClockPlan s rows -> ClockQueue rows act nba -> forall s' act' nba',
    ExecEvent decls funcs mtrss (map fst rows) s act nba s' act' nba' ->
    s' = s /\ ClockQueue rows act' nba'.
  Proof.
    intros s rows act nba Hplan Hqueue s' act' nba' Hstep.
    pose proof (clock_queue_events Hqueue) as Hkinds.
    destruct Hstep.
    - apply Forall_app in Hkinds; destruct Hkinds as [_ Htail].
      inversion Htail; subst. destruct ev; simpl in *; contradiction.
    - pose proof (ExecEventRegion_in H4) as Hin.
      apply (Forall_In Hkinds) in Hin; contradiction.
    - split; [reflexivity|].
      destruct H6 as [a1 [a2 [b1 [b2 [old [Hlen [Ha [Ha' [Hb Hb']]]]]]]]].
      subst act nact nba nnba.
      destruct (@clock_queue_split a1 b1 Hlen rows (Some (EventEval false cpos evu) :: a2) (old :: b2) Hqueue) as [r1 [r2 [Hr [Hpre Htail]]]].
      inversion Htail; subst.
      match goal with Hcell: ClockCell _ (Some _) _ |- _ => inversion Hcell; subst end.
      apply Forall_app in Hplan; destruct Hplan as [_ Hplan]; inversion Hplan; subst.
      match goal with Hsample: ClockSample _ _ |- _ =>
        unfold ClockSample in Hsample; destruct row as [proc bindings]; simpl in *;
        match goal with Hclk: trig_clk (proc_trig proc) = true |- _ => rewrite Hclk in Hsample end;
        destruct Hsample as [Hnonempty [a [Hex Hsteady]]]
      end.
      unfold trsProc in Hex; rewrite Hex in H3; inversion H3; subst.
      apply clock_queue_app; [exact Hpre|]. constructor; [|assumption].
      destruct bindings; [contradiction|constructor].
  Qed.

  Lemma clock_queue_run: forall s rows act nba t acts nbas,
    ExecEvents decls funcs mtrss (map fst rows) s act nba t acts nbas ->
    ClockPlan s rows -> ClockQueue rows act nba ->
    t = s /\ ClockQueue rows acts nbas.
  Proof.
    intros s rows act nba t acts nbas Hrun; induction Hrun; intros Hp Hq.
    - auto.
    - destruct (clock_queue_step Hp Hq H3) as [-> Hq1].
      apply IHHrun; assumption.
  Qed.

  Definition pendingCount (act: Region): nat :=
    length (filter (fun ev => match ev with None => false | Some _ => true end) act).

  Lemma clock_queue_advance: forall s rows act nba,
    ClockPlan s rows -> ClockQueue rows act nba ->
    act = nilR (map fst rows) \/
    exists act' nba',
      ExecEvent decls funcs mtrss (map fst rows) s act nba s act' nba' /\
      ClockQueue rows act' nba' /\ pendingCount act' < pendingCount act.
  Proof.
    intros s rows act nba Hp Hq.
    assert (Hlocate: forall rows act nba, ClockQueue rows act nba ->
      act = nilR (map fst rows) \/
      exists r1 row r2 a1 a2 b1 b2,
        rows = r1 ++ row :: r2 /\
        act = a1 ++ Some (EventEval false (proc_pos (fst row)) (proc_evu (fst row))) :: a2 /\
        nba = b1 ++ None :: b2 /\ trig_clk (proc_trig (fst row)) = true /\
        ClockQueue r1 a1 b1 /\ ClockQueue r2 a2 b2).
    { intros rs acts nbas Hqueue; induction Hqueue as [|row tail ac nb acts nbas Hcell Hqueue IHloc].
      - left; reflexivity.
      - destruct Hcell.
        + right; exists [],row,tail,[],acts,[],nbas; simpl; repeat split; auto using ClockQueueNil.
        + destruct IHloc as [Heq|[r1 [r [r2 [a1 [a2 [b1 [b2 Hrest]]]]]]]].
          * left; simpl; congruence.
          * right; destruct Hrest as [Hr [Ha [Hb [Hclk [Hpre Hpost]]]]]; subst.
            exists (row::r1),r,r2,(None::a1),a2,(bindingEvent (snd row)::b1),b2.
            simpl; repeat split; auto using ClockQueueCons, ClockCellDone. }
    destruct (Hlocate _ _ _ Hq) as [Heq|[r1 [[proc bindings] [r2 [a1 [a2 [b1 [b2 Hparts]]]]]]]];
      [left; exact Heq|right].
    destruct Hparts as [Hr [Ha [Hb [Hclk [Hpre Hpost]]]]]; subst.
    apply Forall_app in Hp; destruct Hp as [_ Hp]; inversion Hp; subst; simpl in Hclk.
    match goal with Hsample: ClockSample _ _ |- _ =>
      unfold ClockSample in Hsample; simpl in Hsample; rewrite Hclk in Hsample;
      destruct Hsample as [Hnonempty [active [Hex Hsteady]]]
    end.
    exists (a1 ++ None :: a2), (b1 ++ Some (EventUpd (HMapStr bindings)) :: b2).
    split.
    - eapply ExecEventEvalNBA.
      + exact Hex.
      + eapply ExecEventRegionStep; reflexivity.
      + eapply ExecEventRegionStep; reflexivity.
      + exists a1,a2,b1,b2,None; repeat split; try reflexivity.
        exact (proj2 (clock_queue_lengths Hpre)).
    - split.
      + apply clock_queue_app; [exact Hpre|]. constructor; [|exact Hpost].
        destruct bindings; [contradiction|constructor].
      + unfold pendingCount; rewrite !filter_app, !length_app; simpl; lia.
  Qed.

  Theorem clock_queue_progress: forall s rows act nba,
    ClockPlan s rows -> ClockQueue rows act nba ->
    ExecEvents decls funcs mtrss (map fst rows) s act nba
      s (nilR (map fst rows)) (initsR (map snd rows)).
  Proof.
    intros s rows.
    assert (Hbounded: forall n act nba, pendingCount act = n ->
      ClockPlan s rows -> ClockQueue rows act nba ->
      ExecEvents decls funcs mtrss (map fst rows) s act nba
        s (nilR (map fst rows)) (initsR (map snd rows))).
    { induction n using lt_wf_ind; intros act nba Hn Hp Hq.
      destruct (clock_queue_advance Hp Hq) as [Heq|[act' [nba' [Hstep [Hnext Hlt]]]]].
      - pose proof (clock_queue_done Hq Heq) as Hnba; subst; constructor.
      - eapply ExecEventsStep; [exact Hstep|].
        eapply H3; [rewrite <-Hn; exact Hlt|reflexivity|exact Hp|exact Hnext]. }
    intros act nba; apply (Hbounded (pendingCount act) act nba eq_refl).
  Qed.

  Lemma gen_clock_pending: forall rows,
    GenEvalEvents EventClkPosedge (map fst rows) (nilR (map fst rows)) (clockPending rows).
  Proof.
    induction rows as [|[proc bindings] rows IH]; [constructor|].
    unfold clockPending, nilR in *; simpl.
    destruct (trig_clk (proc_trig proc)) eqn:Hclk.
    - eapply GenEvalEventsStepNone with (noev := Some (EventEval false (proc_pos proc) (proc_evu proc)));
        [unfold genEvalEvent; rewrite Hclk; reflexivity|exact IH].
    - eapply GenEvalEventsStepNone with (noev := None);
        [unfold genEvalEvent; rewrite Hclk; reflexivity|exact IH].
  Qed.

  Lemma gen_clock_pending_unique: forall rows next,
    GenEvalEvents EventClkPosedge (map fst rows) (nilR (map fst rows)) next ->
    next = clockPending rows.
  Proof.
    induction rows as [|[proc bindings] rows IH]; intros next Hgen; inversion Hgen; subst.
    - reflexivity.
    - unfold clockPending, nilR in *; simpl in *.
      match goal with Hg: GenEvalEvents _ _ _ _ |- _ => rewrite (IH _ Hg) end.
      unfold genEvalEvent; destruct (trig_clk (proc_trig proc)); reflexivity.
  Qed.

  Lemma clock_first_step: forall s rows,
    ExecEvent decls funcs mtrss (getProcInputClk :: map fst rows)
      s (clkR (getProcInputClk :: map fst rows)) (nilR (getProcInputClk :: map fst rows))
      s (None :: clockPending rows) (nilR (getProcInputClk :: map fst rows)).
  Proof.
    intros s rows.
    eapply ExecEventUpdClk with (procs1 := []) (proc := getProcInputClk)
      (procs2 := map fst rows) (act11 := []) (act12 := nilR (map fst rows))
      (act21 := []) (act22 := clockPending rows) (ev := EventClkPosedge).
    - constructor.
    - apply gen_clock_pending.
    - reflexivity.
    - reflexivity.
    - exact I.
  Qed.

  Lemma clock_first_inv: forall s rows s' act' nba',
    ExecEvent decls funcs mtrss (getProcInputClk :: map fst rows)
      s (clkR (getProcInputClk :: map fst rows)) (nilR (getProcInputClk :: map fst rows))
      s' act' nba' ->
    s' = s /\ act' = None :: clockPending rows /\
      nba' = nilR (getProcInputClk :: map fst rows).
  Proof.
    intros s rows s' act' nba' Hstep.
    assert (Hnil: Forall (fun ev => ev = None) (nilR (map fst rows))).
    { apply Forall_forall; intros ev Hin; apply in_map_iff in Hin;
        destruct Hin as [p [<- _]]; reflexivity. }
    inversion Hstep; subst.
    - assert (Hpre: act11 = []).
      { destruct act11 as [|a pre]; [reflexivity|].
        change (a :: (pre ++ Some ev :: act12) = Some EventClkPosedge :: nilR (map fst rows)) in H3.
        injection H3 as Hhead Htail; rewrite <-Htail in Hnil.
        apply Forall_app in Hnil; destruct Hnil as [_ Hnil]; inversion Hnil; discriminate. }
      subst act11; simpl in *.
      assert (Hps: procs1 = []).
      { pose proof (proj1 (GenEvalEvents_length H4)) as Hlen; destruct procs1; [reflexivity|discriminate]. }
      subst procs1; inversion H4; subst; simpl in *.
      inversion H6; subst. inversion H3; subst.
      repeat split; try reflexivity. f_equal; eapply gen_clock_pending_unique; eassumption.
    - match goal with Hr: ExecEventRegion (Some (EventEval _ _ _)) _ _ _ |- _ =>
        pose proof (ExecEventRegion_in Hr) as Hin end.
      simpl in Hin; destruct Hin as [Heq|Hin]; [discriminate|].
      apply (Forall_In Hnil) in Hin; discriminate.
    - match goal with Hr: ExecEventRegion (Some (EventEval _ _ _)) _ _ _ |- _ =>
        pose proof (ExecEventRegion_in Hr) as Hin end.
      simpl in Hin; destruct Hin as [Heq|Hin]; [discriminate|].
      apply (Forall_In Hnil) in Hin; discriminate.
  Qed.

  Lemma input_clock_sample: forall s,
    ClockSample s (getProcInputClk,[]).
  Proof. intros; split; [reflexivity|split; [apply hmergeR_empty|reflexivity]]. Qed.

  Theorem clock_active: forall s rows,
    ClockPlan s rows ->
    ExecActiveRegion decls funcs mtrss (getProcInputClk :: map fst rows)
      s (clkR (getProcInputClk :: map fst rows)) s (initsR ([] :: map snd rows)).
  Proof.
    intros s rows Hp; unfold ExecActiveRegion.
    eapply ExecEventsStep; [apply clock_first_step|].
    change (ExecEvents decls funcs mtrss (map fst ((getProcInputClk,[])::rows))
      s (clockPending ((getProcInputClk,[])::rows)) (nilR (map fst ((getProcInputClk,[])::rows)))
      s (nilR (map fst ((getProcInputClk,[])::rows))) (initsR (map snd ((getProcInputClk,[])::rows)))).
    apply clock_queue_progress; [constructor; [apply input_clock_sample|exact Hp]|].
    apply (clock_queue_initial (s:=s)); constructor; [apply input_clock_sample|exact Hp].
  Qed.

  Theorem clock_active_inv: forall s rows,
    ClockPlan s rows -> forall t nba,
    ExecActiveRegion decls funcs mtrss (getProcInputClk :: map fst rows)
      s (clkR (getProcInputClk :: map fst rows)) t nba ->
    t = s /\ nba = initsR ([] :: map snd rows).
  Proof.
    intros s rows Hp t nba Hrun; unfold ExecActiveRegion in Hrun.
    inversion Hrun; subst.
    match goal with Hfirst: ExecEvent _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (clock_first_inv rows Hfirst) as [Heq [Hact Hnba]]; subst
    end.
    assert (Hplan: ClockPlan s ((getProcInputClk,[])::rows))
      by (constructor; [apply input_clock_sample|exact Hp]).
    match goal with Hrest: ExecEvents _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (clock_queue_run (rows := ((getProcInputClk,[])::rows)) Hrest Hplan (clock_queue_initial Hplan)) as [Heq Hq]
    end.
    split; [exact Heq|exact (clock_queue_done Hq eq_refl)].
  Qed.

  Lemma initsR_nil_dec: forall inits ps,
    {initsR inits = nilR ps} + {initsR inits <> nilR ps}.
  Proof.
    induction inits as [|bindings rest IH]; intros [|proc ps];
      try (left; reflexivity); try (right; discriminate).
    destruct bindings as [|binding bindings]; [|right; discriminate].
    destruct (IH ps) as [Heq|Hneq]; [left; simpl; congruence|right; intro Heq; inversion Heq; contradiction].
  Qed.

  Theorem clock_slot_iff_injection: forall s rows,
    ClockPlan s rows -> forall t,
    ExecTimeSlot decls funcs mtrss (getProcInputClk :: map fst rows)
      s (clkR (getProcInputClk :: map fst rows)) (nilR (getProcInputClk :: map fst rows)) t <->
    ExecTimeSlot decls funcs mtrss (getProcInputClk :: map fst rows)
      s (initsR ([] :: map snd rows)) (nilR (getProcInputClk :: map fst rows)) t.
  Proof.
    intros s rows Hp t; split; intros Hslot.
    - apply ExecTimeSlot_nba_nilR_inv in Hslot.
      destruct Hslot as [mid [nba [Hactive Hrest]]].
      destruct (clock_active_inv Hp Hactive) as [-> ->].
      apply ExecTimeSlot_act_nilR_inv; exact Hrest.
    - eapply ExecTimeSlotActive; [discriminate|apply clock_active; exact Hp|].
      destruct (initsR_nil_dec ([] :: map snd rows) (getProcInputClk :: map fst rows)).
      + rewrite e in *; exact Hslot.
      + apply ExecTimeSlotNBA; assumption.
  Qed.
End ClockSampling.
