Require Import Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard TrsProc ProcUpdGraph StfStd SourceShape ClockSampling.

Set Implicit Arguments.

Section UpdateCompletion.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  (** Completing a partial update preserves its sensitivity keys and its
      effect. The domain is closed under individual boundary updates and
      process outputs; no execution or equivalence is assumed here. *)
  Record UpdateCompletion (ps: Processes) (initial: State)
    (raw full: list InitState): Type := {
    completion_domain: State -> Prop;
    completion_initial: completion_domain initial;
    completion_keys: Forall2 (fun a b => map fst a = map fst b) raw full;
    completion_effect: forall a b, In (a,b) (combine raw full) ->
      forall s, completion_domain s -> hupds s (HMapStr a) = hupds s (HMapStr b);
    completion_boundary: forall a, In a (raw ++ full) -> forall s,
      completion_domain s -> completion_domain (hupds s (HMapStr a));
    completion_process: forall proc, In proc ps -> forall t s active nba,
      completion_domain t -> completion_domain s ->
      trsProc decls funcs mtrss proc t = Sret (active,nba) ->
      completion_domain (hupds s active)
  }.

  Lemma completion_refl: forall ps s inits, UpdateCompletion ps s inits inits.
  Proof.
    intros; refine {| completion_domain := fun _ => True |}; try (intros; exact I).
    - induction inits; constructor; auto.
    - intros a b Hin; apply in_combine_l in Hin as Ha.
      assert (Hab: a = b).
      { clear Ha; induction inits; simpl in Hin; [contradiction|].
        destruct Hin as [Heq|Hin]; [inversion Heq; reflexivity|auto]. }
      subst; reflexivity.
  Qed.

  Lemma combine_swap_in: forall (A: Type) (xs ys: list A) a b,
    In (a,b) (combine xs ys) -> In (b,a) (combine ys xs).
  Proof.
    intros A xs; induction xs; intros [|y ys] a' b Hin; simpl in *; try contradiction.
    destruct Hin as [Heq|Hin]; [inversion Heq; left; reflexivity|right; eauto].
  Qed.

  Lemma completion_sym: forall ps s raw full,
    UpdateCompletion ps s raw full -> UpdateCompletion ps s full raw.
  Proof.
    intros ps s raw full C.
    refine {| completion_domain := completion_domain C;
      completion_initial := completion_initial C |}.
    - pose proof (completion_keys C) as Hkeys; clear C.
      induction Hkeys; constructor; congruence.
    - intros a b Hin t HP; symmetry; eapply completion_effect;
        [apply combine_swap_in; exact Hin|exact HP].
    - intros a Hin t HP; apply (completion_boundary C a); [|exact HP].
      apply in_app_or in Hin; apply in_or_app; tauto.
    - exact (completion_process C).
  Qed.

  Lemma binding_keys_none: forall a b,
    map fst a = map fst b -> (bindingEvent a = None <-> bindingEvent b = None).
  Proof. intros [|a xs] [|b ys]; simpl; intros; try discriminate; split; intros; try reflexivity; discriminate. Qed.

  Lemma binding_keys_trigger: forall a b,
    map fst a = map fst b -> forall proc,
    genEvalEvent (EventUpd (HMapStr a)) proc = genEvalEvent (EventUpd (HMapStr b)) proc.
  Proof.
    intros a b Hkeys proc.
    assert (Hpoint: forall key,
      (match hfind [HEltVid key] (HMapStr a) with Some _ => true | None => false end) =
      (match hfind [HEltVid key] (HMapStr b) with Some _ => true | None => false end)).
    { intros key.
      pose proof (same_keys_present
        (ex_intro _ a (ex_intro _ b (conj eq_refl (conj eq_refl Hkeys)))) key) as Heq.
      destruct (hfind [HEltVid key] (HMapStr a));
        destruct (hfind [HEltVid key] (HMapStr b)); intuition congruence. }
    assert (Hex: forall keys,
      existsb (fun key => match hfind [HEltVid key] (HMapStr a) with Some _ => true | None => false end) keys =
      existsb (fun key => match hfind [HEltVid key] (HMapStr b) with Some _ => true | None => false end) keys).
    { induction keys; [reflexivity|]. cbn [existsb]; rewrite Hpoint, IHkeys; reflexivity. }
    unfold genEvalEvent; rewrite Hex; reflexivity.
  Qed.

  Section Simulation.
    Variables (ps: Processes) (initial: State) (raw full: list InitState).
    Variable C: UpdateCompletion ps initial raw full.
    Let P := completion_domain C.

    Inductive Ordinary: option Event -> Prop :=
    | OrdinaryNone: Ordinary None
    | OrdinaryEval proc: In proc ps ->
        Ordinary (Some (EventEval true (proc_pos proc) (proc_evu proc)))
    | OrdinaryUpdate proc t active nba:
        In proc ps -> P t -> trsProc decls funcs mtrss proc t = Sret (active,nba) ->
        Ordinary (Some (EventUpd active)).

    Inductive EventCompleted: option Event -> option Event -> Prop :=
    | CompletedSame oe: Ordinary oe -> EventCompleted oe oe
    | CompletedPatch a b: In (a,b) (combine raw full) ->
        EventCompleted (bindingEvent a) (bindingEvent b).

    Definition RegionsCompleted := Forall2 EventCompleted.

    Lemma patch_keys: forall a b, In (a,b) (combine raw full) -> map fst a = map fst b.
    Proof.
      pose proof (completion_keys C) as Hkeys; clear P C.
      induction Hkeys; intros a b Hin; simpl in Hin; [contradiction|].
      destruct Hin as [Heq|Hin]; [inversion Heq; subst; assumption|auto].
    Qed.

    Lemma completed_none: forall oe, EventCompleted None oe -> oe = None.
    Proof.
      intros oe Heq; inversion Heq; subst; [reflexivity|].
      rewrite H3; apply (proj1 (binding_keys_none a b (patch_keys a b H4))); assumption.
    Qed.

    Lemma completed_empty: forall a,
      RegionsCompleted (nilR ps) a -> a = nilR ps.
    Proof.
      assert (Hnone: forall xs ys, RegionsCompleted xs ys ->
        Forall (fun oe => oe = None) xs -> ys = xs).
      { intros xs ys Hr; induction Hr; intros Hnil; [reflexivity|].
        inversion Hnil; subst. f_equal.
        - eapply completed_none; eassumption.
        - apply IHHr; assumption. }
      intros a Hr; apply (Hnone _ _ Hr).
      unfold nilR; apply Forall_forall; intros oe Hin.
      apply in_map_iff in Hin; destruct Hin as [proc [<- _]]; reflexivity.
    Qed.

    Lemma completed_eval: forall flag pos evu oe,
      EventCompleted (Some (EventEval flag pos evu)) oe ->
      flag = true /\ oe = Some (EventEval true pos evu) /\
      exists proc, In proc ps /\ proc_pos proc = pos /\ proc_evu proc = evu.
    Proof.
      intros flag pos evu oe Heq; inversion Heq; subst.
      - match goal with Ho: Ordinary _ |- _ => inversion Ho; subst end.
        split; [reflexivity|]; split; [reflexivity|].
        eexists; repeat split; eassumption.
      - destruct a; discriminate.
    Qed.

    Lemma completed_update: forall s ev oe,
      P s -> EventCompleted (Some ev) oe -> EventUpdClk ev ->
      exists ev', oe = Some ev' /\ EventUpdClk ev' /\
        eventUpdate s ev = eventUpdate s ev' /\ P (eventUpdate s ev) /\
        forall proc, genEvalEvent ev proc = genEvalEvent ev' proc.
    Proof.
      intros s ev oe HP Hr Hkind; inversion Hr; subst.
      - match goal with Ho: Ordinary _ |- _ => inversion Ho; subst end; try contradiction.
        exists (EventUpd active); repeat split; auto.
        eapply completion_process; eassumption.
      - destruct a as [|binding a]; [discriminate|].
        pose proof (patch_keys (binding::a) b H4) as Hkeys.
        destruct b as [|binding' b]; [discriminate|].
        injection H3 as <-. exists (EventUpd (HMapStr (binding'::b))).
        split; [reflexivity|]; split; [discriminate|]; split.
        + eapply completion_effect; eassumption.
        + split.
          * eapply completion_boundary; [|exact HP]. apply in_or_app; left.
            eapply in_combine_l; exact H4.
          * apply binding_keys_trigger; exact Hkeys.
    Qed.

    Lemma gen_completed: forall ev ev' qs a a' b,
      (forall proc, genEvalEvent ev proc = genEvalEvent ev' proc) ->
      (forall proc, In proc qs -> In proc ps) ->
      (forall proc, exists flag: bool, genEvalEvent ev proc =
        (if flag then Some (EventEval true (proc_pos proc) (proc_evu proc)) else None)) ->
      RegionsCompleted a a' -> GenEvalEvents ev qs a b ->
      exists b', GenEvalEvents ev' qs a' b' /\ RegionsCompleted b b'.
    Proof.
      intros ev ev' qs a a' b Htr Hsub Hkind Hr Hg.
      revert a' Hr Hsub.
      induction Hg as [|proc poev noev Hgen qs preg nreg Hg IH];
        intros a' Hr Hsub; inversion Hr as [|old new olds news Hpair Hrest]; subst.
      - exists []; split; constructor.
      - destruct (IH _ Hrest) as [b' [Hg' Hr']].
        { intros proc' Hin; apply Hsub; right; exact Hin. }
        exists ((match genEvalEvent ev' proc with Some ev => Some ev | None => new end)::b').
        split; [constructor; [reflexivity|exact Hg']|].
        rewrite <-Htr. constructor; [|exact Hr'].
        destruct (Hkind proc) as [flag Hflag]; rewrite Hflag.
        destruct flag; [constructor; constructor; apply Hsub; left; reflexivity|exact Hpair].
    Qed.

    Lemma completion_step: forall s act target s' act' nba',
      P s -> RegionsCompleted act target ->
      ExecEvent decls funcs mtrss ps s act (nilR ps) s' act' nba' ->
      exists target', ExecEvent decls funcs mtrss ps s target (nilR ps) s' target' (nilR ps) /\
        P s' /\ RegionsCompleted act' target' /\ nba' = nilR ps.
    Proof.
      intros s act target s' act' nba' HP Hr Hstep; destruct Hstep.
      - apply Forall2_app_inv_l in Hr; destruct Hr as [left [tail [Hleft [Htail ->]]]].
        inversion Htail; subst.
        destruct (@completed_update s1 ev y HP H10 H7)
          as [ev' [Hev [Hkind [Heffect [HP' Htrigger]]]]]; subst y.
        assert (Hactive: forall proc, exists flag: bool, genEvalEvent ev proc =
          (if flag then Some (EventEval true (proc_pos proc) (proc_evu proc)) else None)).
        { destruct ev; simpl in *; try contradiction.
          - exfalso; match goal with Hpair: EventCompleted (Some EventClkPosedge) _ |- _ =>
              inversion Hpair; subst; [match goal with Ho: Ordinary _ |- _ => inversion Ho end|destruct a; discriminate] end.
          - intros triggered; unfold genEvalEvent; eexists; reflexivity. }
        destruct (@gen_completed ev ev' procs1 act11 left act21 Htrigger ltac:(intros triggered Hin; rewrite H5; apply in_or_app; left; exact Hin) Hactive Hleft H3) as [nextleft [Hgl Hrl]].
        destruct (@gen_completed ev ev' procs2 act12 l' act22 Htrigger ltac:(intros triggered Hin; rewrite H5; apply in_or_app; right; right; exact Hin) Hactive H12 H4)
          as [nextright [Hgr Hrr]].
        exists (nextleft ++ None :: nextright); split.
        + eapply ExecEventUpdClk; [exact Hgl|exact Hgr|exact H5|exact Heffect|exact Hkind].
        + split; [exact HP'|]; split; [apply Forall2_app; [exact Hrl|constructor; [constructor; constructor|exact Hrr]]|reflexivity].
      - inversion H4; subst.
        apply Forall2_app_inv_l in Hr; destruct Hr as [left [tail [Hleft [Htail ->]]]].
        inversion Htail; subst.
        match goal with Hpair: EventCompleted (Some (EventEval _ _ _)) _ |- _ =>
          destruct (completed_eval Hpair) as [_ [-> [proc [Hin [Hpos Hevu]]]]]
        end.
        exists (left ++ Some (EventUpd uacts) :: l'); split.
        + eapply ExecEventEvalActive; [exact H3|eapply ExecEventRegionStep; reflexivity].
        + split; [exact HP|]; split; [|reflexivity].
          apply Forall2_app; [exact Hleft|constructor; [|assumption]].
          constructor; eapply OrdinaryUpdate; [exact Hin|exact HP|].
          unfold trsProc; rewrite Hpos, Hevu; exact H3.
      - inversion H4; subst.
        apply Forall2_app_inv_l in Hr; destruct Hr as [left [tail [Hleft [Htail Heq]]]].
        inversion Htail; subst.
        match goal with Hpair: EventCompleted (Some (EventEval false _ _)) _ |- _ =>
          destruct (completed_eval Hpair) as [Hfalse _]; discriminate
        end.
    Qed.

    Lemma completion_run: forall s act t done nba,
      ExecEvents decls funcs mtrss ps s act (nilR ps) t done nba ->
      forall target, P s -> RegionsCompleted act target ->
      exists final, ExecEvents decls funcs mtrss ps s target (nilR ps) t final (nilR ps) /\
        RegionsCompleted done final.
    Proof.
      intros s act t done nba Hrun; remember (nilR ps) as start in Hrun.
      induction Hrun; intros target HP Hr; subst.
      - exists target; split; [constructor|exact Hr].
      - destruct (completion_step HP Hr H3) as [next [Hstep [HP' [Hr' ->]]]].
        destruct (IHHrun eq_refl next HP' Hr') as [final [Htail Hfinal]].
        exists final; split; [econstructor; eassumption|exact Hfinal].
    Qed.

    Lemma completion_initial_regions: RegionsCompleted (initsR raw) (initsR full).
    Proof.
      assert (Hrows: forall xs ys, Forall2 (fun a b => map fst a = map fst b) xs ys ->
        (forall a b, In (a,b) (combine xs ys) -> In (a,b) (combine raw full)) ->
        RegionsCompleted (initsR xs) (initsR ys)).
      { intros xs ys Hkeys; induction Hkeys; intros Hin; constructor.
        - apply CompletedPatch; apply Hin; left; reflexivity.
        - apply IHHkeys; intros a b Hpair; apply Hin; right; exact Hpair. }
      apply Hrows; [exact (completion_keys C)|auto].
    Qed.

    Theorem completion_slot_forward: forall t,
      ExecTimeSlot decls funcs mtrss ps initial (initsR raw) (nilR ps) t ->
      ExecTimeSlot decls funcs mtrss ps initial (initsR full) (nilR ps) t.
    Proof.
      intros t Hslot; apply ExecTimeSlot_inits_events in Hslot.
      destruct (completion_run Hslot (completion_initial C) completion_initial_regions)
        as [final [Hrun Hrel]].
      pose proof (completed_empty Hrel) as ->.
      destruct (initsR_nil_dec full ps) as [Heq|Hneq].
      - rewrite Heq in Hrun; rewrite Heq. inversion Hrun; subst; [constructor|].
        exfalso; eapply ExecEvent_nilR_false; eassumption.
      - eapply ExecTimeSlotActive; [exact Hneq|exact Hrun|constructor].
    Qed.
  End Simulation.

  Theorem completion_slot_iff: forall ps s raw full,
    UpdateCompletion ps s raw full -> forall t,
    ExecTimeSlot decls funcs mtrss ps s (initsR raw) (nilR ps) t <->
    ExecTimeSlot decls funcs mtrss ps s (initsR full) (nilR ps) t.
  Proof.
    intros ps s raw full C t; split; intros Hr.
    - eapply completion_slot_forward; [exact C|exact Hr].
    - eapply completion_slot_forward; [exact (completion_sym C)|exact Hr].
  Qed.
End UpdateCompletion.
