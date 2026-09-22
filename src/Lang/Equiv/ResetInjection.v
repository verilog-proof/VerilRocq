Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard UpdGraph ProcUpdGraph StdUpdGraph RankedGraph ResetGraph GraphStructure.

Set Implicit Arguments.
Local Open Scope bool_scope.

Section ResetInjection.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  (** An injection replaces selected constant boundary functions. Computation
      functions and graph wiring stay fixed. These conditions mention no runs. *)
  Record GraphChange (old next: ugraph) (inits: list InitState)
    (injected: unode -> bool): Prop := {
    change_wiring: SameWiring old next;
    change_slots: Forall2 (fun un init =>
      injected un = isInit init /\
      (init <> [] -> deps un = [] /\ forall s, updf un s = HMapStr init)) next inits;
    change_held: Forall2 (fun un un' =>
      injected un' = false -> updf un = updf un') old next
  }.

  Lemma reset_upd_ok: forall rank ug injected,
    RankedGraph rank ug -> UGraphUnique ug -> UGraphUpdOk (resetGraph rank ug injected).
  Proof.
    intros rank ug injected Hr Hu; apply Forall_forall; intros un Hin.
    apply in_map_iff in Hin; destruct Hin as [original [Heq Hin]]; subst un.
    unfold UNodeUpdOk; simpl; intros Hd.
    pose proof (reset_valid injected original Hr Hu Hin) as Hv.
    simpl in Hv; rewrite Hd, Bool.andb_false_r in Hv; exact Hv.
  Qed.

  Lemma reset_sub: forall rank old ug inits injected s,
    RankedGraph rank ug -> UGraphUnique ug -> GraphChange old ug inits injected ->
    GraphEquations old s -> UpdfSub (resetGraph rank ug injected) s.
  Proof.
    intros rank old ug inits injected s Hr Hu [Hw Hslots Hheld] Heq.
    apply Forall_forall; intros un Hin Hdone.
    apply in_map_iff in Hin; destruct Hin as [original [Hnode Hin]]; subst un.
    pose proof (reset_valid injected original Hr Hu Hin) as Hv; rewrite Hdone in Hv.
    symmetry in Hv; apply Bool.andb_true_iff in Hv; destruct Hv as [Hnot Hd].
    apply Bool.negb_true_iff in Hnot; split; [exact Hd|].
    assert (Hlocal: Forall2 (fun before after => keys before = keys after /\
      (injected after = false -> updf before = updf after)) old ug).
    { clear -Hw Hheld; induction Hw as [|x y xs ys Hxy Hrest IH]; inversion Hheld; subst; constructor.
      - destruct Hxy as [Hk _]; split; assumption.
      - apply IH; assumption. }
    pose proof (Forall2_In_right Hlocal original Hin) as [owner [Ho [Hk Hf]]].
    intros key Hkey; simpl in Hkey; simpl; rewrite <-Hf by exact Hnot.
    apply Heq; [exact Ho|rewrite Hk; exact Hkey].
  Qed.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Lemma reset_events: forall rank old ug inits injected s,
    RankedGraph rank ug -> UGraphUnique ug -> GraphChange old ug inits injected ->
    UGraphEventsStOk decls funcs mtrss (resetGraph rank ug injected) (initsR inits) s.
  Proof.
    intros rank old ug inits injected s Hr Hu [_ Hslots _].
    unfold resetGraph, initsR.
    assert (Hrows: forall nodes initial,
      Forall2 (fun un init => injected un = isInit init /\
        (init <> [] -> deps un = [] /\ forall s, updf un s = HMapStr init)) nodes initial ->
      (forall un, In un nodes -> In un ug) ->
      Forall2 (fun un ev => UNodeEventOk decls funcs mtrss s un ev /\
        UNodeUpdEvCompl (resetGraph rank ug injected) un ev)
        (map (resetNode (S (graphHeight rank ug)) ug injected) nodes)
        (initsR initial)).
    { intros nodes initial Hrel; induction Hrel; intros Hin; [constructor|].
      destruct H3 as [Hmask Hboundary]; constructor.
      - pose proof (reset_valid injected x Hr Hu (Hin x (or_introl eq_refl))) as Hv.
        destruct y as [|binding rest].
        + simpl in Hmask; rewrite Hmask in Hv; simpl in Hv.
          split; [exact I|].
          unfold UNodeUpdEvCompl, unodeUpdCompl; simpl.
          rewrite Hv; destruct (getDepsUpdDone (resetGraph rank ug injected) (deps x)); reflexivity.
        + destruct (Hboundary ltac:(discriminate)) as [Hd Hfun].
          simpl in Hmask; rewrite Hmask in Hv; simpl in Hv.
          split; [split; [apply Hfun|exact Hv]|left; exact Hd].
      - apply IHHrel; intros un Hnode; apply Hin; right; exact Hnode. }
    apply Hrows; [exact Hslots|intros; assumption].
  Qed.

  Theorem reset_initial: forall rank old ug inits injected s procs,
    RankedGraph rank ug -> UGraphUnique ug -> GraphChange old ug inits injected ->
    UGraphStd decls funcs mtrss ug procs -> GraphEquations old s ->
    UGraphOk decls funcs mtrss (resetGraph rank ug injected) procs (initsR inits) s /\
    UpdfSub (resetGraph rank ug injected) s.
  Proof.
    intros rank old ug inits injected s procs Hr Hu Hchange Hstd Heq.
    split.
    - split; [eapply wiring_unique; [apply same_wiring; apply reset_same|exact Hu]|].
      split; [apply reset_upd_ok; assumption|].
      split; [eapply same_std; [apply reset_same|exact Hstd]|].
      eapply reset_events; eassumption.
    - eapply reset_sub; eassumption.
  Qed.
End ResetInjection.
