Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.Wf_nat.
Require Import Lib.Lib UpdGraph Standard.

Set Implicit Arguments.

Section RankedGraph.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition nodeRank (rank: vid_t -> nat) (un: unode): nat :=
    match keys un with nil => 0 | key :: _ => rank key end.

  Definition RankedGraph (rank: vid_t -> nat) (ug: ugraph): Prop :=
    forall un, In un ug -> forall dep, In dep (deps un) ->
      exists parent, In parent ug /\ In dep (keys parent) /\
        nodeRank rank parent < nodeRank rank un.

  Definition GraphEquations (ug: ugraph) (st: State): Prop :=
    forall un, In un ug -> forall key, In key (keys un) ->
      hfind [HEltVid key] st = hfind [HEltVid key] (updf un st).

  Definition SameGraph (ug1 ug2: ugraph): Prop :=
    Forall2 (fun un1 un2 => keys un1 = keys un2 /\ deps un1 = deps un2 /\
      updf un1 = updf un2) ug1 ug2.

  Lemma SameGraph_refl: forall ug, SameGraph ug ug.
  Proof.
    induction ug; constructor; [repeat split; reflexivity|assumption].
  Qed.

  Lemma SameGraph_sym: forall ug1 ug2,
    SameGraph ug1 ug2 -> SameGraph ug2 ug1.
  Proof.
    induction 1; constructor; [destruct H3 as [? [? ?]]; repeat split; congruence|assumption].
  Qed.

  Lemma SameGraph_trans: forall ug1 ug2,
    SameGraph ug1 ug2 -> forall ug3, SameGraph ug2 ug3 -> SameGraph ug1 ug3.
  Proof.
    induction 1; intros ug3 Hnext; inversion Hnext; subst; constructor.
    - destruct H3 as [? [? ?]].
      match goal with Hnode: keys _ = _ /\ deps _ = _ /\ updf _ = _ |- _ =>
        destruct Hnode as [? [? ?]]
      end.
      repeat split; congruence.
    - eapply IHForall2; eassumption.
  Qed.

  Lemma EvalUGraph_same: forall ug st ug' st',
    EvalUGraph ug st ug' st' -> SameGraph ug ug'.
  Proof.
    intros ug st ug' st' Hstep; destruct Hstep; subst.
    apply Forall2_app; [apply SameGraph_refl|].
    constructor; [repeat split; reflexivity|apply SameGraph_refl].
  Qed.

  Lemma EvalUGraphTrs_same: forall ug st ug' st',
    EvalUGraphTrs ug st ug' st' -> SameGraph ug ug'.
  Proof.
    induction 1; [apply SameGraph_refl|].
    eapply SameGraph_trans; [eapply EvalUGraph_same; eassumption|exact IHEvalUGraphTrs].
  Qed.

  Definition GraphDomain (ug: ugraph) (P: State -> Prop): Prop :=
    (forall s, P s -> UGraphUpdfAt s ug) /\
    (forall current s next s', SameGraph ug current -> P s ->
      EvalUGraph current s next s' -> P s').

  Lemma SameGraph_updf_at: forall ug current,
    SameGraph ug current -> forall s,
    UGraphUpdfAt s ug -> UGraphUpdfAt s current.
  Proof.
    induction 1; intros s Hwf; inversion Hwf; subst; constructor.
    - destruct H3 as [Hkeys [Hdeps Hfun]].
      unfold UNodeUpdfConst in *; rewrite <-Hkeys, <-Hdeps, <-Hfun; assumption.
    - apply IHForall2; assumption.
  Qed.

  Lemma graph_domain_trace: forall ug P,
    GraphDomain ug P -> forall current s next s',
    EvalUGraphTrs current s next s' ->
    SameGraph ug current -> UGraphUnique current -> UGraphKeysOk current ->
    P s -> UpdfSub current s -> P s' /\ UpdfSub next s'.
  Proof.
    intros ug P [Hat Hpres] current s next s' Hrun.
    induction Hrun; intros Hsame Hu Hk HP Hsub; [split; assumption|].
    eapply IHHrun.
    - eapply SameGraph_trans; [exact Hsame|eapply EvalUGraph_same; eassumption].
    - eapply EvalUGraph_UGraphUnique; eassumption.
    - eapply EvalUGraph_UGraphKeysOk; eassumption.
    - eapply Hpres; eassumption.
    - eapply EvalUGraph_UpdfSub_at; try eassumption.
      eapply SameGraph_updf_at; [exact Hsame|apply Hat; exact HP].
  Qed.

  Lemma SameGraph_domain: forall ug current P,
    SameGraph ug current -> GraphDomain ug P -> GraphDomain current P.
  Proof.
    intros ug current P Hsame [Hat Hpres]; split.
    - intros s HP; eapply SameGraph_updf_at; [exact Hsame|apply Hat; exact HP].
    - intros next s next' s' Hnext HP Hstep.
      eapply Hpres; [eapply SameGraph_trans; eassumption|exact HP|exact Hstep].
  Qed.

  Lemma SameGraph_equations: forall ug1 ug2,
    SameGraph ug1 ug2 -> forall st,
    GraphEquations ug2 st -> GraphEquations ug1 st.
  Proof.
    intros ug1 ug2 Hsame st Heq un Hin key Hkey.
    eapply Forall2_In_left in Hsame; [|exact Hin].
    destruct Hsame as [un2 [Hin2 [Hkeys [Hdeps Hfun]]]].
    rewrite Hfun; apply Heq; [exact Hin2|rewrite <-Hkeys; exact Hkey].
  Qed.

  Lemma SameGraph_ranked: forall rank ug1 ug2,
    SameGraph ug1 ug2 -> RankedGraph rank ug1 -> RankedGraph rank ug2.
  Proof.
    intros rank ug1 ug2 Hsame Hrank un2 Hin2 dep Hdep.
    pose proof (SameGraph_sym Hsame) as Hback.
    eapply Forall2_In_left in Hback; [|exact Hin2].
    destruct Hback as [un1 [Hin1 [Hkeys [Hdeps Hfun]]]].
    rewrite Hdeps in Hdep.
    destruct (Hrank _ Hin1 _ Hdep) as [parent1 [Hp1 [Hpk1 Hlt]]].
    eapply Forall2_In_left in Hsame; [|exact Hp1].
    destruct Hsame as [parent2 [Hp2 [Hpkeys _]]].
    exists parent2; split; [exact Hp2|]; split.
    - rewrite <-Hpkeys; exact Hpk1.
    - unfold nodeRank in *; rewrite <-Hpkeys, Hkeys; exact Hlt.
  Qed.

  Theorem graph_equations_unique: forall rank ug,
    RankedGraph rank ug -> Forall UNodeUpdfConst ug -> forall st1 st2,
    GraphEquations ug st1 -> GraphEquations ug st2 ->
    forall un, In un ug -> forall key, In key (keys un) ->
      hfind [HEltVid key] st1 = hfind [HEltVid key] st2.
  Proof.
    intros rank ug Hrank Hwf st1 st2 Hst1 Hst2.
    assert (Hnode: forall n un, nodeRank rank un = n -> In un ug ->
      forall key, In key (keys un) ->
        hfind [HEltVid key] st1 = hfind [HEltVid key] st2).
    { induction n using lt_wf_ind; intros un Hn Hin key Hkey.
      rewrite (Hst1 _ Hin _ Hkey), (Hst2 _ Hin _ Hkey).
      assert (Hfun: updf un st1 = updf un st2).
      { assert (Hlocal: UNodeUpdfConst un) by (eapply Forall_In; eassumption).
        apply Hlocal; intros dep Hdep.
        destruct (Hrank _ Hin _ Hdep) as [parent [Hp [Hpk Hlt]]].
        eapply H3; [rewrite <-Hn; exact Hlt|reflexivity|exact Hp|exact Hpk]. }
      rewrite Hfun; reflexivity. }
    intros un Hin key Hkey; eapply Hnode; [reflexivity|exact Hin|exact Hkey].
  Qed.

  Theorem ranked_complete_done: forall rank ug,
    RankedGraph rank ug -> UGraphUnique ug -> UGraphUpdCompl ug ->
    Forall (fun un => updDone un = true) ug.
  Proof.
    intros rank ug Hrank Hunique Hcomplete.
    assert (Hnode: forall n un, nodeRank rank un = n -> In un ug -> updDone un = true).
    { induction n using lt_wf_ind; intros un Hn Hin.
      assert (Hdeps: getDepsUpdDone ug (deps un) = true).
      { assert (Hparents: forall dep, In dep (deps un) -> getUpdDone ug dep = true).
        { intros dep Hdep.
          destruct (Hrank _ Hin _ Hdep) as [parent [Hp [Hpk Hlt]]].
          unfold getUpdDone.
          pose proof (UGraphUnique_getNode Hunique) as Hlookup.
          rewrite Forall_forall in Hlookup.
          rewrite (Hlookup parent Hp dep Hpk).
          eapply H3; [rewrite <-Hn; exact Hlt|reflexivity|exact Hp]. }
        induction (deps un) as [|dep rest]; [reflexivity|].
        simpl; rewrite Hparents by (left; reflexivity).
        apply IHrest; intros; apply Hparents; right; assumption. }
      pose proof Hcomplete as Hc.
      unfold UGraphUpdCompl in Hc; rewrite Forall_forall in Hc.
      specialize (Hc un Hin).
      unfold unodeUpdCompl in Hc; rewrite Hdeps in Hc; exact Hc. }
    apply Forall_forall; intros un Hin; eapply Hnode; [reflexivity|exact Hin].
  Qed.

  Theorem ranked_complete_equations: forall rank ug,
    RankedGraph rank ug -> UGraphUnique ug -> UGraphUpdCompl ug -> forall st,
    UpdfSub ug st -> GraphEquations ug st.
  Proof.
    intros rank ug Hrank Hunique Hcomplete st Hsub un Hin key Hkey.
    pose proof (ranked_complete_done Hrank Hunique Hcomplete) as Hdone.
    rewrite Forall_forall in Hdone; specialize (Hdone un Hin).
    eapply Forall_In in Hsub; [|exact Hin].
    exact (proj2 (Hsub Hdone) key Hkey).
  Qed.
End RankedGraph.
