Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib.
Import MonadNotations. Import HMapNotations. Import SZNotations.
Require Import Lang.Lang.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

(*! Update Graphs [ugraph] *)

Section UGraph.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Definition updu := vid_t.

  Record unode: Set :=
    { keys: list updu;
      deps: list updu;
      updOnce: bool; (* update is performed at least once *)
      updDone: bool; (* update is done *)
      updf: State -> State;
    }.

  Definition ugraph := list unode.

  Fixpoint getNode (ug: ugraph) (k: updu): option unode :=
    match ug with
    | nil => None
    | un :: nug => if (List.existsb (vid_eqb k) (keys un)) then Some un else getNode nug k
    end.

  Definition getUpdOnce (ug: ugraph) (k: updu): bool :=
    match getNode ug k with
    | Some un => updOnce un
    | None => false
    end.

  Fixpoint getDepsUpdOnce (ug: ugraph) (deps: list updu): bool :=
    match deps with
    | nil => false
    | dep :: ndeps => (getUpdOnce ug dep) || (getDepsUpdOnce ug ndeps)
    end.

  Definition getUpdDone (ug: ugraph) (k: updu): bool :=
    match getNode ug k with
    | Some un => updDone un
    | None => false
    end.

  Fixpoint getDepsUpdDone (ug: ugraph) (deps: list updu): bool :=
    match deps with
    | nil => true
    | dep :: ndeps => (getUpdDone ug dep) && (getDepsUpdDone ug ndeps)
    end.

  Inductive EvalUGraph: ugraph -> State -> ugraph -> State -> Prop :=
  | EvalUGraphNode:
    forall ug ug1 un ug2,
      ug = ug1 ++ un :: ug2 ->
      (deps un = nil \/ getDepsUpdOnce ug (deps un) = true) ->
      updDone un = false ->
      forall nug nun,
        nun = {| keys := keys un;
                updOnce := true;
                updDone := getDepsUpdDone ug (deps un);
                updf := updf un;
                deps := deps un |} ->
        nug = ug1 ++ nun :: ug2 ->
        forall st nst,
          nst = hupds st (updf un st) ->
          EvalUGraph ug st nug nst.

  Inductive EvalUGraphTrs: ugraph -> State -> ugraph -> State -> Prop :=
  | EvalUGraphId: forall ug st, EvalUGraphTrs ug st ug st
  | EvalUGraphStep: forall ug1 st1 ug2 st2,
      EvalUGraph ug1 st1 ug2 st2 ->
      forall ug st,
        EvalUGraphTrs ug2 st2 ug st ->
        EvalUGraphTrs ug1 st1 ug st.

  Inductive EvalUGraphTrsR: ugraph -> State -> ugraph -> State -> Prop :=
  | EvalUGraphRId: forall ug st, EvalUGraphTrsR ug st ug st
  | EvalUGraphRStep: forall ug1 st1 ug2 st2,
      EvalUGraphTrsR ug1 st1 ug2 st2 ->
      forall ug st,
        EvalUGraph ug2 st2 ug st ->
        EvalUGraphTrsR ug1 st1 ug st.

  Definition unodeUpdCompl (ug: ugraph) (un: unode): bool :=
    (negb (getDepsUpdDone ug (deps un))) || (updDone un).

  Definition UGraphUpdCompl (ug: ugraph): Prop :=
    Forall (fun un => unodeUpdCompl ug un = true) ug.

  (** Predicate to ensure that the graph does not contain any cycles (w.r.t. keys/deps)
   * May want to make it static. *)
  Definition UGraphUpdFull (ug: ugraph): Prop :=
    Forall (fun un => updOnce un = updDone un) ug.

  Definition EvalUGraphTrsFp (ug: ugraph) (st: State) (ugf: ugraph) (stf: State): Prop :=
    EvalUGraphTrs ug st ugf stf /\ UGraphUpdCompl ugf /\ UGraphUpdFull ugf.

  Definition UGraphCycleFree (ug: ugraph): Prop :=
    forall st ugf stf,
      EvalUGraphTrs ug st ugf stf ->
      UGraphUpdCompl ugf ->
      UGraphUpdFull ugf.

  Definition UGraphStateMono (ug: ugraph): Prop :=
    forall st ugf stf,
      EvalUGraphTrs ug st ugf stf ->
      hupds st stf = stf.

  Definition UGraphBaseMono (stb: State): Prop :=
    forall ug st ugf stf,
      (EvalUGraphTrs ug st ugf stf <->
         EvalUGraphTrs ug (hupds stb st) ugf (hupds stb stf)).

  (*! Well-formedness *)

  Definition UGraphUnique (ug: ugraph): Prop :=
    forall i1 i2,
      i1 <> i2 ->
      forall un1 un2,
        List.nth_error ug i1 = Some un1 ->
        List.nth_error ug i2 = Some un2 ->
        forall key, In key (keys un1) -> In key (keys un2) -> False.

  Definition UNodeKeysOk (un: unode): Prop :=
    forall st, (updf un st = HMapEmpty) \/
                 exists vs, updf un st = HMapStr vs /\ keys un = List.map fst vs.

  Definition UGraphKeysOk (ug: ugraph): Prop :=
    Forall UNodeKeysOk ug.

  Definition UNodeDepsOk (ug: ugraph) (un: unode): Prop :=
    Forall (fun dk => getNode ug dk <> None) (deps un).

  Definition UGraphDepsOk (ug: ugraph): Prop :=
    Forall (UNodeDepsOk ug) ug.

  Definition UNodeUpdfUpd (un: unode): Prop :=
    forall v,
      In v (keys un) ->
      forall stb,
        hfind [HEltVid v] (hupds stb (updf un stb)) =
          hfind [HEltVid v] (updf un stb).

  Definition UNodeUpdfConst (un: unode): Prop :=
    forall st1 st2,
      (forall v, In v (deps un) ->
                 hfind [HEltVid v] st1 = hfind [HEltVid v] st2) ->
      updf un st1 = updf un st2.

  Definition UNodeUpdfOk (un: unode): Prop :=
    UNodeUpdfUpd un /\ UNodeUpdfConst un.

  Definition UGraphUpdfOk (ug: ugraph): Prop :=
    Forall UNodeUpdfOk ug.

  Definition UNodeUpdOk (ug: ugraph) (un: unode): Prop :=
    getDepsUpdDone ug (deps un) = false ->
    updDone un = false.

  Definition UGraphUpdOk (ug: ugraph): Prop :=
    Forall (UNodeUpdOk ug) ug.

  Definition UNodeSt (st: State) (un: unode): Prop :=
    (updOnce un = updDone un) /\
      (updDone un = true -> forall v, In v (keys un) -> hfind [HEltVid v] st <> None) /\
      (updDone un = false -> forall v, In v (keys un) -> hfind [HEltVid v] st = None).

  Definition UGraphSt (st: State) (ug: ugraph): Prop :=
    Forall (UNodeSt st) ug.

  (*! Facts *)

  Lemma getNode_Some_In:
    forall ug k un, getNode ug k = Some un ->
                    In un ug /\ In k (keys un).
  Proof using .
    induction ug as [|un ug]; simpl; intros; [discriminate|].
    destruct (existsb (vid_eqb k) (keys un)) eqn:Hkun.
    - inv H3.
      rewrite existsb_exists in Hkun; destruct Hkun as [uk [? ?]].
      apply vid_eqb_eq in H4; subst uk.
      auto.
    - specialize (IHug _ _ H3); dest.
      auto.
  Qed.

  Lemma getNode_app:
    forall ug1 ug2 k, getNode (ug1 ++ ug2) k = match getNode ug1 k with
                                               | Some un => Some un
                                               | None => getNode ug2 k
                                               end.
  Proof using .
    induction ug1; simpl; intros; [reflexivity|].
    destruct (existsb (vid_eqb k) (keys a)); [reflexivity|].
    apply IHug1.
  Qed.

  Lemma getUpdDone_cons:
    forall un ug k, getUpdDone (un :: ug) k = if existsb (vid_eqb k) (keys un)
                                              then updDone un
                                              else getUpdDone ug k.
  Proof using .
    unfold getUpdDone; simpl; intros.
    destruct (existsb _ _); reflexivity.
  Qed.

  Lemma getUpdDone_upd:
    forall ug1 pun ug2 k b,
      getUpdDone (ug1 ++ pun :: ug2) k = b ->
      forall nun,
        keys nun = keys pun ->
        updDone nun = b ->
        getUpdDone (ug1 ++ nun :: ug2) k = b.
  Proof using .
    induction ug1; simpl; intros.
    - rewrite getUpdDone_cons in H3.
      rewrite getUpdDone_cons.
      rewrite H4.
      destruct (existsb _ _); assumption.
    - rewrite getUpdDone_cons in H3.
      rewrite getUpdDone_cons.
      destruct (existsb _ _); [assumption|].
      eapply IHug1; eassumption.
  Qed.

  Lemma getDepsUpdDone_existsb:
    forall ug ndeps,
      getDepsUpdDone ug ndeps = negb (existsb (fun dep => negb (getUpdDone ug dep)) ndeps).
  Proof using .
    induction ndeps; [reflexivity|].
    simpl; destruct (getUpdDone ug a); simpl; [assumption|reflexivity].
  Qed.

  Lemma getDepsUpdOnce_existsb:
    forall ug ndeps,
      getDepsUpdOnce ug ndeps = existsb (fun dep => getUpdOnce ug dep) ndeps.
  Proof using .
    induction ndeps; [reflexivity|].
    simpl; destruct (getUpdOnce ug a); simpl; [reflexivity|assumption].
  Qed.

  Lemma getDepsUpdDone_node:
    forall ug ndeps,
      getDepsUpdDone ug ndeps = true ->
      forall dk,
        In dk ndeps ->
        exists dun, getNode ug dk = Some dun /\ updDone dun = true.
  Proof using .
    induction ndeps as [|dep ndeps]; simpl; intros; [exfalso; assumption|].
    destruct H4.
    - subst dep.
      apply Bool.andb_true_iff in H3; dest.
      unfold getUpdDone in H3.
      destruct (getNode ug dk); [|discriminate].
      eauto.
    - eapply IHndeps.
      + apply Bool.andb_true_iff in H3; dest; assumption.
      + assumption.
  Qed.

  Lemma getDepsUpdDone_new_upd_ok:
    forall ug1 pun nun ug2,
      keys nun = keys pun ->
      updDone nun = getDepsUpdDone (ug1 ++ pun :: ug2) (deps pun) ->
      getDepsUpdDone (ug1 ++ nun :: ug2) (deps pun) =
        getDepsUpdDone (ug1 ++ pun :: ug2) (deps pun).
  Proof using .
    intros.
    destruct (getDepsUpdDone (ug1 ++ pun :: ug2) (deps pun)) eqn:Hpun.
    - rewrite getDepsUpdDone_existsb in Hpun; apply Bool.negb_true_iff in Hpun.
      rewrite getDepsUpdDone_existsb; apply Bool.negb_true_iff.
      apply existsb_false_forall; intros dep; intros.
      apply Bool.negb_false_iff.
      rewrite existsb_false_forall in Hpun.
      specialize (Hpun _ H5).
      apply Bool.negb_false_iff in Hpun.
      eapply getUpdDone_upd; eassumption.
    - rewrite getDepsUpdDone_existsb in Hpun; apply Bool.negb_false_iff in Hpun.
      rewrite getDepsUpdDone_existsb; apply Bool.negb_false_iff.
      apply existsb_exists in Hpun; destruct Hpun as [dep [? ?]].
      apply existsb_exists.
      exists dep; split; [assumption|].
      apply Bool.negb_true_iff in H6.
      apply Bool.negb_true_iff.
      eapply getUpdDone_upd; eassumption.
  Qed.

  Lemma getDepsUpdDone_new_upd_others:
    forall ug1 pun nun ug2,
      keys nun = keys pun ->
      updDone pun = false ->
      forall udeps,
        getDepsUpdDone (ug1 ++ pun :: ug2) udeps = true ->
        getDepsUpdDone (ug1 ++ nun :: ug2) udeps = true.
  Proof using .
    induction udeps as [|udep udeps]; simpl; intros; [reflexivity|].
    apply Bool.andb_true_iff in H5; dest.
    apply Bool.andb_true_iff; split; [|auto; fail].
    unfold getUpdDone in *.
    destruct (getNode (ug1 ++ pun :: ug2) udep) as [uun|] eqn:Hudep; [|discriminate].
    rewrite getNode_app in *.
    destruct (getNode ug1 udep); [congruence|].
    simpl in *; rewrite H3.
    destruct (existsb _ _); [congruence|].
    rewrite Hudep; assumption.
  Qed.

  Lemma UGraphUnique_cons:
    forall un ug, UGraphUnique (un :: ug) -> UGraphUnique ug.
  Proof using .
    unfold UGraphUnique; intros.
    eapply H3 with (i1:= S i1) (i2:= S i2); try eassumption.
    intuition.
  Qed.

  Lemma UGraphUnique_getNode:
    forall ug, UGraphUnique ug ->
               Forall (fun un => forall key, In key (keys un) -> getNode ug key = Some un) ug.
  Proof using .
    intros; apply Forall_forall.
    intros un; intros.
    induction ug as [|hun tug]; [inv H4|].

    simpl.
    destruct (existsb (vid_eqb key) (keys hun)) eqn:Hhun.
    - apply existsb_exists in Hhun; destruct Hhun as [hkey [? ?]].
      apply vid_eqb_eq in H7; subst hkey.
      apply In_nth_error in H4.
      destruct H4 as [i ?].
      destruct i as [|i]; [assumption|].
      unfold UGraphUnique in H3.
      exfalso; eapply H3 with (i1:= O) (i2:= S i); try eassumption.
      + discriminate.
      + reflexivity.

    - inv H4.
      + erewrite existsb_In in Hhun; [discriminate|..].
        * eassumption.
        * apply vid_eqb_refl.
      + apply IHtug.
        * eapply UGraphUnique_cons; eassumption.
        * assumption.
  Qed.

  Lemma UGraphUnique_getNode_In:
    forall ug,
      UGraphUnique ug ->
      forall un,
        In un ug ->
        forall k,
          In k (keys un) ->
          forall iun,
            getNode ug k = Some iun ->
            iun = un.
  Proof using .
    intros.
    apply UGraphUnique_getNode in H3.
    rewrite Forall_forall in H3.
    specialize (H3 _ H4 _ H5).
    congruence.
  Qed.

  Lemma UGraphUnique_keys_equiv:
    forall ug1,
      UGraphUnique ug1 ->
      forall ug2,
        List.map keys ug1 = List.map keys ug2 ->
        UGraphUnique ug2.
  Proof using .
    unfold UGraphUnique; intros.

    assert (exists un11, nth_error ug1 i1 = Some un11 /\ keys un11 = keys un1).
    { clear -H4 H6.
      generalize dependent i1.
      generalize dependent ug2.
      induction ug1 as [|hun1 tug1]; intros.
      { exfalso; destruct ug2; [|discriminate].
        destruct i1; discriminate.
      }
      { destruct ug2 as [|hun2 tug2]; [discriminate|].
        destruct i1 as [|i1].
        { inv H4; inv H6.
          exists hun1; split; [reflexivity|assumption].
        }
        { inv H4; simpl in H6.
          eapply IHtug1; eassumption.
        }
      }
    }
    destruct H10 as [un11 [? ?]].

    assert (exists un12, nth_error ug1 i2 = Some un12 /\ keys un12 = keys un2).
    { clear -H4 H7.
      generalize dependent i2.
      generalize dependent ug2.
      induction ug1 as [|hun1 tug1]; intros.
      { exfalso; destruct ug2; [|discriminate].
        destruct i2; discriminate.
      }
      { destruct ug2 as [|hun2 tug2]; [discriminate|].
        destruct i2 as [|i2].
        { inv H4; inv H7.
          exists hun1; split; [reflexivity|assumption].
        }
        { inv H4; simpl in H7.
          eapply IHtug1; eassumption.
        }
      }
    }
    destruct H12 as [un12 [? ?]].

    eapply H3 with (un1:= un11) (un2:= un12); try eassumption.
    - rewrite H11; eassumption.
    - rewrite H13; eassumption.
  Qed.

  Lemma EvalUGraph_UGraphUnique:
    forall ug1,
      UGraphUnique ug1 ->
      forall st1 ug2 st2,
        EvalUGraph ug1 st1 ug2 st2 ->
        UGraphUnique ug2.
  Proof using .
    intros; inv H4.
    eapply UGraphUnique_keys_equiv; [eassumption|].
    rewrite !map_app; reflexivity.
  Qed.

  Lemma EvalUGraphTrs_UGraphUnique:
    forall ug1,
      UGraphUnique ug1 ->
      forall st1 ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        UGraphUnique ug2.
  Proof using .
    induction 2; simpl; intros; [assumption|].
    eapply IHEvalUGraphTrs.
    eapply EvalUGraph_UGraphUnique; eassumption.
  Qed.

  Lemma UGraphUnique_false_left:
    forall ug1 un ug2,
      UGraphUnique (ug1 ++ un :: ug2) ->
      forall un1,
        In un1 ug1 ->
        forall v, In v (keys un1) -> In v (keys un) -> False.
  Proof using .
    intros.
    apply In_nth_error in H4; destruct H4 as [n1 ?].
    pose proof (nth_error_Some ug1 n1).
    rewrite H4 in H7; destruct H7 as [? _]; specialize (H7 ltac:(discriminate)).
    eapply H3 with (i1:= n1) (i2:= length ug1) (un1:= un1) (un2:= un); try eassumption.
    - apply PeanoNat.Nat.lt_neq; assumption.
    - rewrite <-H4.
      apply nth_error_app1; assumption.
    - rewrite nth_error_app2.
      + rewrite PeanoNat.Nat.sub_diag; reflexivity.
      + constructor.
  Qed.

  Lemma UGraphUnique_false_right:
    forall ug1 un ug2,
      UGraphUnique (ug1 ++ un :: ug2) ->
      forall un2,
        In un2 ug2 ->
        forall v, In v (keys un2) -> In v (keys un) -> False.
  Proof using .
    intros.
    apply In_nth_error in H4; destruct H4 as [n2 ?].
    pose proof (nth_error_Some ug2 n2).
    rewrite H4 in H7; destruct H7 as [? _]; specialize (H7 ltac:(discriminate)).
    eapply H3 with (i1:= (S n2 + length ug1)%nat) (i2:= length ug1) (un1:= un2) (un2:= un); try eassumption.
    - simpl; intro Hx; apply eq_sym in Hx.
      eapply PeanoNat.Nat.succ_add_discr; eassumption.
    - rewrite <-H4.
      rewrite nth_error_app2.
      + rewrite <-PeanoNat.Nat.add_sub_assoc by constructor.
        rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r.
        reflexivity.
      + apply PeanoNat.Nat.le_add_l.
    - rewrite nth_error_app2.
      + rewrite PeanoNat.Nat.sub_diag; reflexivity.
      + constructor.
  Qed.

  Lemma UNodeKeysOk_HMapStrEmpty:
    forall un, UNodeKeysOk un -> forall st, HMapStrEmpty (updf un st).
  Proof using .
    intros.
    specialize (H3 st); destruct H3.
    - rewrite H3; red; auto.
    - dest; rewrite H3; red; auto.
  Qed.

  Lemma UNodeKeysOk_prop:
    forall un,
      UNodeKeysOk un ->
      forall st,
        updf un st <> [] ->
        forall v, hfind [HEltVid v] (updf un st) <> None <-> In v (keys un).
  Proof using .
    intros.
    specialize (H3 st).
    destruct H3; [elim H4; assumption|].
    destruct H3 as [vs [? ?]].
    rewrite H3, H5; simpl.
    split; intros.
    - clear -H6; induction vs as [|[hk hv] vs]; simpl in *; [intuition|].
      destruct (vid_eqb v hk) eqn:Hv; [|intuition; fail].
      apply vid_eqb_eq in Hv; auto.
    - apply in_map_iff in H6; destruct H6 as [[tk tv] [? ?]]; simpl in *; subst.
      clear -H7; induction vs as [|[hk hv] vs]; simpl in *; [exfalso; auto|].
      destruct H7.
      + inv H; rewrite vid_eqb_refl; discriminate.
      + destruct (vid_eqb v hk); [discriminate|intuition].
  Qed.

  Lemma EvalUGraph_UGraphKeysOk:
    forall ug1,
      UGraphKeysOk ug1 ->
      forall st1 ug2 st2,
        EvalUGraph ug1 st1 ug2 st2 ->
        UGraphKeysOk ug2.
  Proof using .
    intros; inv H4.
    red in H3; rewrite Forall_app in H3; dest.
    inv H4.
    apply Forall_app; split; [assumption|].
    constructor; assumption.
  Qed.

  Lemma EvalUGraphTrs_UGraphKeysOk:
    forall ug1,
      UGraphKeysOk ug1 ->
      forall st1 ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        UGraphKeysOk ug2.
  Proof using .
    induction 2; simpl; intros; [assumption|].
    eapply IHEvalUGraphTrs.
    eapply EvalUGraph_UGraphKeysOk; eassumption.
  Qed.

  Lemma EvalUGraph_UGraphUpdfOk:
    forall ug1,
      UGraphUpdfOk ug1 ->
      forall st1 ug2 st2,
        EvalUGraph ug1 st1 ug2 st2 ->
        UGraphUpdfOk ug2.
  Proof using .
    intros; inv H4.
    red in H3; rewrite Forall_app in H3; dest.
    inv H4.
    apply Forall_app; split; [assumption|].
    constructor; assumption.
  Qed.

  Lemma EvalUGraphTrs_UGraphUpdfOk:
    forall ug1,
      UGraphUpdfOk ug1 ->
      forall st1 ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        UGraphUpdfOk ug2.
  Proof using .
    induction 2; simpl; intros; [assumption|].
    eapply IHEvalUGraphTrs.
    eapply EvalUGraph_UGraphUpdfOk; eassumption.
  Qed.

  Lemma UGraphDepsOk_keys_equiv:
    forall ug1,
      UGraphDepsOk ug1 ->
      forall ug2,
        List.map keys ug1 = List.map keys ug2 ->
        List.map deps ug1 = List.map deps ug2 ->
        UGraphDepsOk ug2.
  Proof using .
    unfold UGraphDepsOk; intros.

    rewrite Forall_forall in H3.
    apply Forall_forall; intros un2 ?.
    assert (exists un1, In un1 ug1 /\ deps un1 = deps un2) as Hun1.
    { clear -H5 H6.
      generalize dependent ug1.
      induction ug2 as [|hun2 ug2]; simpl; intros.
      { destruct ug1; [elim H6; fail|discriminate]. }
      { destruct ug1 as [|hun1 ug1]; [discriminate|].
        simpl in *; inv H5.
        destruct H6.
        { subst; exists hun1; auto. }
        { specialize (IHug2 H _ H2).
          destruct IHug2 as [un1 [? ?]].
          exists un1; auto.
        }
      }
    }

    destruct Hun1 as [un1 [? ?]].
    specialize (H3 _ H7).
    red in H3; rewrite Forall_forall in H3.
    apply Forall_forall; intros dk ?.
    rewrite H8 in H3; specialize (H3 _ H9).

    clear -H3 H4.
    generalize dependent ug1.
    induction ug2 as [|un2 ug2]; simpl; intros.
    - destruct ug1; simpl in *; [elim H3; reflexivity|discriminate].
    - destruct ug1 as [|un1 ug1]; [discriminate|].
      simpl in *; inv H4.
      destruct (existsb _ _); [discriminate|].
      eapply IHug2; eassumption.
  Qed.

  Lemma EvalUGraphTrs_one:
    forall ug1 st1 ug2 st2,
      EvalUGraph ug1 st1 ug2 st2 ->
      EvalUGraphTrs ug1 st1 ug2 st2.
  Proof using .
    intros.
    econstructor; [eassumption|].
    constructor.
  Qed.

  Lemma EvalUGraphTrs_trs:
    forall ug0 st0 ug1 st1,
      EvalUGraphTrs ug0 st0 ug1 st1 ->
      forall ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        EvalUGraphTrs ug0 st0 ug2 st2.
  Proof using .
    induction 1; simpl; intros; [assumption|].
    econstructor; eauto.
  Qed.

  Lemma EvalUGraphTrsR_one:
    forall ug1 st1 ug2 st2,
      EvalUGraph ug1 st1 ug2 st2 ->
      EvalUGraphTrsR ug1 st1 ug2 st2.
  Proof using .
    intros.
    econstructor; [|eassumption].
    constructor.
  Qed.

  Lemma EvalUGraphTrsR_trs:
    forall ug0 st0 ug1 st1,
      EvalUGraphTrsR ug0 st0 ug1 st1 ->
      forall ug2 st2,
        EvalUGraphTrsR ug1 st1 ug2 st2 ->
        EvalUGraphTrsR ug0 st0 ug2 st2.
  Proof using .
    intros.
    generalize dependent st0.
    generalize dependent ug0.
    induction H4; simpl; intros; [assumption|].
    specialize (IHEvalUGraphTrsR _ _ H5).
    econstructor.
    - eapply IHEvalUGraphTrsR.
    - assumption.
  Qed.

  Lemma EvalUGraphTrs_r:
    forall ug1 st1 ug2 st2, EvalUGraphTrs ug1 st1 ug2 st2 -> EvalUGraphTrsR ug1 st1 ug2 st2.
  Proof using .
    induction 1; simpl; intros; [constructor; fail|].
    eapply EvalUGraphTrsR_trs; [|eassumption].
    apply EvalUGraphTrsR_one.
    assumption.
  Qed.

  Lemma EvalUGraphTrs_o:
    forall ug1 st1 ug2 st2, EvalUGraphTrsR ug1 st1 ug2 st2 -> EvalUGraphTrs ug1 st1 ug2 st2.
  Proof using .
    induction 1; simpl; intros; [constructor; fail|].
    eapply EvalUGraphTrs_trs; [eassumption|].
    apply EvalUGraphTrs_one.
    assumption.
  Qed.

  (*! Confluence of the update-graph evaluation *)
  Section Confluence.

    Definition UpdfSub (ug: ugraph) (st: State): Prop :=
      Forall (fun un =>
                updDone un = true ->
                (getDepsUpdDone ug (deps un) = true /\
                   (forall v,
                       In v (keys un) ->
                       hfind [HEltVid v] st = hfind [HEltVid v] (updf un st)))) ug.

    Definition UGSub (ug1 ug2: ugraph): Prop :=
      Forall2 (fun un1 un2 =>
                 keys un1 = keys un2 /\
                   deps un1 = deps un2 /\
                   updf un1 = updf un2 /\
                   (updDone un1 = true -> updDone un2 = true)) ug1 ug2.

    Definition UStSub (ug1: ugraph) (st1: State) (st2: State): Prop :=
      Forall (fun un1 => updDone un1 = true ->
                         forall v,
                           In v (keys un1) ->
                           hfind [HEltVid v] st1 = hfind [HEltVid v] st2) ug1.

    Definition USSub (ug1: ugraph) (st1: State) (ug2: ugraph) (st2: State): Prop :=
      UGSub ug1 ug2 /\ UStSub ug1 st1 st2.

    (** Equivalence w.r.t. the update-done ugraph nodes *)
    Definition USEquiv (ug1: ugraph) (st1: State) (ug2: ugraph) (st2: State): Prop :=
      Forall2 (fun un1 un2 =>
                 keys un1 = keys un2 /\
                   updDone un1 = updDone un2 /\
                   (updDone un1 = true ->
                    forall v,
                      In v (keys un1) ->
                      hfind [HEltVid v] st1 = hfind [HEltVid v] st2)) ug1 ug2.

    Definition UpdStEquiv (ug: ugraph) (st1 st2: State): Prop :=
      Forall (fun un => updDone un = true ->
                        forall v,
                          In v (keys un) ->
                          hfind [HEltVid v] st1 = hfind [HEltVid v] st2) ug.

    Lemma USEquiv_UpdStEquiv:
      forall ug1 st1 ug2 st2, USEquiv ug1 st1 ug2 st2 -> UpdStEquiv ug1 st1 st2.
    Proof using .
      induction 1; simpl; intros; [constructor; fail|].
      rename x into un1; rename y into un2.
      rename l into ug1; rename l' into ug2.
      dest; constructor; [assumption|apply IHForall2; assumption].
    Qed.

    Lemma UGSub_refl: forall ug, UGSub ug ug.
    Proof using .
      intros; red.
      induction ug; [constructor; fail|].
      constructor; intros; intuition.
    Qed.

    Lemma UStSub_refl: forall ug st, UStSub ug st st.
    Proof using .
      intros; apply Forall_forall; intros; reflexivity.
    Qed.

    Lemma USSub_refl: forall ug st, USSub ug st ug st.
    Proof using .
      intros; split.
      - apply UGSub_refl.
      - apply UStSub_refl.
    Qed.

    Lemma UGSub_trs:
      forall ug1 ug2,
        UGSub ug1 ug2 ->
        forall ug3, UGSub ug2 ug3 -> UGSub ug1 ug3.
    Proof using .
      induction 1; simpl; intros; [assumption|].
      rename x into un1; rename y into un2.
      rename l into ug1; rename l' into ug2.
      destruct ug3 as [|un3 ug3]; inv H5.
      specialize (IHForall2 _ H11).
      constructor; [|assumption].
      repeat split.
      - dest; congruence.
      - dest; congruence.
      - dest; congruence.
      - intuition.
    Qed.

    Lemma UStSub_trs:
      forall ug1 st1 st2,
        UStSub ug1 st1 st2 ->
        forall ug2,
          UGSub ug1 ug2 ->
          forall st3,
            UStSub ug2 st2 st3 ->
            UStSub ug1 st1 st3.
    Proof using .
      induction 1; simpl; intros; [constructor; fail|].
      rename x into un1; rename l into ug1.
      destruct ug2 as [|un2 ug2]; inv H5.
      inv H6.
      constructor.
      - intros.
        rewrite H3 by assumption.
        apply H8.
        + intuition.
        + dest; rewrite <-H7; assumption.
      - eapply IHForall; eassumption.
    Qed.

    Lemma USSub_trs:
      forall ug1 st1 ug2 st2,
        USSub ug1 st1 ug2 st2 ->
        forall ug3 st3,
          USSub ug2 st2 ug3 st3 -> USSub ug1 st1 ug3 st3.
    Proof using .
      unfold USSub; intros; dest; split.
      - eapply UGSub_trs; eassumption.
      - eapply UStSub_trs; eassumption.
    Qed.

    Lemma USSub_equiv:
      forall ug1 st1 ug2 st2,
        USSub ug1 st1 ug2 st2 -> USSub ug2 st2 ug1 st1 ->
        USEquiv ug1 st1 ug2 st2.
    Proof using .
      unfold USSub, USEquiv, UGSub, UStSub; intros; dest.
      induction H3; [constructor; fail|].
      rename x into un1; rename y into un2.
      rename l into ug1; rename l' into ug2.
      inv H4; inv H5; inv H6.
      specialize (IHForall2 H12 H13 H10).
      constructor; [|assumption].
      dest; repeat split.
      - assumption.
      - destruct (updDone un1), (updDone un2).
        all: intuition; fail.
      - assumption.
    Qed.

    Lemma EvalUGraph_UGSub:
      forall ug1 st1 ug2 st2, EvalUGraph ug1 st1 ug2 st2 -> UGSub ug1 ug2.
    Proof using .
      intros; inv H3.
      apply Forall2_app; [apply UGSub_refl|].
      constructor; [|apply UGSub_refl].
      simpl; repeat split.
      intros; congruence.
    Qed.

    Lemma EvalUGraph_updf_others:
      forall ug1 un ug2
             (* (Hugu: UGraphUnique (ug1 ++ un :: ug2)) *)
             (Hugk: UGraphKeysOk (ug1 ++ un :: ug2)) v,
        ~ In v (keys un) ->
        forall st,
          hfind [HEltVid v] st = hfind [HEltVid v] (hupds st (updf un st)).
    Proof using .
      intros.
      assert (UNodeKeysOk un) as Hun.
      { apply Forall_app in Hugk; dest.
        inv H5; assumption.
      }
      clear Hugk.

      specialize (Hun st); destruct Hun;
        [rewrite H4; rewrite hupds_empty; reflexivity|].

      destruct H4 as [uvs [? ?]].
      rewrite H4; clear H4.
      rewrite H5 in H3; clear H5.
      simpl; destruct st; simpl; try reflexivity.
      - destruct (haccessV uvs v) eqn:Hv; [|reflexivity].
        elim H3.
        eapply haccessV_Some.
        congruence.
      - clear -H3.
        rewrite <-haccessV_hbinUStr_no_effect by assumption.
        reflexivity.
    Qed.

    Definition UGraphUpdOnceMono (ug1 ug2: ugraph) :=
      Forall2 (fun un1 un2 => keys un1 = keys un2 /\ (updOnce un1 = true -> updOnce un2 = true)) ug1 ug2.

    Lemma updOnce_mono_refl:
      forall ug, UGraphUpdOnceMono ug ug.
    Proof using .
      induction ug; simpl; intros; [constructor; fail|].
      constructor; intuition.
    Qed.

    Lemma EvalUGraph_updOnce_mono:
      forall ug1 st1 ug2 st2, EvalUGraph ug1 st1 ug2 st2 -> UGraphUpdOnceMono ug1 ug2.
    Proof using .
      intros; inv H3.
      apply Forall2_app; [apply updOnce_mono_refl|].
      constructor; simpl; intros; [intuition|].
      apply updOnce_mono_refl.
    Qed.

    Lemma EvalUGraphTrs_updOnce_mono:
      forall ug1 st1 ug2 st2, EvalUGraphTrs ug1 st1 ug2 st2 -> UGraphUpdOnceMono ug1 ug2.
    Proof using .
      induction 1; simpl; intros.
      - apply updOnce_mono_refl.
      - eapply EvalUGraph_updOnce_mono in H3.
        clear H4.
        generalize dependent ug.
        induction H3; intros.
        + inv IHEvalUGraphTrs; constructor.
        + rename x into un1; rename y into un2.
          rename l into ug1; rename l' into ug2.
          destruct ug as [|un3 ug3]; inv IHEvalUGraphTrs.
          constructor.
          * dest; split; [congruence|auto].
          * apply IHForall2; assumption.
    Qed.

    Lemma EvalUGraph_hfind_not_updated:
      forall ug1 (Hugk: UGraphKeysOk ug1)
             st1 ug2 st2,
        EvalUGraph ug1 st1 ug2 st2 ->
        forall v,
          Forall (fun un => updOnce un = true -> ~ In v (keys un)) ug2 ->
          hfind [HEltVid v] st1 = hfind [HEltVid v] st2.
    Proof using .
      intros; inv H3.
      rename ug0 into ug1; rename ug3 into ug2.
      apply Forall_app in H4; dest; inv H4.
      simpl in H9; specialize (H9 eq_refl).
      eapply EvalUGraph_updf_others; eassumption.
    Qed.

    Lemma EvalUGraphTrs_hfind_not_updated:
      forall ug1 (Hugk: UGraphKeysOk ug1)
             st1 ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        forall v,
          Forall (fun un => updOnce un = true -> ~ In v (keys un)) ug2 ->
          hfind [HEltVid v] st1 = hfind [HEltVid v] st2.
    Proof using .
      induction 2; intros; [reflexivity|].
      erewrite EvalUGraph_hfind_not_updated; try eassumption.
      - apply IHEvalUGraphTrs; [|assumption].
        eapply EvalUGraph_UGraphKeysOk; eassumption.
      - eapply EvalUGraphTrs_updOnce_mono in H4.
        clear -H4 H5.
        induction H4; [constructor; fail|].
        rename x into un1; rename y into un2.
        rename l into ug1; rename l' into ug2.
        inv H5.
        constructor; auto.
        intros; destruct H.
        rewrite H2; auto.
    Qed.

    Lemma EvalUGraph_updf_other_node:
      forall ug1 un ug2
             (Hugu: UGraphUnique (ug1 ++ un :: ug2))
             (Hugk: UGraphKeysOk (ug1 ++ un :: ug2))
             nun,
        (In nun ug1 \/ In nun ug2) ->
        forall v,
          In v (keys nun) ->
          forall st,
            hfind [HEltVid v] st = hfind [HEltVid v] (hupds st (updf un st)).
    Proof using .
      intros.
      assert (forall v, In v (keys nun) -> In v (keys un) -> False) as Hk.
      { destruct H3.
        { eapply UGraphUnique_false_left; eassumption. }
        { eapply UGraphUnique_false_right; eassumption. }
      }
      specialize (Hk _ H4).
      eapply EvalUGraph_updf_others; eassumption.
    Qed.

    Lemma EvalUGraph_UStSub:
      forall ug1 (Hugu1: UGraphUnique ug1)
             (Hugk1: UGraphKeysOk ug1)
             st1 ug2 st2,
        EvalUGraph ug1 st1 ug2 st2 -> UStSub ug1 st1 st2.
    Proof using .
      intros; inv H3.
      apply Forall_app; split; [|constructor].
      - apply Forall_forall; intros.
        eapply EvalUGraph_updf_other_node; try eassumption.
        left; assumption.
      - intros; congruence.
      - apply Forall_forall; intros.
        eapply EvalUGraph_updf_other_node; try eassumption.
        right; assumption.
    Qed.

    Lemma EvalUGraph_USSub:
      forall ug1 st1 ug2 st2,
        UGraphUnique ug1 ->
        UGraphKeysOk ug1 ->
        EvalUGraph ug1 st1 ug2 st2 ->
        USSub ug1 st1 ug2 st2.
    Proof using .
      intros; split.
      - eapply EvalUGraph_UGSub; eassumption.
      - eapply EvalUGraph_UStSub; try eassumption.
    Qed.

    Lemma EvalUGraphTrs_USSub:
      forall ug1 st1 ug2 st2,
        EvalUGraphTrs ug1 st1 ug2 st2 ->
        UGraphUnique ug1 ->
        UGraphKeysOk ug1 ->
        USSub ug1 st1 ug2 st2.
    Proof using .
      induction 1; simpl; intros; [apply USSub_refl; fail|].
      eapply USSub_trs.
      - eapply EvalUGraph_USSub; eassumption.
      - apply IHEvalUGraphTrs.
        + eapply EvalUGraph_UGraphUnique; eassumption.
        + eapply EvalUGraph_UGraphKeysOk; eassumption.
    Qed.

    Lemma UGSub_getNode_None:
      forall ug1 ug2,
        UGSub ug1 ug2 ->
        forall k,
          getNode ug1 k = None ->
          getNode ug2 k = None.
    Proof using .
      induction 1; simpl; intros; [reflexivity|].
      rename x into un1; rename y into un2.
      rename l into ug1; rename l' into ug2.
      dest.
      rewrite <-H3.
      destruct (existsb _ _); [discriminate|].
      apply IHForall2; assumption.
    Qed.

    Lemma UGSub_getNode_Some:
      forall ug1 ug2,
        UGSub ug1 ug2 ->
        forall k un1,
          getNode ug1 k = Some un1 ->
          exists un2,
            getNode ug2 k = Some un2 /\
              (updDone un1 = true -> updDone un2 = true).
    Proof using .
      induction 1; simpl; intros; [discriminate|].
      rename x into hun1; rename y into hun2.
      rename l into ug1; rename l' into ug2.
      dest.
      rewrite <-H3.
      destruct (existsb _ _);
        [inv H5; exists hun2; split; intuition; fail|].
      eapply IHForall2; assumption.
    Qed.

    Lemma UGSub_getDepsUpdDone_ok:
      forall ug1 ugf1,
        UGSub ug1 ugf1 ->
        forall un unf,
          keys un = keys unf ->
          deps un = deps unf ->
          updf un = updf unf ->
          (updDone un = true -> updDone unf = true) ->
          forall ug2 ugf2,
            UGSub ug2 ugf2 ->
            forall dks,
              getDepsUpdDone (ug1 ++ un :: ug2) dks = true ->
              getDepsUpdDone (ugf1 ++ unf :: ugf2) dks = true.
    Proof using .
      intros.
      rewrite getDepsUpdDone_existsb in *.
      apply Bool.negb_true_iff in H9.
      rewrite existsb_false_forall in H9.
      apply Bool.negb_true_iff.
      apply existsb_false_forall.
      intros dk ?.
      specialize (H9 _ H10).
      apply Bool.negb_false_iff in H9.
      apply Bool.negb_false_iff.
      unfold getUpdDone in *.
      rewrite getNode_app in *.
      destruct (getNode ug1 dk) as [un1|] eqn:Hk1.
      - eapply UGSub_getNode_Some in Hk1; [|eassumption].
        destruct Hk1 as [unf1 [? ?]].
        rewrite H11; intuition.
      - eapply UGSub_getNode_None in Hk1; [|eassumption].
        rewrite Hk1.
        replace (un :: ug2) with ([un] ++ ug2) in H9 by reflexivity.
        replace (unf :: ugf2) with ([unf] ++ ugf2) by reflexivity.
        rewrite getNode_app in *.
        destruct (getNode [un] dk) as [unn|] eqn:Hk.
        + eapply UGSub_getNode_Some with (ug2:= [unf]) in Hk;
            [|repeat constructor; assumption].
          destruct Hk as [unnf [? ?]].
          rewrite H11; intuition.
        + eapply UGSub_getNode_None with (ug2:= [unf]) in Hk;
            [|repeat constructor; assumption].
          rewrite Hk.
          destruct (getNode ug2 dk) as [un2|] eqn:Hk2.
          * eapply UGSub_getNode_Some in Hk2; [|eassumption].
            destruct Hk2 as [unf2 [? ?]].
            rewrite H11; intuition.
          * discriminate.
    Qed.

    Lemma eval_ugraph_compl_UGSub:
      forall ug0 st0 ugf stf,
        EvalUGraphTrs ug0 st0 ugf stf -> UGraphUpdCompl ugf ->
        forall ug1 st1,
          UGSub ug1 ugf ->
          forall ug2 st2,
            EvalUGraph ug1 st1 ug2 st2 ->
            UGSub ug2 ugf.
    Proof using .
      unfold UGSub; intros.
      inv H6.
      rename ug3 into ug1; rename ug4 into ug2.
      apply Forall2_app_inv_l in H5; dest; subst.
      rename x into ugf1; rename x0 into ugf2.
      destruct ugf2 as [|unf ugf2]; inv H6; dest.
      apply Forall2_app; [assumption|].
      constructor; [|assumption].
      simpl; repeat split; [assumption..|].

      red in H4. (* [UGraphUpdCompl] *)
      rewrite Forall_app in H4; dest.
      inv H12.
      unfold unodeUpdCompl in H16.

      intros.
      eapply UGSub_getDepsUpdDone_ok
        with (ugf1:= ugf1) (unf:= unf) (ugf2:= ugf2) in H12; [|try assumption..].
      rewrite H7 in H12.
      destruct (getDepsUpdDone _ _); [|discriminate].
      assumption.
    Qed.

    Lemma getDepsUpdDone_updf_const:
      forall ug un,
        In un ug ->
        forall st1 st2,
          UStSub ug st1 st2 ->
          updDone un = false ->
          getDepsUpdDone ug (deps un) = true ->
          forall dk,
            In dk (deps un) ->
            hfind [HEltVid dk] st1 = hfind [HEltVid dk] st2.
    Proof using .
      unfold UStSub; intros.
      rewrite getDepsUpdDone_existsb in H6.
      apply Bool.negb_true_iff in H6.
      rewrite existsb_false_forall in H6.
      specialize (H6 _ H7).
      apply Bool.negb_false_iff in H6.

      unfold getUpdDone in H6.
      destruct (getNode ug dk) as [dun|] eqn:Hdun; [|discriminate].
      apply getNode_Some_In in Hdun; dest.
      rewrite Forall_forall in H4.
      eapply H4; eassumption.
    Qed.

    Definition UGraphUpdfAt (st: State) (ug: ugraph): Prop :=
      Forall (fun un =>
        (forall v, In v (keys un) ->
          hfind [HEltVid v] (hupds st (updf un st)) =
          hfind [HEltVid v] (updf un st)) /\ UNodeUpdfConst un) ug.

    Lemma EvalUGraph_UpdfSub_at:
      forall ug1 (Hugu: UGraphUnique ug1)
             (Hugk: UGraphKeysOk ug1)
             st1 (Hugf: UGraphUpdfAt st1 ug1),
        UpdfSub ug1 st1 ->
        forall ug2 st2,
          EvalUGraph ug1 st1 ug2 st2 ->
          UpdfSub ug2 st2.
    Proof using .
      intros.
      assert (UStSub ug1 st1 st2) as Huss by (eapply EvalUGraph_UStSub; eassumption).
      inv H4.
      rename ug0 into ug1; rename ug3 into ug2.
      assert (In un (ug1 ++ un :: ug2)) as Huni by (apply in_or_app; right; left; reflexivity).
      pose proof (getDepsUpdDone_updf_const _ Huni Huss) as Hupdfc.
      clear Huni Huss.
      apply Forall_app in H3; dest; inv H4; dest.
      apply Forall_app; split; [|constructor].

      - rewrite Forall_forall in H3.
        apply Forall_forall; intros un1; intros.
        specialize (H3 _ H4 H5); dest.
        split.
        + eapply getDepsUpdDone_new_upd_others; [|eassumption..].
          reflexivity.
        + intros uk1; intros.
          specialize (H8 _ H11).
          erewrite <-EvalUGraph_updf_other_node; try eassumption; [|left; assumption].
          rewrite H8.
          apply Forall_app in Hugf; dest.
          rewrite Forall_forall in H12; specialize (H12 _ H4).
          dest.
          erewrite H14; [reflexivity|].
          intros dk1; intros.
          eapply EvalUGraph_updf_others; [eassumption|].
          intro Hx.
          eapply getDepsUpdDone_node in H15; [|eassumption].
          destruct H15 as [dun1 [? ?]].
          eapply UGraphUnique_getNode_In in H15; try eassumption;
            [|apply in_or_app; right; left; reflexivity].
          subst dun1.
          congruence.

      - split.
        + simpl; rewrite getDepsUpdDone_new_upd_ok; [assumption|reflexivity..].
        + unfold keys at 1.
          unfold updf at 2.
          intros k; intros.

          move Hugf at bottom.
          apply Forall_app in Hugf; dest; inv H11.
          dest.
          rewrite H11 by assumption. (* [UNodeUpdfUpd] *)
          red in H12.
          specialize (H12 st1 (hupds st1 (updf un st1))).
          rewrite H12 at 1; [reflexivity|]. (* [UNodeUpdfConst] *)
          apply Hupdfc; assumption.

      - rewrite Forall_forall in H10.
        apply Forall_forall; intros un2; intros.
        specialize (H10 _ H4 H5); dest.
        split.
        + eapply getDepsUpdDone_new_upd_others; [|eassumption..].
          reflexivity.
        + intros uk2; intros.
          specialize (H10 _ H11).
          erewrite <-EvalUGraph_updf_other_node; try eassumption; [|right; assumption].
          rewrite H10.
          apply Forall_app in Hugf; dest; inv H13.
          rewrite Forall_forall in H17; specialize (H17 _ H4).
          dest.
          erewrite H14; [reflexivity|].
          intros dk2; intros.
          eapply EvalUGraph_updf_others; [eassumption|].
          intro Hx.
          eapply getDepsUpdDone_node in H8; [|eassumption].
          destruct H8 as [dun2 [? ?]].
          eapply UGraphUnique_getNode_In in H8; try eassumption;
            [|apply in_or_app; right; left; reflexivity].
          subst dun2.
          congruence.
    Qed.

    Lemma EvalUGraph_UpdfSub:
      forall ug1, UGraphUnique ug1 -> UGraphKeysOk ug1 ->
      UGraphUpdfOk ug1 -> forall st1, UpdfSub ug1 st1 ->
      forall ug2 st2, EvalUGraph ug1 st1 ug2 st2 -> UpdfSub ug2 st2.
    Proof.
      intros ug1 Hu Hk Hf st1 Hsub ug2 st2 Hstep.
      eapply EvalUGraph_UpdfSub_at; try eassumption.
      unfold UGraphUpdfAt; apply Forall_forall; intros un Hin.
      eapply Forall_In in Hf; [|exact Hin].
      destruct Hf as [Hupd Hconst]; split; [intros; apply Hupd; assumption|exact Hconst].
    Qed.

    Lemma EvalUGraphTrs_UpdfSub:
      forall ug1 (Hugu: UGraphUnique ug1)
             (Hugk: UGraphKeysOk ug1)
             (Hugf: UGraphUpdfOk ug1) st1,
        UpdfSub ug1 st1 ->
        forall ug2 st2,
          EvalUGraphTrs ug1 st1 ug2 st2 ->
          UpdfSub ug2 st2.
    Proof using .
      induction 5; simpl; intros; [assumption|].
      eapply IHEvalUGraphTrs.
      - eapply EvalUGraph_UGraphUnique; eassumption.
      - eapply EvalUGraph_UGraphKeysOk; eassumption.
      - eapply EvalUGraph_UGraphUpdfOk; eassumption.
      - eapply EvalUGraph_UpdfSub; eassumption.
    Qed.

    Lemma eval_ugraph_compl_UStSub:
      forall ug0 st0 ugf stf (Hugfs: UpdfSub ugf stf),
        EvalUGraphTrs ug0 st0 ugf stf ->
        UGraphUpdCompl ugf ->
        forall ug1 (Hugu: UGraphUnique ug1)
               (Hugk: UGraphKeysOk ug1)
               (Hugf: UGraphUpdfOk ug1) st1,
          UStSub ug1 st1 stf ->
          forall ug2 st2,
            EvalUGraph ug1 st1 ug2 st2 ->
            UGSub ug2 ugf ->
            UStSub ug2 st2 stf.
    Proof using .
      intros.
      inv H6.
      rename ug3 into ug1; rename ug4 into ug2.
      assert (In un (ug1 ++ un :: ug2)) as Huni by (apply in_or_app; right; left; reflexivity).
      pose proof (getDepsUpdDone_updf_const _ Huni H5) as Hupdfc.

      unfold UGSub, UStSub in *.
      apply Forall_app in H5; dest; inv H6.
      clear H12. (* [updDone un = true -> ..] *)
      apply Forall2_app_inv_l in H7; dest; subst.
      rename x into ugf1; rename x0 into ugf2.
      destruct ugf2 as [|unf ugf2]; inv H7; dest.
      simpl in H7, H8, H11.

      apply Forall_app; split; [|constructor].
      - rewrite Forall_forall in H5.
        apply Forall_forall; intro un1; intros.
        specialize (H5 _ H14 H15 _ H17).
        erewrite <-EvalUGraph_updf_other_node; try eassumption.
        left; assumption.

      - unfold updDone; unfold keys at 1.
        intros.
        specialize (H12 H14). (* [getDepsUpdDone .. = true -> ..] from [UGSub ug2 ugf] *)

        apply Forall_app in Hugfs; dest; inv H18.
        specialize (H21 H12); dest.
        rewrite H19 by congruence.
        rewrite <-H11.

        move Hugf at bottom.
        apply Forall_app in Hugf; dest; inv H21.
        red in H25; dest.
        rewrite H21 by assumption. (* [UNodeUpdfUpd] *)
        erewrite H23; [reflexivity|]. (* [UNodeUpdfConst] *)
        apply Hupdfc; assumption.

      - rewrite Forall_forall in H13.
        apply Forall_forall; intro un2; intros.
        specialize (H13 _ H14 H15 _ H17).
        erewrite <-EvalUGraph_updf_other_node; try eassumption.
        right; assumption.
    Qed.

    Lemma eval_ugraph_compl_sub:
      forall ug0 st0 ugf stf (Hugfs: UpdfSub ugf stf),
        EvalUGraphTrs ug0 st0 ugf stf -> UGraphUpdCompl ugf ->
        forall ug1 (Hugu: UGraphUnique ug1)
               (Hugk: UGraphKeysOk ug1)
               (Hugf: UGraphUpdfOk ug1) st1,
          USSub ug1 st1 ugf stf ->
          forall ug2 st2,
            EvalUGraph ug1 st1 ug2 st2 ->
            USSub ug2 st2 ugf stf.
    Proof using .
      unfold USSub; intros; dest.
      assert (UGSub ug2 ugf)
        as Hugs by (eapply eval_ugraph_compl_UGSub; eassumption).
      split.
      - assumption.
      - eapply eval_ugraph_compl_UStSub; try eassumption.
    Qed.

    Lemma eval_ugraph_trs_compl_sub:
      forall ug0 (Hugu0: UGraphUnique ug0)
             (Hugk0: UGraphKeysOk ug0)
             (Hugf0: UGraphUpdfOk ug0)
             st0 ugf stf (Hugfs: UpdfSub ugf stf),
        EvalUGraphTrs ug0 st0 ugf stf -> UGraphUpdCompl ugf ->
        forall ug1 st1,
          EvalUGraphTrsR ug0 st0 ug1 st1 ->
          USSub ug1 st1 ugf stf.
    Proof using .
      induction 7; simpl; intros.
      - apply EvalUGraphTrs_USSub; assumption.
      - specialize (IHEvalUGraphTrsR Hugu0 Hugk0 Hugf0 H3).
        eapply eval_ugraph_compl_sub.
        + eassumption.
        + eassumption.
        + eassumption.
        + eapply EvalUGraphTrs_UGraphUnique; [eassumption|].
          apply EvalUGraphTrs_o; eassumption.
        + eapply EvalUGraphTrs_UGraphKeysOk; [eassumption|].
          apply EvalUGraphTrs_o; eassumption.
        + eapply EvalUGraphTrs_UGraphUpdfOk; [eassumption|].
          apply EvalUGraphTrs_o; eassumption.
        + eassumption.
        + eassumption.
    Qed.

    Definition UNodeStWf (st: State) (un: unode): Prop :=
      forall v, In v (keys un) -> hfind [HEltVid v] st <> None.

    Definition UGraphStWf (st: State) (ug: ugraph): Prop :=
      Forall (UNodeStWf st) ug.

    Lemma EvalUGraph_UGraphStWf_KeysWf:
      forall ug1 (Hugk1: UGraphKeysOk ug1) st1 vs,
        HMapStrKeysWf st1 vs ->
        UGraphStWf st1 ug1 ->
        forall ug2 st2,
          EvalUGraph ug1 st1 ug2 st2 ->
          UGraphStWf st2 ug2 /\ HMapStrKeysWf st2 vs.
    Proof using .
      intros; inv H5.
      rename ug0 into ug1; rename ug3 into ug2.
      apply Forall_app in H4; dest; inv H5.
      split.
      - apply Forall_app; split; [|constructor].
        + rewrite Forall_forall in H4.
          apply Forall_forall; intro hun; intros.
          red; intros.
          specialize (H4 _ H5 _ H6).
          eapply hfind_hupds_Some; [assumption|].
          eapply UNodeKeysOk_HMapStrEmpty.
          eapply Forall_app in Hugk1; dest; inv H12; assumption.
        + red; intros.
          simpl in H5.
          specialize (H10 _ H5).
          eapply hfind_hupds_Some; [assumption|].
          eapply UNodeKeysOk_HMapStrEmpty.
          eapply Forall_app in Hugk1; dest; inv H9; assumption.
        + rewrite Forall_forall in H11.
          apply Forall_forall; intro hun; intros.
          red; intros.
          specialize (H11 _ H5 _ H6).
          eapply hfind_hupds_Some; [assumption|].
          eapply UNodeKeysOk_HMapStrEmpty.
          eapply Forall_app in Hugk1; dest; inv H12; assumption.

      - apply Forall_app in Hugk1; dest; inv H6.
        specialize (H13 st1).
        destruct H13; [rewrite H6; rewrite hupds_empty; assumption|].
        destruct H6 as [uvs [? ?]].
        rewrite H6.
        red in H10; rewrite H9 in H10.
        apply HMapStrKeysWf_hupds_no_effect; assumption.
    Qed.

    Lemma EvalUGraphTrs_UGraphStWf_KeysWf:
      forall ug1 (Hugk1: UGraphKeysOk ug1) st1 vs,
        HMapStrKeysWf st1 vs ->
        UGraphStWf st1 ug1 ->
        forall ug2 st2,
          EvalUGraphTrs ug1 st1 ug2 st2 ->
          UGraphStWf st2 ug2 /\ HMapStrKeysWf st2 vs.
    Proof using .
      induction 4; simpl; intros; [split; assumption|].
      eapply IHEvalUGraphTrs.
      - eapply EvalUGraph_UGraphKeysOk; eassumption.
      - eapply EvalUGraph_UGraphStWf_KeysWf; eassumption.
      - eapply EvalUGraph_UGraphStWf_KeysWf; eassumption.
    Qed.

    (** Initial conditions: all proven statically (syntactically) by the given processes. *)
    Variables (ug0: ugraph) (st0: State).
    Hypotheses (Hugu0: UGraphUnique ug0)
      (Hugk0: UGraphKeysOk ug0)
      (Hugf0: UGraphUpdfOk ug0)
      (Hugfs: UpdfSub ug0 st0).

    Theorem eval_ugraph_confl:
      forall ug1 st1,
        EvalUGraphTrs ug0 st0 ug1 st1 -> UGraphUpdCompl ug1 ->
        forall ug2 st2,
          EvalUGraphTrs ug0 st0 ug2 st2 -> UGraphUpdCompl ug2 ->
          USEquiv ug1 st1 ug2 st2.
    Proof using All.
      intros.
      assert (USSub ug1 st1 ug2 st2) as Hs1.
      { eapply eval_ugraph_trs_compl_sub; try eassumption.
        { eapply EvalUGraphTrs_UpdfSub; eassumption. }
        { apply EvalUGraphTrs_r; assumption. }
      }
      assert (USSub ug2 st2 ug1 st1) as Hs2.
      { eapply eval_ugraph_trs_compl_sub; try eassumption.
        { eapply EvalUGraphTrs_UpdfSub; eassumption. }
        { apply EvalUGraphTrs_r; assumption. }
      }
      apply USSub_equiv; assumption.
    Qed.

    (** Additional initial conditions to prove the confluence by state equality *)
    Variable vs: list vid_t.
    Hypotheses (Hugwf0: UGraphStWf st0 ug0)
      (Hvs0: HMapStrKeysWf st0 vs).

    Lemma eval_ugraph_confl_state_eq_ind:
      forall ug1 st1,
        EvalUGraphTrs ug0 st0 ug1 st1 -> UGraphUpdCompl ug1 -> UGraphUpdFull ug1 ->
        forall ug2 st2,
          EvalUGraphTrs ug0 st0 ug2 st2 -> UGraphUpdCompl ug2 -> UGraphUpdFull ug2 ->
          st1 = st2.
    Proof using All.
      intros.
      pose proof (eval_ugraph_confl H3 H4 H6 H7) as Hcfl.
      pose proof (EvalUGraphTrs_hfind_not_updated Hugk0 H3).
      pose proof (EvalUGraphTrs_hfind_not_updated Hugk0 H6).
      eapply HMapStrKeysWf_hfind_eq;
        [eapply EvalUGraphTrs_UGraphStWf_KeysWf; eassumption
        |eapply EvalUGraphTrs_UGraphStWf_KeysWf; eassumption
        |].
      clear H3 H4 H6 H7.
      intros.

      assert (Forall (fun un : unode => updDone un = true -> ~ In v (keys un)) ug1 \/
                (exists un1, In un1 ug1 /\ updDone un1 = true /\ In v (keys un1))) as Hv.
      { clear -H1. (* [vid_ops] *)
        induction ug1 as [|un1 ug1]; [left; constructor; fail|].
        destruct IHug1.
        { destruct (updDone un1) eqn:Hun1.
          { destruct (in_dec vid_eq_dec v (keys un1)).
            { right; eexists; repeat split.
              { left; reflexivity. }
              { assumption. }
              { assumption. }
            }
            { left; constructor; [|assumption].
              intros; assumption.
            }
          }
          { left; constructor; [|assumption].
            intros; congruence.
          }
        }
        { destruct H as [dun1 [? [? ?]]].
          right; exists dun1; repeat split; try assumption.
          right; assumption.
        }
      }
      destruct Hv.

      - assert (Forall (fun un : unode => updOnce un = true -> ~ In v (keys un)) ug1).
        { clear -H3 H5.
          induction ug1 as [|un1 ug1]; [constructor; fail|].
          inv H3; inv H5.
          constructor; [|apply IHug1; assumption].
          intros; apply H2; congruence.
        }

        assert (Forall (fun un : unode => updOnce un = true -> ~ In v (keys un)) ug2).
        { clear -H4 H5 H8 Hcfl.
          induction Hcfl; [constructor; fail|].
          rename x into un1; rename y into un2.
          rename l into ug1; rename l' into ug2.
          inv H4; inv H5; inv H8; dest.
          constructor; [|eapply IHHcfl; eassumption].
          intros; rewrite <-H3.
          apply H9.
          congruence.
        }
        rewrite <-H9 by assumption.
        rewrite <-H10 by assumption.
        reflexivity.

      - destruct H3 as [un1 [? [? ?]]].
        apply in_split in H3; destruct H3 as [ug11 [ug12 ?]]; subst ug1.
        apply Forall2_app_inv_l in Hcfl; dest.
        inv H7; dest.
        apply H12; assumption.
    Qed.

    Theorem eval_ugraph_confl_state_eq:
      forall ug1 st1,
        EvalUGraphTrsFp ug0 st0 ug1 st1 ->
        forall ug2 st2,
          EvalUGraphTrsFp ug0 st0 ug2 st2 ->
          st1 = st2.
    Proof using All.
      unfold EvalUGraphTrsFp; intros; dest.
      eapply eval_ugraph_confl_state_eq_ind; eassumption.
    Qed.

  End Confluence.

  (*! Modular [ugraph] and its local-complete evaluation and confluence *)
  Section Modular.
    Definition flatten (ugs: list ugraph): ugraph := concat ugs.

    (** Modular version of [EvalUGraphTrs], dealing with multiple [ugraph]s *)
    Definition EvalUGraphTrsM (ugs: list ugraph) (st: State) (nugs: list ugraph) (nst: State): Prop :=
      EvalUGraphTrs (flatten ugs) st (flatten nugs) nst.

    (** Modular version with a constraint that each local evaluation is always complete *)
    Inductive EvalUGraphTrsMC: list ugraph -> State -> list ugraph -> State -> Prop :=
    | EvalUGraphIdMC:
      forall ugs1 ugs2,
        flatten ugs1 = flatten ugs2 ->
        forall st, EvalUGraphTrsMC ugs1 st ugs2 st
    | EvalUGraphStepMC:
      forall ugs ugs1 ug ugs2,
        ugs = ugs1 ++ ug :: ugs2 ->
        forall nug nugs,
          nugs = ugs1 ++ nug :: ugs2 ->
          forall st nst,
            EvalUGraphTrs (flatten ugs) st (flatten nugs) nst ->
            (* Below is the constraint added *)
            UGraphUpdCompl nug -> UGraphUpdFull nug ->
            EvalUGraphTrsMC ugs st nugs nst.

    Lemma EvalUGraphTrsMC_EvalUGraphTrs:
      forall iugs ist nugs nst,
        EvalUGraphTrsMC iugs ist nugs nst ->
        EvalUGraphTrs (flatten iugs) ist (flatten nugs) nst.
    Proof using .
      induction 1; simpl; intros.
      - rewrite H3; constructor.
      - assumption.
    Qed.

    (** Initial conditions: all proven statically (syntactically) by the given processes. *)
    Variables (iugs: list ugraph) (vs: list vid_t) (ist: State).
    Hypotheses (Hugu: UGraphUnique (flatten iugs))
      (Hugk: UGraphKeysOk (flatten iugs))
      (Hugf: UGraphUpdfOk (flatten iugs))
      (Hugfs: UpdfSub (flatten iugs) ist)
      (Hugwf: UGraphStWf ist (flatten iugs))
      (Hkwf: HMapStrKeysWf ist vs).

    (** Confluence is obtained almost for free! *)
    Theorem EvalUGraphTrsMC_EvalUGraphTrsM_confl:
      forall mnugs mnst,
        EvalUGraphTrsM iugs ist mnugs mnst ->
        UGraphUpdCompl (flatten mnugs) -> UGraphUpdFull (flatten mnugs) ->
        forall cnugs cnst,
          EvalUGraphTrsMC iugs ist cnugs cnst ->
          UGraphUpdCompl (flatten cnugs) -> UGraphUpdFull (flatten cnugs) ->
          mnst = cnst.
    Proof using All.
      unfold EvalUGraphTrsM; intros.
      apply EvalUGraphTrsMC_EvalUGraphTrs in H6.
      eapply eval_ugraph_confl_state_eq with (ug0:= flatten iugs) (st0:= ist); try eassumption.
      all: repeat split; eassumption.
    Qed.

  End Modular.

End UGraph.
