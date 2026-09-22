Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.Wf_nat Coq.micromega.Lia.
Require Import Lib.Lib Standard UpdGraph ProcUpdGraph RankedGraph.

Set Implicit Arguments.
Local Open Scope bool_scope.

Section ResetGraph.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition graphHeight (rank: vid_t -> nat) (ug: ugraph): nat :=
    fold_right (fun un n => Nat.max (nodeRank rank un) n) 0 ug.

  Lemma rank_bounded: forall rank ug un,
    In un ug -> nodeRank rank un <= graphHeight rank ug.
  Proof.
    intros rank ug; induction ug; intros un Hin; [contradiction|].
    destruct Hin as [Heq|Hin]; [subst un; simpl; lia|].
    specialize (IHug un Hin); simpl; lia.
  Qed.

  Fixpoint nodeValid (fuel: nat) (base: ugraph) (injected: unode -> bool) (un: unode): bool :=
    match fuel with
    | 0 => true
    | S fuel => negb (injected un) &&
        forallb (fun dep => match getNode base dep with
          | Some parent => nodeValid fuel base injected parent
          | None => false
          end) (deps un)
    end.

  Definition resetNode (fuel: nat) (base: ugraph) (injected: unode -> bool) (un: unode): unode :=
    {| keys := keys un; deps := deps un; updf := updf un;
       updOnce := nodeValid fuel base injected un;
       updDone := nodeValid fuel base injected un |}.

  Definition resetGraph (rank: vid_t -> nat) (base: ugraph) (injected: unode -> bool): ugraph :=
    map (resetNode (S (graphHeight rank base)) base injected) base.

  Lemma forallb_agree: forall (A: Type) (f g: A -> bool) xs,
    (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
  Proof.
    intros A f g xs; induction xs; intros Heq; [reflexivity|].
    simpl; rewrite Heq by (left; reflexivity); rewrite IHxs; [reflexivity|].
    intros x Hin; apply Heq; right; exact Hin.
  Qed.

  Lemma ranked_parent: forall rank base un dep,
    RankedGraph rank base -> UGraphUnique base -> In un base -> In dep (deps un) ->
    exists parent, getNode base dep = Some parent /\ In parent base /\
      nodeRank rank parent < nodeRank rank un.
  Proof.
    intros rank base un dep Hrank Hu Hun Hdep.
    destruct (Hrank un Hun dep Hdep) as (parent & Hp & Hkey & Hlt).
    exists parent; split; [|split; assumption].
    pose proof (UGraphUnique_getNode Hu) as Hfind; rewrite Forall_forall in Hfind.
    apply Hfind; assumption.
  Qed.

  Lemma nodeValid_stable: forall rank base injected,
    RankedGraph rank base -> UGraphUnique base -> forall un,
    In un base -> forall fuel1 fuel2,
    nodeRank rank un < fuel1 -> nodeRank rank un < fuel2 ->
    nodeValid fuel1 base injected un = nodeValid fuel2 base injected un.
  Proof.
    intros rank base injected Hrank Hu.
    assert (Hnode: forall n un, nodeRank rank un = n -> In un base -> forall fuel1 fuel2,
      n < fuel1 -> n < fuel2 -> nodeValid fuel1 base injected un = nodeValid fuel2 base injected un).
    { induction n using lt_wf_ind; intros un Hn Hun fuel1 fuel2 Hf1 Hf2.
      destruct fuel1 as [|f1], fuel2 as [|f2]; try lia.
      simpl; f_equal; apply forallb_agree; intros dep Hdep.
      destruct (ranked_parent un dep Hrank Hu Hun Hdep) as (parent & Hfind & Hp & Hlt).
      rewrite Hfind; eapply H3; [rewrite <-Hn; exact Hlt|reflexivity|exact Hp|lia|lia]. }
    intros un Hun fuel1 fuel2 Hf1 Hf2; eapply Hnode; eassumption || reflexivity.
  Qed.

  Lemma reset_getNode: forall fuel base injected nodes key,
    getNode (map (resetNode fuel base injected) nodes) key =
      option_map (resetNode fuel base injected) (getNode nodes key).
  Proof.
    intros fuel base injected nodes; induction nodes; intros key; [reflexivity|].
    simpl; destruct (existsb (vid_eqb key) (keys a)); [reflexivity|apply IHnodes].
  Qed.

  Lemma reset_deps: forall fuel base injected ds,
    getDepsUpdDone (map (resetNode fuel base injected) base) ds =
      forallb (fun dep => match getNode base dep with
        | Some parent => nodeValid fuel base injected parent | None => false end) ds.
  Proof.
    intros fuel base injected ds; induction ds; [reflexivity|].
    simpl; unfold getUpdDone; rewrite reset_getNode, IHds.
    destruct (getNode base a); reflexivity.
  Qed.

  Lemma reset_valid: forall rank base injected un,
    RankedGraph rank base -> UGraphUnique base -> In un base ->
    updDone (resetNode (S (graphHeight rank base)) base injected un) =
      negb (injected un) && getDepsUpdDone (resetGraph rank base injected) (deps un).
  Proof.
    intros rank base injected un Hrank Hu Hun.
    unfold resetGraph; rewrite reset_deps; simpl; f_equal.
    apply forallb_agree; intros dep Hdep.
    destruct (ranked_parent un dep Hrank Hu Hun Hdep) as (parent & Hfind & Hp & Hlt).
    rewrite Hfind.
    change (nodeValid (graphHeight rank base) base injected parent =
      nodeValid (S (graphHeight rank base)) base injected parent).
    eapply nodeValid_stable; try eassumption.
    - pose proof (rank_bounded rank base un Hun); lia.
    - pose proof (rank_bounded rank base parent Hp); lia.
  Qed.

  Lemma reset_same: forall rank base injected, SameGraph base (resetGraph rank base injected).
  Proof.
    intros rank base injected; unfold resetGraph.
    assert (Hmap: forall nodes, SameGraph nodes
      (map (resetNode (S (graphHeight rank base)) base injected) nodes)).
    { induction nodes; [constructor|].
      constructor; [repeat split; reflexivity|exact IHnodes]. }
    apply Hmap.
  Qed.
End ResetGraph.
