Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.PeanoNat Coq.micromega.Lia.
Require Import Lib.Lib Standard UpdGraph RankedGraph ResetGraph StdProgress.

Set Implicit Arguments.

Section WeightedRank.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Lemma edge_rank: forall rank ug parent child,
    RankedGraph rank ug -> UGraphUnique ug -> In parent ug -> In child ug ->
    hasEdge parent child = true -> nodeRank rank parent < nodeRank rank child.
  Proof.
    intros rank ug parent child Hr Hu Hp Hc He.
    unfold hasEdge in He; apply existsb_exists in He.
    destruct He as [dep [Hd He]]; apply existsb_exists in He.
    destruct He as [key [Hk He]]; apply vid_eqb_eq in He; subst key.
    destruct (Hr child Hc dep Hd) as [owner [Ho [Hok Hlt]]].
    pose proof (UGraphUnique_getNode Hu) as Hfind; rewrite Forall_forall in Hfind.
    pose proof (Hfind parent Hp dep Hk); pose proof (Hfind owner Ho dep Hok).
    assert (parent = owner) by congruence; subst parent; exact Hlt.
  Qed.

  Definition rankCost (rank: vid_t -> nat) (ug: ugraph) (key: vid_t): nat :=
    (2 * length ug + 1) ^ (S (graphHeight rank ug) - rank key).

  Lemma broadcast_bound: forall cost parent nodes bound,
    (forall child, In child nodes -> hasEdge parent child = true ->
      nodeCost cost child <= bound) ->
    broadcastCost cost parent nodes <= length nodes * (2 * bound).
  Proof.
    intros cost parent nodes; induction nodes; intros bound Hb; [simpl; lia|].
    assert (Htail: broadcastCost cost parent nodes <= length nodes * (2 * bound)).
    { apply IHnodes; intros child Hin; apply Hb; right; exact Hin. }
    simpl; destruct (hasEdge parent a) eqn:He; [|lia].
    specialize (Hb a (or_introl eq_refl) He); lia.
  Qed.

  Theorem ranked_schedule: forall rank ug,
    RankedGraph rank ug -> UGraphUnique ug -> ScheduleCosts (rankCost rank ug) ug.
  Proof.
    intros rank ug Hr Hu; apply Forall_forall; intros parent Hp.
    destruct (keys parent) as [|key rest] eqn:Hkeys.
    - assert (Hz: broadcastCost (rankCost rank ug) parent ug = 0).
      { assert (Hnone: forall nodes, broadcastCost (rankCost rank ug) parent nodes = 0).
        { intros nodes; induction nodes as [|child tail IH]; [reflexivity|].
          simpl; unfold hasEdge; rewrite Hkeys; simpl.
          assert (He: existsb (fun _ : vid_t => false) (deps child) = false).
          { induction (deps child); simpl; congruence. }
          rewrite He; simpl; exact IH. }
        apply Hnone. }
      unfold nodeCost; rewrite Hkeys, Hz; lia.
    - set (base := 2 * length ug + 1).
      set (height := S (graphHeight rank ug)).
      set (exponent := height - rank key - 1).
      assert (Hparent: rank key < height).
      { pose proof (rank_bounded rank ug parent Hp); unfold nodeRank in *;
          rewrite Hkeys in *; unfold height; lia. }
      assert (Hb: broadcastCost (rankCost rank ug) parent ug <= length ug * (2 * base ^ exponent)).
      { apply broadcast_bound; intros child Hc He.
        pose proof (edge_rank parent child Hr Hu Hp Hc He) as Hlt.
        unfold nodeRank in Hlt; rewrite Hkeys in Hlt.
        unfold nodeCost, rankCost; destruct (keys child) as [|ck cr]; [lia|].
        apply Nat.pow_le_mono_r; [unfold base; lia|].
        unfold exponent, height; lia. }
      unfold nodeCost; rewrite Hkeys; unfold rankCost; fold base height.
      assert (Hex: height - rank key = S exponent) by (unfold exponent; lia).
      rewrite Hex, Nat.pow_succ_r by lia.
      assert (Hpos: 0 < base ^ exponent) by (assert (base ^ exponent <> 0) by (apply Nat.pow_nonzero; unfold base; lia); lia).
      change (broadcastCost (rankCost rank ug) parent ug < base * base ^ exponent).
      assert (Hbase: base = 2 * length ug + 1) by reflexivity; nia.
  Qed.
End WeightedRank.
