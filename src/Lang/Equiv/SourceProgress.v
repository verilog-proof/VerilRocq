Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.Wf_nat Coq.micromega.Lia.
Require Import Lib.Lib Lang.Semantics Standard UpdGraph ProcUpdGraph RankedGraph TrsProc StfUpdGraph.

Set Implicit Arguments.

Section SourceProgress.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition unseen (ug: ugraph): nat :=
    length (filter (fun un => negb (updOnce un)) ug).

  Lemma unseen_monotone: forall ug next,
    UGraphUpdOnceMono ug next -> unseen next <= unseen ug.
  Proof.
    induction 1; [reflexivity|].
    destruct H3 as [_ Hmono]; unfold unseen in *; simpl.
    destruct (updOnce x) eqn:Hx, (updOnce y) eqn:Hy; simpl in *; try lia.
  Qed.

  Lemma unseen_step: forall ug s next s',
    UGraphUpdFull ug -> EvalUGraph ug s next s' -> unseen next < unseen ug.
  Proof.
    intros ug s next s' Hfull Hstep; destruct Hstep; subst.
    unfold UGraphUpdFull in Hfull; rewrite Forall_app in Hfull.
    destruct Hfull as [_ Hfull]; inversion Hfull; subst.
    assert (Honce: updOnce un = false) by congruence.
    unfold unseen; rewrite !filter_app, !length_app; simpl; rewrite Honce; simpl; lia.
  Qed.

  Lemma source_trace_progress: forall ug s next s',
    UGraphUpdFull ug -> EvalUGraphTrs ug s next s' ->
    s' = s \/ unseen next < unseen ug.
  Proof.
    intros ug s next s' Hfull Hrun; destruct Hrun.
    - left; reflexivity.
    - right; pose proof (unseen_step Hfull H3) as Hlt.
      pose proof (unseen_monotone (EvalUGraphTrs_updOnce_mono Hrun)) as Hle; lia.
  Qed.

  Lemma source_graph_full: forall s ug,
    UGraphSt s ug -> UGraphUpdFull ug.
  Proof.
    intros s ug Hstate; unfold UGraphSt in Hstate; unfold UGraphUpdFull.
    rewrite Forall_forall in *; intros un Hin; exact (proj1 (Hstate un Hin)).
  Qed.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Theorem source_progress: forall procs P ug s,
    UGraphSource decls funcs mtrss ug procs -> UGraphSt s ug ->
    UGraphUnique ug -> UGraphKeysOk ug -> UGraphDepsOk ug ->
    GraphDomain ug P -> P s -> UpdfSub ug s -> HMapStrEmptyWf s ->
    exists final flops, TrsProcsRep decls funcs mtrss procs s final flops.
  Proof.
    intros procs P.
    assert (Hbounded: forall n ug, unseen ug = n -> forall s,
      UGraphSource decls funcs mtrss ug procs -> UGraphSt s ug ->
      UGraphUnique ug -> UGraphKeysOk ug -> UGraphDepsOk ug ->
      GraphDomain ug P -> P s -> UpdfSub ug s -> HMapStrEmptyWf s ->
      exists final flops, TrsProcsRep decls funcs mtrss procs s final flops).
    { induction n using lt_wf_ind; intros ug Hn s Hsource Hstate Hu Hk Hd Hdomain HP Hsub Hwf.
      destruct (trsProcs decls funcs mtrss procs (s,HMapEmpty))
        as [[nextState nextFlops]|err] eqn:Hsweep.
      - destruct (trsProcs_imp_EvalUGraphTrs_ind (decls := decls) (funcs := funcs) (mtrss := mtrss)
          (P := P) (gprocs := procs) procs ltac:(exists nil; reflexivity)
          Hwf HMapEmpty Hsweep HP Hsub Hk Hdomain Hd Hu Hsource Hstate)
          as [next [Htrace [Hdn [Hun [Hsn [Hstn Hwfn]]]]]].
        destruct (source_trace_progress (source_graph_full Hstate) Htrace) as [Heq|Hlt].
        + subst nextState; exists s, nextFlops; apply TrsProcsFix; exact Hsweep.
        + destruct (graph_domain_trace Hdomain Htrace (SameGraph_refl ug)
            Hu Hk HP Hsub) as [HPn Hsubn].
          assert (Hkn: UGraphKeysOk next) by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
          assert (Hdomainn: GraphDomain next P).
          { eapply SameGraph_domain; [eapply EvalUGraphTrs_same; exact Htrace|exact Hdomain]. }
          destruct (H3 (unseen next) ltac:(rewrite <-Hn; exact Hlt) next eq_refl
            nextState Hsn Hstn Hun Hkn Hdn Hdomainn HPn Hsubn Hwfn)
            as [final [flops Hrep]].
          exists final, flops; eapply TrsProcsNext; eassumption.
      - exfalso; eapply trsProcs_never_fails; exact Hsweep. }
    intros ug s; eapply Hbounded; reflexivity.
  Qed.
End SourceProgress.
