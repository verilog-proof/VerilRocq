Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard UpdGraph ProcUpdGraph RankedGraph ResetGraph StdProgress TrsProc.

Set Implicit Arguments.

Section GraphStructure.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition SameWiring (ug next: ugraph): Prop :=
    Forall2 (fun un un' => keys un = keys un' /\ deps un = deps un') ug next.

  Lemma same_wiring: forall ug next, SameGraph ug next -> SameWiring ug next.
  Proof. induction 1; constructor; [destruct H3 as [? [? ?]]; split; assumption|assumption]. Qed.

  Lemma wiring_sym: forall ug next, SameWiring ug next -> SameWiring next ug.
  Proof. induction 1; constructor; [destruct H3; split; congruence|assumption]. Qed.

  Lemma wiring_unique: forall ug next,
    SameWiring ug next -> UGraphUnique ug -> UGraphUnique next.
  Proof.
    intros ug next Hw Hu; eapply UGraphUnique_keys_equiv; [exact Hu|].
    clear Hu; induction Hw; [reflexivity|].
    destruct H3 as [Hk _]; simpl; rewrite Hk, IHHw; reflexivity.
  Qed.

  Lemma wiring_present: forall ug next,
    SameWiring ug next -> forall s, UGraphStWf s ug -> UGraphStWf s next.
  Proof.
    induction 1; intros s Hp; inversion Hp; subst; constructor.
    - destruct H3 as [Hkeys _]; unfold UNodeStWf in *; rewrite <-Hkeys; assumption.
    - apply IHForall2; assumption.
  Qed.

  Lemma wiring_covered: forall ug next,
    SameWiring ug next -> forall key,
    (exists un, In un ug /\ In key (keys un)) ->
    exists un, In un next /\ In key (keys un).
  Proof.
    intros ug next Hw key [un [Hin Hkey]].
    eapply Forall2_In_left in Hw; [|exact Hin].
    destruct Hw as [un' [Hin' [Hkeys _]]].
    exists un'; split; [exact Hin'|rewrite <-Hkeys; exact Hkey].
  Qed.

  Lemma same_keys_ok: forall ug next,
    SameGraph ug next -> UGraphKeysOk ug -> UGraphKeysOk next.
  Proof.
    induction 1; intros Hk; inversion Hk; subst; constructor.
    - destruct H3 as [Hkeys [_ Hfun]]; unfold UNodeKeysOk in *; rewrite <-Hkeys, <-Hfun; assumption.
    - apply IHForall2; assumption.
  Qed.

  Lemma same_const: forall ug next,
    SameGraph ug next -> Forall UNodeUpdfConst ug -> Forall UNodeUpdfConst next.
  Proof.
    induction 1; intros Hk; inversion Hk; subst; constructor.
    - destruct H3 as [_ [Hd Hf]]; unfold UNodeUpdfConst in *; rewrite <-Hd, <-Hf; assumption.
    - apply IHForall2; assumption.
  Qed.

  Lemma ranked_deps: forall rank ug,
    RankedGraph rank ug -> UGraphUnique ug -> UGraphDepsOk ug.
  Proof.
    intros rank ug Hr Hu; apply Forall_forall; intros un Hin.
    apply Forall_forall; intros dep Hd.
    destruct (ranked_parent un dep Hr Hu Hin Hd) as [parent [Hfind _]]; congruence.
  Qed.

  Lemma domain_const: forall ug P s,
    GraphDomain ug P -> P s -> Forall UNodeUpdfConst ug.
  Proof.
    intros ug P s [Hat _] HP; specialize (Hat s HP).
    eapply Forall_impl; [|exact Hat]; intros un [_ Hc]; exact Hc.
  Qed.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Lemma same_std: forall ug next,
    SameGraph ug next -> forall procs,
    UGraphStd decls funcs mtrss ug procs -> UGraphStd decls funcs mtrss next procs.
  Proof.
    induction 1; intros procs Hstd; inversion Hstd; subst; constructor.
    - destruct H3 as [Hk [Hd Hf]]; unfold UNodeStd in *.
      unfold UNodeKeysOk in *; rewrite <-Hk, <-Hd, <-Hf; assumption.
    - apply IHForall2; assumption.
  Qed.

  Definition CompleteDomain (ug: ugraph) (P: State -> Prop) (s: State): Prop :=
    P s /\ UGraphStWf s ug /\ exists schema, HMapStrKeysWf s schema.

  Lemma complete_domain: forall ug P,
    UGraphKeysOk ug -> GraphDomain ug P -> GraphDomain ug (CompleteDomain ug P).
  Proof.
    intros ug P Hk [Hat Hpres]; split.
    - intros s [HP _]; apply Hat; exact HP.
    - intros current s next s' Hsame [HP [Hp [schema Hshape]]] Hstep.
      split; [eapply Hpres; eassumption|].
      assert (Hkc: UGraphKeysOk current) by (eapply same_keys_ok; eassumption).
      assert (Hpc: UGraphStWf s current) by (eapply wiring_present; [apply same_wiring; exact Hsame|exact Hp]).
      destruct (EvalUGraph_UGraphStWf_KeysWf Hkc schema Hshape Hpc Hstep) as [Hpn Hshn].
      split; [|exists schema; exact Hshn].
      eapply wiring_present; [apply wiring_sym; apply same_wiring;
        eapply SameGraph_trans; [exact Hsame|eapply EvalUGraph_same; exact Hstep]|exact Hpn].
  Qed.

  Lemma complete_process_progress: forall rank ug P procs,
    RankedGraph rank ug -> UGraphStd decls funcs mtrss ug procs ->
    Forall (fun proc => trig_stv (proc_trig proc) = [] \/
      ProcSourceWf decls funcs mtrss proc) procs ->
    ProcessProgress decls funcs mtrss (CompleteDomain ug P) procs.
  Proof.
    intros rank ug P procs Hr Hstd Hlocal proc Hin Hsens s [_ [Hp _]].
    pose proof (Forall_In Hlocal proc Hin) as Hproc; destruct Hproc as [Hnil|[_ Hsucc]]; [contradiction|].
    pose proof (Forall2_In_right Hstd proc Hin) as [un [Hun [_ [_ [Hd _]]]]].
    specialize (Hsucc s); destruct (trsProc decls funcs mtrss proc s) as [[a n]|err] eqn:Hex.
    - exists a,n; split; [reflexivity|exact (proj1 Hsucc)].
    - destruct Hsucc as [dep [Hdep Hnone]]; rewrite <-Hd in Hdep.
      destruct (Hr un Hun dep Hdep) as [parent [Hpar [Hkey _]]].
      pose proof (Forall_In Hp parent Hpar) as Hpresent; specialize (Hpresent dep Hkey); contradiction.
  Qed.
End GraphStructure.
