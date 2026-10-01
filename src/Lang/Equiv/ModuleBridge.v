Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Syntax Lang.Semantics Standard TrsProc.
Include SFMonadNotations.

Set Implicit Arguments.

Section ModuleBridge.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.
  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  (** This syntactic fragment has the same item boundaries in the module
      evaluator and the process extractor. Parameters and conditional generate
      blocks require elaboration before using this bridge. *)
  Inductive FlatCommon : @VModuleCommonItem vid_t -> Prop :=
  | FlatAlways kw stmt: FlatCommon (VModuleCommonItemAlways kw (VStatementO stmt))
  | FlatAssign vid expr: FlatCommon
      (VModuleCommonItemContAssign (VContAssignNet (VAssignsOne (VAssignO (VExprId vid) expr))))
  | FlatNet nt pd vid: FlatCommon
      (VModuleCommonItemDecl (VModuleGenItemDeclPkg
        (VPkgGenItemDeclNet (VNetDeclOne nt pd (VNetDeclAssignsOne (VNetDeclAssignOne vid None))))))
  | FlatVar dt vid dims: FlatCommon
      (VModuleCommonItemDecl (VModuleGenItemDeclPkg
        (VPkgGenItemDeclData (VDataDeclVarDecl
          (VVarDeclOne dt (VVarDeclAssignsOne (VVarDeclAssignVar vid dims None)))))))
  | FlatAssert assertion: FlatCommon (VModuleCommonItemAssert assertion).

  Inductive FlatItem : @VModuleItem vid_t -> Prop :=
  | FlatPort port: FlatItem (VModuleItemPortDecl port)
  | FlatCommonItem item: FlatCommon item -> FlatItem
      (VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemCommon item)))
  | FlatInstance inst: FlatItem
      (VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemIns inst))).

  Fixpoint FlatItems (items: @VModuleItems vid_t): Prop :=
    match items with
    | VModuleItemsOne item => FlatItem item
    | VModuleItemsCons item rest => FlatItem item /\ FlatItems rest
    end.

  Definition FlatModule (m: @VModuleDecl vid_t): Prop :=
    match m with
    | VModuleDeclAnsi _ params _ items => params = VParamPortsNil /\ FlatItems items
    end.

  Lemma iffupds_empty: forall iff,
    iffupds iff (HMapEmpty, HMapEmpty) = iff.
  Proof. intros [s f]; unfold iffupds; simpl; rewrite !hmergeR_empty; reflexivity. Qed.

  Lemma flat_common_sweep: forall item,
    FlatCommon item -> forall iff,
    trsVModuleItem decls funcs HMapEmpty mtrss
      (VModuleItemNonPort (VNonPortModuleOrGenerateItem (VModuleOrGenerateItemCommon item))) iff =
    trsProcs decls funcs mtrss (getProcsModuleCommonItem decls [] item) iff.
  Proof.
    intros item Hflat [s f]; destruct Hflat.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        trsVModuleCommonItem getProcsModuleCommonItem trsProcs trsProc execEvalEvent proc_pos proc_evu fst snd].
      destruct (trsVStatementItem decls funcs HMapEmpty [] s
        (match kw with VAlwaysComb => true | _ => false end) stmt HMapEmpty)
        as [[[a n] v]|err]; [reflexivity|].
      rewrite iffupds_empty; reflexivity.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        trsVModuleCommonItem trsVContAssign trsVAssigns trsVAssign
        getProcsModuleCommonItem getProcsAssigns getProcsAssign trsProcs trsProc execEvalEvent
        lvposfind proc_pos proc_evu fst snd].
      unfold declfind.
      destruct (hpos [] vid decls) as [path|] eqn:Hpath; simpl.
      + unfold ctxEval, ctxfind.
        rewrite hfind_empty by (eapply hpos_not_nil; exact Hpath).
        destruct (evalExpr decls funcs [] s HMapEmpty expr) as [v|err]; simpl;
          [reflexivity|rewrite iffupds_empty; reflexivity].
      + rewrite iffupds_empty; reflexivity.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        trsVModuleCommonItem trsVPkgGenItemDecl trsVNetDeclAssigns trsVNetDeclAssign
        getProcsModuleCommonItem getProcsPkgGenItemDecl getProcsNetDeclAssigns getProcsNetDeclAssign
        trsProcs]. rewrite iffupds_empty; reflexivity.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        trsVModuleCommonItem trsVPkgGenItemDecl trsVVarDeclAssigns trsVVarDeclAssign
        getProcsModuleCommonItem getProcsPkgGenItemDecl getProcsVarDeclAssigns getProcsVarDeclAssign
        trsProcs]. rewrite iffupds_empty; reflexivity.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        trsVModuleCommonItem getProcsModuleCommonItem trsProcs].
      rewrite iffupds_empty; reflexivity.
  Qed.

  Lemma flat_item_sweep: forall item,
    FlatItem item -> forall iff,
    trsVModuleItem decls funcs HMapEmpty mtrss item iff =
    trsProcs decls funcs mtrss (getProcsModuleItem decls mtrss item) iff.
  Proof.
    intros item Hflat iff; destruct Hflat.
    - reflexivity.
    - apply flat_common_sweep; assumption.
    - cbn [trsVModuleItem trsVNonPortModuleItem trsVModuleOrGenerateItem
        getProcsModuleItem getProcsNonPortModuleItem getProcsMGenItem
        trsProcs trsProc execEvalEvent proc_pos proc_evu fst snd].
      destruct (trsVModuleIns decls funcs HMapEmpty [] (fst iff) mtrss inst);
        [reflexivity|rewrite iffupds_empty; reflexivity].
  Qed.

  Lemma flat_items_sweep: forall items,
    FlatItems items -> forall iff,
    trsVModuleItems decls funcs HMapEmpty mtrss items iff =
    trsProcs decls funcs mtrss (getProcsModuleItems decls mtrss items) iff.
  Proof.
    induction items as [item|item items IHitems]; intros Hflat iff; simpl in *.
    - apply flat_item_sweep; assumption.
    - destruct Hflat as [Hi Hrest]. rewrite trsProcs_app, flat_item_sweep by exact Hi.
      destruct (trsProcs decls funcs mtrss (getProcsModuleItem decls mtrss item) iff);
        apply IHitems; exact Hrest.
  Qed.

  Theorem flat_module_sweep: forall m,
    FlatModule m -> forall s,
    trsVModuleDecl decls funcs HMapEmpty mtrss m s =
    trsProcs decls funcs mtrss (getProcs decls mtrss m) (s,HMapEmpty).
  Proof.
    intros [name params ports items] [Hp Hi] s; subst params.
    cbn [trsVModuleDecl trsVParamPorts getProcs getProcsParamPorts trsProcs
      getProcInputClk trsProc execEvalEvent proc_pos proc_evu fst snd].
    rewrite !iffupds_empty. apply flat_items_sweep; exact Hi.
  Qed.

  (** A source sweep fixes the wire state first. One more sweep fixes the pair
      of wires and computed flop updates used by the executable evaluator. *)
  Theorem flat_module_lfp: forall m,
    FlatModule m -> forall seed final flops,
    TrsProcsRep decls funcs mtrss (getProcs decls mtrss m) seed final flops <->
    LFP (seed,HMapEmpty) (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) (final,flops).
  Proof.
    intros m Hflat seed final flops; split.
    - assert (Hprepend: forall start mid finish,
        trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m start = Sret mid ->
        chain mid (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) finish ->
        chain start (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) finish).
      { intros start mid finish Hstep Hchain; induction Hchain.
        - eapply chain_step; [constructor|exact Hstep].
        - eapply chain_step; eassumption. }
      assert (Hforward: forall s t f,
        TrsProcsRep decls funcs mtrss (getProcs decls mtrss m) s t f -> forall initialFlops,
        LFP (s,initialFlops) (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) (t,f)).
      { intros s t f Hr; induction Hr as [s1 sf f Hr IH s0 f1 Hstep|s f Hfix]; intros initialFlops.
        - destruct (IH f1) as [Hchain Hfix]. split; [|exact Hfix].
          eapply Hprepend; [|exact Hchain].
          unfold trsVModuleDecl_IFF; rewrite flat_module_sweep by exact Hflat; exact Hstep.
        - assert (Hstep: forall old,
            trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m (s,old) = Sret (s,f)).
          { intros old; unfold trsVModuleDecl_IFF; rewrite flat_module_sweep by exact Hflat; exact Hfix. }
          split; [eapply chain_step; [constructor|apply Hstep]|apply Hstep]. }
      intros Hr; apply Hforward; exact Hr.
    - intros [Hchain Hfix].
      assert (Hback: forall start finish,
        chain start (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) finish ->
        forall out, TrsProcsRep decls funcs mtrss (getProcs decls mtrss m)
          (fst finish) final out ->
        TrsProcsRep decls funcs mtrss (getProcs decls mtrss m) (fst start) final out).
      { intros start finish Hc; induction Hc; intros out Hr; [exact Hr|].
        apply IHHc. destruct h as [s f], h' as [s' f']; simpl in *.
        eapply TrsProcsNext; [exact Hr|].
        rewrite <-flat_module_sweep by exact Hflat; exact H3. }
      apply (Hback (seed,HMapEmpty) (final,flops) Hchain flops).
      apply TrsProcsFix. rewrite <-flat_module_sweep by exact Hflat; exact Hfix.
  Qed.

  Lemma module_chain_rep: forall m seed final,
    chain seed (trsVModuleDecl_IFF decls funcs HMapEmpty mtrss m) final ->
    exists n, trsM_iff_rep decls funcs HMapEmpty mtrss m seed n = Sret final.
  Proof.
    intros m seed final Hchain; induction Hchain.
    - exists 0; reflexivity.
    - destruct IHHchain as [n Hrep]. exists (S n); simpl; rewrite Hrep; assumption.
  Qed.

  Theorem flat_module_rep: forall m,
    FlatModule m -> forall seed final flops,
    TrsProcsRep decls funcs mtrss (getProcs decls mtrss m) seed final flops <->
    exists n,
      trsM_iff_rep decls funcs HMapEmpty mtrss m (seed,HMapEmpty) n = Sret (final,flops) /\
      trsVModuleDecl decls funcs HMapEmpty mtrss m final = Sret (final,flops).
  Proof.
    intros m Hflat seed final flops; rewrite flat_module_lfp by exact Hflat.
    split.
    - intros [Hchain Hfix]; destruct (module_chain_rep Hchain) as [n Hrep]; exists n; auto.
    - intros [n [Hrep Hfix]]; split; [eapply trsM_iff_rep_is_chain; exact Hrep|exact Hfix].
  Qed.
End ModuleBridge.
