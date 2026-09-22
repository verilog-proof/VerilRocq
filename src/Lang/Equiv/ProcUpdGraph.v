Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics.

Require Import UpdGraph Standard TrsProc.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section ProcUpdGraph.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition getWritesEvalUnit (initWrites: list vid_t) (cpos: hpath) (evu: EvalUnit): list vid_t :=
    match evu with
    | EvalUnitAlways isComb stmt =>
        if isComb
        then getSLStatementWrites decls cpos stmt
        else initWrites
    | EvalUnitAssign lv e => getSLExpr decls cpos lv
    | EvalUnitModuleIns mins => getWritesModuleIns decls mtrss cpos mins
    | EvalUnitInputClk => initWrites
    end.

  Definition isInit (init: InitState): bool :=
    match init with
    | nil => false
    | _ => true
    end.

  Definition IPS := list (InitState * Process).

  (** [Inject] supplies new boundary values; [Hold] retains existing ones.
   * [Compute] evaluates a process. Its [valid] flag records whether the stored
   * values agree with its current dependencies. Old values may still be
   * present when [valid = false]. *)
  Inductive NodeRole :=
  | Inject (bindings: InitState)
  | Hold (bindings: InitState)
  | Compute (writes: list vid_t) (valid: bool).

  Definition getUNode (role: NodeRole) (proc: Process): unode :=
    match role with
    | Inject bindings =>
        {| keys := List.map fst bindings; deps := nil;
           updOnce := negb (isInit bindings); updDone := negb (isInit bindings);
           updf := fun _ => HMapStr bindings |}
    | Hold bindings =>
        {| keys := List.map fst bindings; deps := nil;
           updOnce := true; updDone := true;
           updf := fun _ => HMapStr bindings |}
    | Compute writes valid =>
        {| keys := writes; deps := trig_stv (proc_trig proc);
           updOnce := valid; updDone := valid;
           updf := fun st => match trsProc decls funcs mtrss proc st with
                            | Sret u => fst u
                            | Fail _ => HMapEmpty
                            end |}
    end.

  Definition roleEvent (role: NodeRole): option Event :=
    match role with
    | Inject (binding :: bindings) => Some (EventUpd (HMapStr (binding :: bindings)))
    | _ => None
    end.

  Definition RoleSlots := list (NodeRole * Process).
  Definition getUGraph (slots: RoleSlots): ugraph :=
    List.map (fun slot => getUNode (fst slot) (snd slot)) slots.
  Definition roleEvents (slots: RoleSlots): Region :=
    List.map (fun slot => roleEvent (fst slot)) slots.

  (** A process triggered by an update computes this node's update function.
   * Boundary nodes have empty sensitivity lists and constant update functions. *)
  Definition UNodeStd (un: unode) (proc: Process): Prop :=
    UNodeKeysOk un /\
      (forall upd, HMapStrEmpty upd -> genEvalEvent (EventUpd upd) proc = None ->
         forall st, updf un (hupds st upd) = updf un st) /\
      deps un = trig_stv (proc_trig proc) /\
      (forall upd ev, genEvalEvent (EventUpd upd) proc = Some ev ->
         forall st, updf un st = match trsProc decls funcs mtrss proc st with
                                | Sret u => fst u | Fail _ => HMapEmpty end).

  Definition UGraphStd (ug: ugraph) (procs: Processes): Prop :=
    Forall2 UNodeStd ug procs.

  Lemma UGraphStd_upd: forall ug1 un ug2 procs,
    UGraphStd (ug1 ++ un :: ug2) procs -> forall once done_,
    UGraphStd (ug1 ++ {| keys := keys un; deps := deps un;
      updOnce := once; updDone := done_; updf := updf un |} :: ug2) procs.
  Proof.
    intros ug1 un ug2 procs Hrel once done_.
    apply Forall2_app_inv_l in Hrel.
    destruct Hrel as [ps1 [ps2 [Hleft [Hright Heq]]]]; subst procs.
    inversion Hright; subst.
    apply Forall2_app; [exact Hleft|].
    constructor; assumption.
  Qed.

  Lemma boundary_role_std: forall bindings proc,
    trig_stv (proc_trig proc) = nil ->
    UNodeStd (getUNode (Inject bindings) proc) proc /\
    UNodeStd (getUNode (Hold bindings) proc) proc.
  Proof.
    intros bindings proc Htrig.
    assert (Hnone: forall upd, genEvalEvent (EventUpd upd) proc = None).
    { intros upd; unfold genEvalEvent; rewrite Htrig; reflexivity. }
    assert (Hconst: forall once done_, UNodeStd
      {| keys := List.map fst bindings; deps := nil;
         updOnce := once; updDone := done_; updf := fun _ => HMapStr bindings |} proc).
    { intros once done_; unfold UNodeStd; split.
      - intros st; right; exists bindings; split; reflexivity.
      - split; [intros; reflexivity|].
        split; [symmetry; exact Htrig|].
        intros upd ev Hgen; rewrite Hnone in Hgen; discriminate. }
    split; apply Hconst.
  Qed.

  Lemma hfind_hupds_absent: forall upd,
    HMapStrEmpty upd -> forall key,
    hfind [HEltVid key] upd = None -> forall st,
    hfind [HEltVid key] (hupds st upd) = hfind [HEltVid key] st.
  Proof.
    intros upd Hmap key Hnone st; destruct upd; try contradiction.
    - rewrite hupds_empty; reflexivity.
    - assert (Hout: ~ In key (List.map fst str)).
      { intros Hin; apply haccessV_Some in Hin; simpl in Hnone.
        destruct (haccessV str key); [discriminate|contradiction]. }
      destruct st; simpl; try reflexivity; try exact Hnone.
      rewrite <-haccessV_hbinUStr_no_effect by exact Hout; reflexivity.
  Qed.

  Lemma compute_role_std: forall writes valid proc,
    UNodeKeysOk (getUNode (Compute writes valid) proc) ->
    UNodeUpdfConst (getUNode (Compute writes valid) proc) ->
    UNodeStd (getUNode (Compute writes valid) proc) proc.
  Proof.
    intros writes valid proc Hkeys Hconst; split; [exact Hkeys|].
    split.
    - intros upd Hmap Hnone st; apply Hconst.
      intros key Hin; apply genEvalEvent_None in Hnone.
      eapply Forall_In in Hnone; [|exact Hin].
      destruct (hfind [HEltVid key] upd) eqn:Hfind; [contradiction|].
      apply hfind_hupds_absent; assumption.
    - split; [reflexivity|intros; reflexivity].
  Qed.

  Definition initState (ips: IPS): IFW :=
    HMapStr (List.concat (List.map fst ips)).

  (*! Well-formedness of processes *)

  Definition ProcWfExecUniq (proc: Process): Prop :=
    forall s, match trsProc decls funcs mtrss proc s with
              | Sret u => HMapStrEmptyWf (fst u)
              | Fail _ => True
              end.

  Definition ProcWfExecSucc (proc: Process): Prop :=
    forall s,
      match trsProc decls funcs mtrss proc s with
      | Sret u => fst u <> [] /\ Forall (fun v => hfind [HEltVid v] s <> None) (trig_stv (proc_trig proc))
      | Fail _ => exists v, In v (trig_stv (proc_trig proc)) /\ hfind [HEltVid v] s = None
      end.

  (*! Well-formedness of ugraphs wrt. associated processes *)

  Definition UNodeCompute (un: unode) (proc: Process): Prop :=
    UNodeKeysOk un /\
      keys un <> nil /\
      deps un = trig_stv (proc_trig proc) /\
      (forall st, updf un st = match trsProc decls funcs mtrss proc st with
                               | Sret u => fst u
                               | Fail _ => []
                               end).

  Definition ProcSourceWf (proc: Process): Prop :=
    ProcWfExecUniq proc /\ ProcWfExecSucc proc.

  (** Source sweeps evaluate clocked blocks to collect next-flop outputs, but
   * these blocks and the input placeholder do not update the active state.
   * Their boundary values are already supplied by [initState]. *)
  Definition UNodeSource (un: unode) (proc: Process): Prop :=
    (UNodeCompute un proc /\ ProcSourceWf proc) \/
    (updOnce un = true /\ updDone un = true /\
      forall st u, trsProc decls funcs mtrss proc st = Sret u -> fst u = HMapEmpty).

  Definition UGraphSource (ug: ugraph) (procs: Processes): Prop :=
    Forall2 UNodeSource ug procs.

  Lemma UGraphSource_upd: forall ug1 un ug2 procs,
    UGraphSource (ug1 ++ un :: ug2) procs ->
    UGraphSource (ug1 ++ {| keys := keys un; deps := deps un;
      updOnce := true; updDone := true; updf := updf un |} :: ug2) procs.
  Proof.
    intros ug1 un ug2 procs Hrel.
    apply Forall2_app_inv_l in Hrel.
    destruct Hrel as [ps1 [ps2 [Hleft [Hright Heq]]]]; subst procs.
    inversion Hright; subst.
    apply Forall2_app; [exact Hleft|].
    constructor; [|assumption].
    match goal with Hnode: UNodeSource _ _ |- _ =>
      destruct Hnode as [[Hnode Hwf] | [_ [_ Hempty]]]
    end.
    - left; split; assumption.
    - right; split; [reflexivity|]; split; [reflexivity|exact Hempty].
  Qed.

End ProcUpdGraph.
