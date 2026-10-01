Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics.

Require Import UpdGraph Standard TrsProc ProcUpdGraph.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section Equivalence.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  (*! Invariants *)

  Definition UNodeEventOk (st: State) (un: unode) (oev: option Event): Prop :=
    match oev with
    | Some EventClkPosedge => False
    | Some (EventUpd upds) => (updf un) st = upds /\ updDone un = false
    | Some (EventEval forActive cpos evu) =>
        (forall st, updf un st = match execEvalEvent decls funcs mtrss st cpos evu with
                                 | Sret u => fst u
                                 | Fail _ => []
                                 end) /\
          updDone un = false
    | _ => True
    end.

  Definition UNodeUpdEvCompl (ug: ugraph) (un: unode) (oev: option Event): Prop :=
    match oev with
    | Some _ => deps un = nil \/ getDepsUpdOnce ug (deps un) = true
    | None => unodeUpdCompl ug un = true
    end.

  (*! Predicates *)

  Definition UGraphEventsStOk (ug: ugraph) (events: Region) (st: State): Prop :=
    Forall2 (fun un oev => UNodeEventOk st un oev /\ UNodeUpdEvCompl ug un oev) ug events.

  Definition UGraphEventsOk (ug: ugraph) (events: Region): Prop :=
    forall st, Forall2 (fun un oev => UNodeEventOk st un oev /\ UNodeUpdEvCompl ug un oev) ug events.

  Definition UGraphUpdComplOk: Prop :=
    forall procs ug st,
      UGraphEventsStOk ug (nilR procs) st ->
      UGraphUpdCompl ug.

  (*! Main proofs *)

  Lemma UGraphUpdOk_upd:
    forall ug1 un (Hun: updDone un = false) ug2,
      UGraphUpdOk (ug1 ++ un :: ug2) ->
      UGraphUpdOk (ug1 ++ {| keys := keys un;
                            deps := deps un;
                            updOnce := true;
                            updDone := getDepsUpdDone (ug1 ++ un :: ug2) (deps un);
                            updf := updf un
                          |} :: ug2).
  Proof using .
    unfold UGraphUpdOk; intros.
    rewrite Forall_forall in H3.
    apply Forall_forall; intros iun; intros.
    apply in_app_or in H4; destruct H4; [|destruct H4; subst].
    - red; intros.
      rewrite getDepsUpdDone_existsb in H5; apply Bool.negb_false_iff in H5.
      apply existsb_exists in H5; destruct H5 as [idep [? ?]].
      apply Bool.negb_true_iff in H6.
      apply H3; [apply in_or_app; left; assumption|].
      rewrite getDepsUpdDone_existsb; apply Bool.negb_false_iff.
      apply existsb_exists.
      exists idep; split; [assumption|].
      apply Bool.negb_true_iff.
      eapply getUpdDone_upd; [eassumption|reflexivity|eassumption].

    - red; simpl; intros.
      erewrite <-getDepsUpdDone_new_upd_ok; [eassumption|reflexivity..].

    - red; intros.
      rewrite getDepsUpdDone_existsb in H5; apply Bool.negb_false_iff in H5.
      apply existsb_exists in H5; destruct H5 as [idep [? ?]].
      apply Bool.negb_true_iff in H6.
      apply H3; [apply in_or_app; right; right; assumption|].
      rewrite getDepsUpdDone_existsb; apply Bool.negb_false_iff.
      apply existsb_exists.
      exists idep; split; [assumption|].
      apply Bool.negb_true_iff.
      eapply getUpdDone_upd; [eassumption|reflexivity|eassumption].
  Qed.

  Lemma genEvalEvent_None_ugraph_not_parent:
    forall upds (Hupds: upds <> []) pproc,
      genEvalEvent (EventUpd upds) pproc = None ->
      forall pun,
        UNodeStd decls funcs mtrss pun pproc ->
        forall st cun,
          UNodeEventOk st cun (Some (EventUpd upds)) ->
          UNodeKeysOk cun ->
          forall v, In v (keys cun) -> In v (deps pun) -> False.
  Proof using .
    unfold genEvalEvent, UNodeStd, UNodeEventOk, UNodeKeysOk; intros; dest.
    destruct (existsb (fun v => match hfind [HEltVid v] upds with
                                | Some _ => true
                                | None => false
                                end) (trig_stv (proc_trig pproc))) eqn:Htr;
      [discriminate|].
    apply UNodeKeysOk_prop with (st:= st) (v:= v) in H6; [|rewrite H5; assumption].
    destruct H6 as [_ ?].
    specialize (H6 H7).
    assert (existsb (fun v => match hfind [HEltVid v] upds with
                              | Some _ => true
                              | None => false
                              end) (trig_stv (proc_trig pproc)) = true) as Het.
    { eapply existsb_In.
      { rewrite <-H11; eassumption. }
      { subst upds.
        destruct (hfind [HEltVid v] (updf cun st)); [reflexivity|].
        elim H6; reflexivity.
      }
    }
    congruence.
  Qed.

  Lemma genEvalEvent_None_updDone_no_effect:
    forall upds (Hupds: upds <> []) pproc,
      genEvalEvent (EventUpd upds) pproc = None ->
      forall pun,
        UNodeStd decls funcs mtrss pun pproc ->
        forall st cun,
          UNodeEventOk st cun (Some (EventUpd upds)) ->
          UNodeKeysOk cun ->
          forall ug1 ug2 ncupd,
            UGraphUnique (ug1 ++ cun :: ug2) ->
            getDepsUpdDone (ug1 ++ cun :: ug2) (deps pun) =
              getDepsUpdDone
                (ug1 ++ {| keys := keys cun;
                          deps := deps cun;
                          updOnce := true;
                          updDone := ncupd;
                          updf := updf cun |} :: ug2) (deps pun).
  Proof using .
    intros.
    pose proof (genEvalEvent_None_ugraph_not_parent Hupds H3 H4 H5 H6) as Hkd.
    assert (forall v, In v (deps pun) ->
                      getUpdDone (ug1 ++ cun :: ug2) v =
                        getUpdDone (ug1 ++ {| keys := keys cun;
                                             deps := deps cun;
                                             updOnce := true;
                                             updDone := ncupd;
                                             updf := updf cun |} :: ug2) v) as Hupd.
    { intros; unfold getUpdDone.
      rewrite !getNode_app.
      destruct (getNode ug1 v) eqn:Hug1; [reflexivity|].
      simpl; destruct (existsb (vid_eqb v) (keys cun)) eqn:Hk; [|reflexivity].
      exfalso.
      apply existsb_exists in Hk; destruct Hk as [vk [? ?]].
      apply vid_eqb_eq in H10; subst vk.
      eapply Hkd; eassumption.
    }
    clear -Hupd.
    induction (deps pun) as [|pdep pdeps]; [reflexivity|].
    simpl.
    rewrite Hupd; [|left; reflexivity].
    rewrite IHpdeps; [reflexivity|].
    intros; apply Hupd; right; assumption.
  Qed.

  Lemma genEvalEvent_None_updOnce_no_effect:
    forall upds (Hupds: upds <> []) pproc,
      genEvalEvent (EventUpd upds) pproc = None ->
      forall pun,
        UNodeStd decls funcs mtrss pun pproc ->
        forall st cun,
          UNodeEventOk st cun (Some (EventUpd upds)) ->
          UNodeKeysOk cun ->
          forall ug1 ug2 ncupd,
            UGraphUnique (ug1 ++ cun :: ug2) ->
            getDepsUpdOnce (ug1 ++ cun :: ug2) (deps pun) =
              getDepsUpdOnce
                (ug1 ++ {| keys := keys cun;
                          deps := deps cun;
                          updOnce := true;
                          updDone := ncupd;
                          updf := updf cun |} :: ug2) (deps pun).
  Proof using .
    intros.
    pose proof (genEvalEvent_None_ugraph_not_parent Hupds H3 H4 H5 H6) as Hkd.
    assert (forall v, In v (deps pun) ->
                      getUpdOnce (ug1 ++ cun :: ug2) v =
                        getUpdOnce (ug1 ++ {| keys := keys cun;
                                             deps := deps cun;
                                             updOnce := true;
                                             updDone := ncupd;
                                             updf := updf cun |} :: ug2) v) as Hupd.
    { intros; unfold getUpdOnce.
      rewrite !getNode_app.
      destruct (getNode ug1 v) eqn:Hug1; [reflexivity|].
      simpl; destruct (existsb (vid_eqb v) (keys cun)) eqn:Hk; [|reflexivity].
      exfalso.
      apply existsb_exists in Hk; destruct Hk as [vk [? ?]].
      apply vid_eqb_eq in H10; subst vk.
      eapply Hkd; eassumption.
    }
    clear -Hupd.
    induction (deps pun) as [|pdep pdeps]; [reflexivity|].
    simpl.
    rewrite Hupd; [|left; reflexivity].
    rewrite IHpdeps; [reflexivity|].
    intros; apply Hupd; right; assumption.
  Qed.

  Lemma genEvalEvent_Some_ugraph_parent:
    forall upds (Hupds: upds <> []) pproc nev,
      genEvalEvent (EventUpd upds) pproc = Some nev ->
      forall pun,
        UNodeStd decls funcs mtrss pun pproc ->
        forall st cun,
          UNodeEventOk st cun (Some (EventUpd upds)) ->
          UNodeKeysOk cun ->
          exists v, In v (keys cun) /\ In v (deps pun).
  Proof using .
    unfold genEvalEvent, UNodeStd, UNodeEventOk, UNodeKeysOk; intros; dest.
    destruct (existsb (fun v => match hfind [HEltVid v] upds with
                                | Some _ => true
                                | None => false
                                end) (trig_stv (proc_trig pproc))) eqn:Htr;
      [|discriminate].
    apply existsb_exists in Htr.
    destruct Htr as [v [? ?]].
    destruct (hfind [HEltVid v] upds) eqn:Hv; [|discriminate].
    subst upds.
    apply UNodeKeysOk_prop with (st:= st) (v:= v) in H6; [|assumption].
    destruct H6 as [? _].
    specialize (H5 ltac:(rewrite Hv; discriminate)).
    rewrite <-H9 in H11.
    exists v; split; assumption.
  Qed.

  Lemma genEvalEvent_Some_updDone_false:
    forall upds (Hupds: upds <> []) pproc nev,
      genEvalEvent (EventUpd upds) pproc = Some nev -> (* upds -> trig pproc *)
      forall ug pun,
        UGraphUnique ug ->
        UNodeUpdOk ug pun ->
        UNodeStd decls funcs mtrss pun pproc -> (* trig pproc = deps pun *)
        forall st cun,
          In cun ug ->
          UNodeEventOk st cun (Some (EventUpd upds)) -> (* updf cun st = upds *)
          UNodeKeysOk cun -> (* (updf cun st) <= (keys cun) *)
          updDone pun = false.
  Proof using .
    intros.
    apply H5. (* [UNodeUpdOk] *)
    eapply genEvalEvent_Some_ugraph_parent in H3; (* [genEvalEvent .. = Some ..] *)
      [|eassumption..].
    destruct H3 as [ckey [? ?]].
    rewrite getDepsUpdDone_existsb; apply Bool.negb_false_iff.
    apply existsb_exists.
    exists ckey; split; [assumption|].
    apply Bool.negb_true_iff.
    unfold getUpdDone.
    (* Use [UGraphUnique] *)
    apply UGraphUnique_getNode in H4; rewrite Forall_forall in H4.
    specialize (H4 _ H7 _ H3).
    rewrite H4.
    apply H8. (* [UNodeEventOk] *)
  Qed.

  Lemma genEvalEvent_Some_updOnce_true:
    forall upds (Hupds: upds <> []) pproc nev,
      genEvalEvent (EventUpd upds) pproc = Some nev ->
      forall pun,
        UNodeStd decls funcs mtrss pun pproc ->
        forall st cun,
          UNodeEventOk st cun (Some (EventUpd upds)) ->
          UNodeKeysOk cun ->
          forall ug1 ug2 ncupd,
            UGraphUnique (ug1 ++ cun :: ug2) ->
            getDepsUpdOnce
              (ug1 ++ {| keys := keys cun;
                        deps := deps cun;
                        updOnce := true;
                        updDone := ncupd;
                        updf := updf cun |} :: ug2) (deps pun) = true.
  Proof using .
    intros.
    eapply genEvalEvent_Some_ugraph_parent in H3; [|eassumption..].
    destruct H3 as [ckey [? ?]].
    rewrite getDepsUpdOnce_existsb.
    apply existsb_exists.
    exists ckey; split; [assumption|].
    unfold getUpdOnce.
    (* Use [UGraphUnique] *)
    eapply UGraphUnique_keys_equiv with (ug2:= ug1 ++ {| keys := keys cun;
                                                        deps := deps cun;
                                                        updOnce := true;
                                                        updDone := ncupd;
                                                        updf := updf cun |} :: ug2) in H7;
      [|rewrite !map_app; reflexivity].
    apply UGraphUnique_getNode in H7; rewrite Forall_forall in H7.
    erewrite H7; [|apply in_or_app; right; left; reflexivity|].
    - reflexivity.
    - assumption.
  Qed.

  Ltac inv_ugraph_events_cons_app He ug1 un2 ug2 :=
    unfold UGraphEventsStOk in He;
    match type of He with
    | Forall2 _ ?ug _ =>
        apply Forall2_app_inv_r in He;
        let He1 := fresh "H" in
        let He2 := fresh "H" in
        destruct He as [ug1 [ug2 [He1 [He2 ?]]]]; subst ug;
        destruct ug2 as [|un2 ug2]; inv He2
    end.

  Lemma ExecEvent_imp_EvalUGraphTrs_upd_others_left:
    forall s tug1 tun tug2 lug evs
           (Htun: UNodeKeysOk tun)
           (Htug: UGraphUnique (tug1 ++ tun :: tug2)),
      Forall2 (fun un oev =>
                 UNodeEventOk s un oev /\ UNodeUpdEvCompl (tug1 ++ tun :: tug2) un oev) lug evs ->
      Forall (UNodeUpdOk (tug1 ++ tun :: tug2)) lug ->
      forall lprocs,
        Forall (fun _ : Process => True) lprocs ->
        UGraphStd decls funcs mtrss lug lprocs ->
        forall upds (Hupds: upds <> []) nevs,
          UNodeEventOk s tun (Some (EventUpd upds)) ->
          GenEvalEvents (EventUpd upds) lprocs evs nevs ->
          Forall2
            (fun un oev =>
               UNodeEventOk (hupds s upds) un oev /\
                 UNodeUpdEvCompl (tug1 ++ {| keys := keys tun;
                                         deps := deps tun;
                                         updOnce := true;
                                         updDone := getDepsUpdDone (tug1 ++ tun :: tug2) (deps tun);
                                         updf := updf tun |} :: tug2) un oev) lug nevs.
  Proof using .
    induction 3; intros; [inv H7; constructor|].
    rename x into un; rename l into ug.
    rename y into oev; rename l' into evs.

    destruct nevs as [|noev nevs]; [inv H9; fail|].
    destruct lprocs as [|lproc lprocs]; [inv H7; fail|].
    inv H5; inv H6; inv H7; inv H9.
    dest.

    constructor; [|eapply IHForall2; eassumption].
    destruct (genEvalEvent (EventUpd upds) lproc) as [nev|] eqn:Hnev.

    - (* Case: the node is triggered to generate an evaluation event. *)
      pose proof Hnev as Hnev0.
      apply genEvalEvent_Some in Hnev0; subst nev.
      split.

      + (* [UNodeEventOk] *)
        destruct oev as [ev|]; [destruct ev as [|eupds|]|].
        * exfalso; red in H3; auto.
        * red in H3; split.
          { eapply H15; exact Hnev. }
          { intuition auto. }
        * red in H3; split.
          { eapply H15; exact Hnev. }
          { intuition auto. }
        * red; split.
          { eapply H15; exact Hnev. }
          { eapply genEvalEvent_Some_updDone_false; try eassumption.
            apply in_or_app; right.
            left; reflexivity.
          }

      + (* [UNodeUpdEvCompl] *)
        red; right.
        eapply genEvalEvent_Some_updOnce_true; eassumption.

    - (* Case: the node is not affected. *)
      split.

      + (* [UNodeEventOk] *)
        destruct oev as [ev|]; [destruct ev as [|eupds|]|].
        * assumption.
        * destruct H3; subst eupds.
          split; [|intuition; fail].
          destruct H15 as [_ [Hsame _]].
          apply Hsame; [|exact Hnev].
          destruct H8 as [Hupd _]. rewrite <-Hupd.
          apply UNodeKeysOk_HMapStrEmpty; exact Htun.
        * assumption.
        * red; auto.

      + (* [UNodeUpdEvCompl] *)
        destruct oev as [ev|].
        * red in H5; red.
          destruct H5; [left; assumption|right].
          erewrite <-genEvalEvent_None_updOnce_no_effect; eassumption.
        * red in H5; red.
          unfold unodeUpdCompl in *.
          destruct (updDone un); [apply Bool.orb_true_r; fail|].
          rewrite Bool.orb_false_r in H5; rewrite Bool.orb_false_r.
          apply Bool.negb_true_iff in H5; apply Bool.negb_true_iff.
          erewrite <-genEvalEvent_None_updDone_no_effect; eassumption.
  Qed.

  Lemma ExecEvent_imp_EvalUGraphTrs_upd:
    forall procs ug1 evs1 upds (Hupds: upds <> []) evs2 s1,
      Forall (fun _ : Process => True) procs ->
      UGraphUnique ug1 ->
      UGraphUpdOk ug1 ->
      UGraphStd decls funcs mtrss ug1 procs ->
      UGraphEventsStOk ug1 (evs1 ++ Some (EventUpd upds) :: evs2) s1 ->
      forall procs1 procs2 proc nevs1 nevs2
             (Hpe: length evs1 = length procs1),
        procs = procs1 ++ proc :: procs2 ->
        GenEvalEvents (EventUpd upds) procs1 evs1 nevs1 ->
        GenEvalEvents (EventUpd upds) procs2 evs2 nevs2 ->
        exists ug2,
          EvalUGraphTrs ug1 s1 ug2 (hupds s1 upds) /\
            UGraphUnique ug2 /\
            UGraphUpdOk ug2 /\
            UGraphStd decls funcs mtrss ug2 procs /\
            UGraphEventsStOk ug2 (nevs1 ++ None :: nevs2) (hupds s1 upds).
  Proof using .
    intros.
    inv_ugraph_events_cons_app H7 ug11 un12 ug12.
    destruct H15.
    eexists; repeat split.
    - apply EvalUGraphTrs_one.
      econstructor; try reflexivity.
      + apply H8. (* [UNodeUpdEvCompl] *)
      + apply H7. (* [UNodeEventOk] *)
      + destruct H7; rewrite H7. (* [UNodeEventOk] *)
        reflexivity.
    - eapply UGraphUnique_keys_equiv; [eassumption|].
      rewrite !map_app; simpl; f_equal.
    - eapply UGraphUpdOk_upd; [|assumption].
      apply H7. (* [UNodeEventOk] *)
    - apply UGraphStd_upd; assumption.
    - apply Forall2_app.
      + eapply ExecEvent_imp_EvalUGraphTrs_upd_others_left;
          [|eassumption|eassumption|..|eassumption].
        * (* [UNodeKeysOk] derived from [UGraphStd] *)
          apply Forall2_app_inv_l in H6; dest; inv H12; apply H16.
        * apply Forall_app in H5; apply H5.
        * apply Forall_app in H3; apply H3.
        * apply Forall2_app_length_inv in H6; dest.
          { assumption. }
          { rewrite <-Hpe; eapply Forall2_length; eassumption. }
        * assumption.
        * assumption.
      + constructor.
        * split; [simpl; trivial|].
          red; unfold unodeUpdCompl; simpl.
          rewrite getDepsUpdDone_new_upd_ok; [|reflexivity..].
          apply Bool.orb_negb_l.
        * eapply ExecEvent_imp_EvalUGraphTrs_upd_others_left;
            [|eassumption|eassumption|..|eassumption].
          { (* [UNodeKeysOk] derived from [UGraphStd] *)
            apply Forall2_app_inv_l in H6; dest; inv H12; apply H16.
          }
          { apply Forall_app in H5; dest.
            inv H12; assumption.
          }
          { apply Forall_app in H3; dest.
            inv H12; assumption.
          }
          { apply Forall2_app_length_inv in H6; dest.
            { inv H12; assumption. }
            { rewrite <-Hpe; eapply Forall2_length; eassumption. }
          }
          { assumption. }
          { assumption. }
  Qed.

  Lemma ExecEvent_imp_EvalUGraphTrs_eval:
    forall ug events1 s,
      UGraphEventsStOk ug events1 s ->
      forall cpos evu uacts unbas,
        execEvalEvent decls funcs mtrss s cpos evu = Sret (uacts, unbas) ->
        forall events2,
          ExecEventRegion (Some (EventEval true cpos evu)) events1 (Some (EventUpd uacts)) events2 ->
          UGraphEventsStOk ug events2 s.
  Proof using .
    intros.
    inv H5.
    inv_ugraph_events_cons_app H3 ug1 un2 ug2.
    apply Forall2_app; [assumption|].
    constructor; [|assumption].
    destruct H9.
    split.
    - destruct H3.
      split; [|assumption].
      rewrite H3.
      rewrite H4.
      reflexivity.
    - assumption.
  Qed.

  Lemma ExecEvent_imp_EvalUGraphTrs:
    forall procs s1 s2 events1 events2 nba1 nba2,
      Forall (fun _ : Process => True) procs ->
      ExecEvent decls funcs mtrss procs s1 events1 nba1 s2 events2 nba2 ->
      nba1 = nilR procs -> nba2 = nilR procs ->
      forall ug1,
        UGraphUnique ug1 ->
        UGraphUpdOk ug1 ->
        UGraphStd decls funcs mtrss ug1 procs ->
        UGraphEventsStOk ug1 events1 s1 ->
        exists ug2, EvalUGraphTrs ug1 s1 ug2 s2 /\
                      UGraphUnique ug2 /\
                      UGraphUpdOk ug2 /\
                      UGraphStd decls funcs mtrss ug2 procs /\
                      UGraphEventsStOk ug2 events2 s2.
  Proof using .
    intros; subst.
    inv H4; [destruct ev; try (exfalso; assumption)|..].
    - (* Case: EventClkPosedge -- exfalso *)
      exfalso.
      inv_ugraph_events_cons_app H10 ug11 un12 ug12.
      destruct H15.
      simpl in H10.
      trivial.
    - (* Case: EventUpd *)
      eapply ExecEvent_imp_EvalUGraphTrs_upd with (evs1 := act11) (evs2 := act12); try eassumption.
      + apply GenEvalEvents_length in H5; intuition.
      + reflexivity.
    - (* Case: EventEval true (Active) *)
      eapply ExecEvent_imp_EvalUGraphTrs_eval in H5; [|eassumption..].
      dest; exists ug1.
      repeat split; [constructor|assumption..].
    - (* Case: EventEval false (NBA) -- exfalso *)
      exfalso.
      eapply ExecEventRegion_nilR_no_some; eassumption.
  Qed.

  Lemma ExecEvents_nba_monotone:
    forall procs s1 act1 nba1 s2 act2 nba2,
      ExecEvents decls funcs mtrss procs s1 act1 nba1 s2 act2 nba2 ->
      nba2 = nilR procs ->
      nba1 = nilR procs.
  Proof using .
    induction 1; intros; [assumption|].
    subst; specialize (IHExecEvents eq_refl); subst.
    clear -H3.
    inv H3; [reflexivity..|].
    exfalso.
    eapply ExecEventRegion_nilR_no_some; eassumption.
  Qed.

  Lemma ExecEvents_imp_EvalUGraphTrs_ind:
    forall procs s1 s2 events1 events2 nba1 nba2,
      Forall (fun _ : Process => True) procs ->
      ExecEvents decls funcs mtrss procs s1 events1 nba1 s2 events2 nba2 ->
      nba1 = nilR procs -> nba2 = nilR procs ->
      forall ug1,
        UGraphUnique ug1 ->
        UGraphUpdOk ug1 ->
        UGraphStd decls funcs mtrss ug1 procs ->
        UGraphEventsStOk ug1 events1 s1 ->
        exists ug2, EvalUGraphTrs ug1 s1 ug2 s2 /\
                      UGraphUnique ug2 /\
                      UGraphUpdOk ug2 /\
                      UGraphStd decls funcs mtrss ug2 procs /\
                      UGraphEventsStOk ug2 events2 s2.
  Proof using .
    induction 2; intros; subst.
    - exists ug1; repeat split; [constructor|assumption..].
    - pose proof H5; apply ExecEvents_nba_monotone in H6; [|reflexivity].
      subst nba1.
      eapply ExecEvent_imp_EvalUGraphTrs in H4; try reflexivity; try eassumption.
      destruct H4 as [ugi ?]; dest.
      specialize (IHExecEvents eq_refl eq_refl _ H6 H7 H12 H13).
      destruct IHExecEvents as [ug2 ?]; dest.
      exists ug2.
      repeat split; [|assumption..].
      eapply EvalUGraphTrs_trs; eassumption.
  Qed.

  (** The graph and initial queue are fixed. Their compatibility is checked at
   * this state, rather than assumed for all modules, inputs, and phases. *)
  Definition UGraphOk (ug: ugraph) (procs: Processes) (events: Region) (st: State): Prop :=
    UGraphUnique ug /\ UGraphUpdOk ug /\ UGraphStd decls funcs mtrss ug procs /\
      UGraphEventsStOk ug events st.

  Lemma graph_empty_queue_complete: forall ug procs st,
    UGraphEventsStOk ug (nilR procs) st -> UGraphUpdCompl ug.
  Proof.
    intros ug procs st Hrel.
    unfold UGraphEventsStOk in Hrel; apply Forall_forall.
    intros un Hin; eapply Forall2_In_left in Hrel; [|exact Hin].
    destruct Hrel as [oev [Hev [_ Hcompl]]].
    unfold nilR in Hev; apply in_map_iff in Hev.
    destruct Hev as [proc [Heq _]]; subst oev; exact Hcompl.
  Qed.

  Theorem ExecTimeSlot_to_graph: forall procs ug st inits stf,
    UGraphOk ug procs (initsR inits) st ->
    ExecTimeSlot decls funcs mtrss procs st (initsR inits) (nilR procs) stf ->
    exists ugf, EvalUGraphTrs ug st ugf stf /\ UGraphUpdCompl ugf.
  Proof.
    intros procs ug st inits stf [Hunique [Hupd [Hprocs Hevents]]] Hslot.
    apply ExecTimeSlot_inits_events in Hslot.
    eapply ExecEvents_imp_EvalUGraphTrs_ind in Hslot; try reflexivity; try eassumption.
    - destruct Hslot as [ugf [Hrun [_ [_ [_ Hfinal]]]]].
      exists ugf; split; [exact Hrun|].
      eapply graph_empty_queue_complete; exact Hfinal.
    - apply Forall_forall; intros; exact I.
  Qed.
End Equivalence.
