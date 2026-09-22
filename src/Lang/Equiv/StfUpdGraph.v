Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics. Include SFMonadNotations.

Require Import UpdGraph Standard ProcUpdGraph TrsProc RankedGraph.

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

  Lemma UNodeSt_upd_other_no_effect:
    forall ug1 un ug2,
      UGraphUnique (ug1 ++ un :: ug2) ->
      UNodeKeysOk un ->
      forall oun,
        In oun ug1 \/ In oun ug2 ->
        forall ifw,
          HMapStrEmpty ifw ->
          HMapStrEmpty (updf un ifw) ->
          UNodeSt ifw oun ->
          UNodeSt (hmergeR ifw (updf un ifw)) oun.
  Proof using .
    intros.
    red in H8; dest.
    red; split; [assumption|].
    split; intros.
    - specialize (H9 H11 _ H12); intro Hx; elim H9.
      rewrite hmergeR_hfind in Hx by assumption.
      destruct (hfind [HEltVid v] (updf un ifw)); [discriminate|].
      assumption.
    - specialize (H10 H11 _ H12).
      rewrite hmergeR_hfind by assumption.
      rewrite H10.

      specialize (H4 ifw); destruct H4; [rewrite H4; reflexivity|].
      destruct H4 as [uvs [? ?]].
      rewrite H4; simpl.
      pose proof (haccessV_Some uvs v) as Hv; destruct Hv as [Hv _].
      destruct (haccessV uvs v); [|reflexivity].
      exfalso.
      specialize (Hv ltac:(discriminate)).
      rewrite <-H13 in Hv.
      destruct H5.
      + eapply UGraphUnique_false_left; [eassumption|..]; eassumption.
      + eapply UGraphUnique_false_right; [eassumption|..]; eassumption.
  Qed.

  Lemma UGraphSt_upd:
    forall proc (HprocWf0: ProcWfExecUniq decls funcs mtrss proc)
           (HprocWf1: ProcWfExecSucc decls funcs mtrss proc)
           ifw (Hifw: HMapStrEmptyWf ifw)
           uifw nflops,
      trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
      forall ug1 un ug2,
        UGraphUnique (ug1 ++ un :: ug2) ->
        UGraphSt ifw (ug1 ++ un :: ug2) ->
        UNodeCompute decls funcs mtrss un proc ->
        UGraphSt (hmergeR ifw uifw)
          (ug1 ++ {| keys := keys un;
                    deps := deps un;
                    updOnce := true;
                    updDone := true;
                    updf := updf un |} :: ug2) /\
          HMapStrEmptyWf (hmergeR ifw uifw).
  Proof using .
    unfold UNodeCompute; intros; dest.
    apply Forall_app in H5; dest; inv H10.
    assert (uifw = updf un ifw) by (rewrite H9, H3; reflexivity); subst uifw.
    pose proof (UNodeKeysOk_HMapStrEmpty H6 ifw) as Huifw.
    split.
    2: { apply HMapStrEmptyWf_hmergeR; [assumption|].
         specialize (HprocWf0 ifw); rewrite H3 in HprocWf0; assumption.
    }

    apply Forall_app; split; [|constructor].
    - apply Forall_forall; intros oun ?.
      eapply Forall_In in H5; [|eassumption].
      eapply UNodeSt_upd_other_no_effect; try eassumption.
      + left; assumption.
      + apply HMapStrEmptyWf_HMapStrEmpty; assumption.
    - red in H13; dest.
      red; split; [reflexivity|].
      split; intros; [|discriminate].
      rewrite hmergeR_hfind; [|apply HMapStrEmptyWf_HMapStrEmpty; assumption|assumption].

      (* use [UNodeKeysOk] *)
      specialize (H6 ifw); destruct H6.
      + exfalso.
        specialize (HprocWf1 ifw).
        rewrite H3 in HprocWf1; dest.
        elim H16; assumption.
      + destruct H6 as [uvs [? ?]].
        rewrite H6; simpl in *.
        rewrite H16 in H15.
        apply haccessV_Some in H15.
        destruct (haccessV uvs v); [assumption|].
        elim H15; reflexivity.

    - apply Forall_forall; intros oun ?.
      eapply Forall_In in H14; [|eassumption].
      eapply UNodeSt_upd_other_no_effect; try eassumption.
      + right; assumption.
      + apply HMapStrEmptyWf_HMapStrEmpty; assumption.
  Qed.

  Lemma unode_updated_hmergeR:
    forall un ifw,
      HMapStrEmptyWf ifw ->
      (forall v, In v (keys un) ->
                 hfind [HEltVid v] ifw = hfind [HEltVid v] (updf un ifw)) ->
      UNodeKeysOk un ->
      keys un <> nil ->
      hmergeR ifw (updf un ifw) = ifw.
  Proof using .
    unfold UNodeKeysOk; intros.
    specialize (H5 ifw); destruct H5;
      [rewrite H5; apply hmergeR_empty|].
    destruct H5 as [uvs [? ?]].
    rewrite H5 in *; clear H5.

    destruct ifw; try (exfalso; auto; fail).
    - exfalso.
      destruct (keys un) as [|k ?]; [elim H6; reflexivity|].
      destruct uvs as [|[uk uv] uvs]; [discriminate|].
      simpl in *; inv H7.
      specialize (H4 uk (or_introl eq_refl)).
      rewrite vid_eqb_refl in H4; discriminate.
    - rewrite H7 in H4.
      apply hmergeR_absorbed; assumption.
  Qed.

  Lemma getNode_Some_In:
    forall ug k un, getNode ug k = Some un -> In un ug /\ In k (keys un).
  Proof using .
    induction ug as [|un ug]; simpl; intros; [discriminate|].
    destruct (existsb _ _) eqn:Hk.
    - inv H3; split.
      + left; reflexivity.
      + apply existsb_exists in Hk; destruct Hk as [uk [? ?]].
        apply vid_eqb_eq in H4; subst uk.
        assumption.
    - specialize (IHug _ _ H3).
      intuition.
  Qed.

  Lemma trsProc_UGraphSt_upd:
    forall proc (Hproc: ProcSourceWf decls funcs mtrss proc)
           ifw uifw nflops,
      trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
      forall ug,
        UGraphUnique ug ->
        UGraphDepsOk ug ->
        UGraphSt ifw ug ->
        forall un,
          In un ug ->
          UNodeCompute decls funcs mtrss un proc ->
          getDepsUpdDone ug (deps un) = true /\
            (deps un = []%list \/ getDepsUpdOnce ug (deps un) = true).
  Proof using .
    intros.
    destruct Hproc as [_ Hproc]; specialize (Hproc ifw).
    rewrite H3 in Hproc; destruct Hproc as [Huifwe Hproc].
    simpl in Huifwe.

    (* reducing [UGraphDepsOk] *)
    eapply Forall_In in H5; [|eassumption].
    red in H5.

    (* reducing [UNodeCompute] *)
    red in H8; dest.
    rewrite <-H10 in Hproc.
    clear H8 H9 H10.

    assert (forall dk, In dk (deps un) -> getUpdDone ug dk = true /\ getUpdOnce ug dk = true) as Hdt.
    { intros.
      eapply Forall_In in Hproc; [|eassumption].
      eapply Forall_In in H5; [|eassumption].
      unfold getUpdDone, getUpdOnce; destruct (getNode ug dk) eqn:Hdk; [|elim H5; reflexivity].
      apply getNode_Some_In in Hdk; dest.
      eapply Forall_In in H6; [|eassumption].
      red in H6; dest.
      rewrite H6.
      destruct (updDone u); [split; reflexivity|].
      specialize (H13 eq_refl _ H10).
      elim Hproc; assumption.
    }

    split.
    - rewrite getDepsUpdDone_existsb.
      apply Bool.negb_true_iff.
      apply existsb_false_forall.
      intros.
      specialize (Hdt _ H8); dest.
      rewrite H9; reflexivity.
    - rewrite getDepsUpdOnce_existsb.
      destruct (deps un) as [|dk ds].
      + left; reflexivity.
      + right; apply existsb_exists.
        exists dk; split; [left; reflexivity|].
        specialize (Hdt dk).
        apply Hdt; left; reflexivity.
  Qed.

  Section WithBase.
    Let stb: State := HMapEmpty.

    Lemma trsProc_imp_EvalUGraphTrs:
      forall proc gprocs,
        In proc gprocs ->
        forall ifw (Hifw: HMapStrEmptyWf ifw) uifw nflops,
          trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
          forall ug (Hupdf: UpdfSub ug ifw),
            UGraphDepsOk ug ->
            UGraphUnique ug ->
            UGraphSource decls funcs mtrss ug gprocs ->
            UGraphSt ifw ug ->
            exists nug, EvalUGraphTrs ug (hupds stb ifw) nug (hupds stb (hmergeR ifw uifw)) /\
                          UGraphDepsOk nug /\
                          UGraphUnique nug /\
                          UGraphSource decls funcs mtrss nug gprocs /\
                          UGraphSt (hmergeR ifw uifw) nug /\
                          HMapStrEmptyWf (hmergeR ifw uifw).
    Proof using .
      intros.
      apply List.in_split in H3; destruct H3 as [procs1 [procs2 ?]]; subst gprocs.
      pose proof H7 as Hup.
      apply Forall2_app_inv_r in H7; destruct H7 as [ug1 [ug2 [? [? ?]]]].
      destruct ug2 as [|un ug2]; inv H7.
      destruct H13 as [[H13 Hprocwf] | [Honce [Hdone Hempty]]].
      2: { specialize (Hempty ifw (uifw, nflops) H4); simpl in Hempty.
           subst uifw; rewrite hmergeR_empty.
           exists (ug1 ++ un :: ug2); split; [apply EvalUGraphId|].
           repeat split; assumption. }
      destruct (updDone un) eqn:Huu.

      - assert (hmergeR ifw uifw = ifw) as Hnupd.
        { replace uifw with (updf un ifw).
          { apply unode_updated_hmergeR; try assumption.
            { apply Forall_app in Hupdf; destruct Hupdf as [_ Hupdf].
              apply Forall_cons_iff in Hupdf; destruct Hupdf as [Hupdf _].
              apply Hupdf; assumption.
            }
            { apply H13. }
            { apply H13. }
          }
          { red in H13; dest.
            rewrite H11; simpl.
            rewrite H4.
            reflexivity.
          }
        }

        rewrite Hnupd.
        eexists; repeat split; [apply EvalUGraphId; fail|..]; assumption.

      - pose proof Hprocwf as H10.
        exists (ug1 ++ {| keys := keys un;
                         deps := deps un;
                         updOnce := true;
                         updDone := true;
                         updf := updf un |} :: ug2);
          repeat split.

        + (* [EvalUGraphTrs] *)
          assert (getDepsUpdDone (ug1 ++ un :: ug2) (deps un) = true) as Hud.
          { eapply trsProc_UGraphSt_upd; try eassumption.
            apply in_or_app; right; left; reflexivity.
          }
          apply EvalUGraphTrs_one.
          econstructor; [reflexivity| | |reflexivity|..].
          * eapply trsProc_UGraphSt_upd; try eassumption.
            apply in_or_app; right; left; reflexivity.
          * assumption.
          * rewrite Hud; reflexivity.
          * assert (updf un (hupds stb ifw) = uifw /\ HMapStrEmpty uifw) as Hupdb.
            { destruct H13 as [Hkeys [_ [_ Heval]]].
              assert (Heq: updf un ifw = uifw) by (rewrite Heval, H4; reflexivity).
              split; [exact Heq|].
              rewrite <-Heq; apply UNodeKeysOk_HMapStrEmpty; exact Hkeys. }

            destruct Hupdb.
            rewrite H7.
            apply hupds_hmergeR_assoc.
            { apply HMapStrEmptyWf_HMapStrEmpty; assumption. }
            { assumption. }
            { assert (Habsent: forall v, In v (keys un) -> hfind [HEltVid v] ifw = None).
              { unfold UGraphSt in H8; rewrite Forall_forall in H8.
                specialize (H8 un ltac:(apply in_or_app; right; left; reflexivity)).
                exact (proj2 (proj2 H8) Huu). }
              destruct H13 as [Hkeys _]. specialize (Hkeys ifw).
              change (updf un ifw = uifw) in H7; rewrite H7 in Hkeys.
              destruct Hkeys as [Heq | [bindings [Heq Hkeys]]]; subst uifw.
              - destruct ifw; exact I.
              - destruct ifw; try exact I.
                intros v HinOld HinNew.
                rewrite <-Hkeys in HinNew.
                specialize (Habsent v HinNew).
                apply haccessV_Some in HinOld; simpl in Habsent.
                destruct (haccessV str v); [discriminate|contradiction].
            }

        + (* [UGraphDepsOk] *)
          eapply UGraphDepsOk_keys_equiv; [eassumption|..].
          all: rewrite !map_app; simpl; f_equal.

        + (* [UGraphUnique] *)
          eapply UGraphUnique_keys_equiv; [eassumption|].
          rewrite !map_app; simpl; f_equal.

        + (* [UGraphSource] *)
          apply UGraphSource_upd; assumption.

        + (* [UGraphSt] *)
          eapply UGraphSt_upd; try eassumption.
          all: apply H10.
        + eapply UGraphSt_upd; try eassumption.
          all: apply H10.
    Qed.

    Lemma trsProcs_imp_EvalUGraphTrs_ind:
      forall (P: State -> Prop) gprocs procs,
        (exists prefix, gprocs = prefix ++ procs) ->
        forall ifw, HMapStrEmptyWf ifw ->
        forall nifw flops nflops,
        trsProcs decls funcs mtrss procs (ifw, flops) = Sret (nifw, nflops) ->
        forall ug, P ifw -> UpdfSub ug ifw -> UGraphKeysOk ug ->
        GraphDomain ug P -> UGraphDepsOk ug -> UGraphUnique ug ->
        UGraphSource decls funcs mtrss ug gprocs -> UGraphSt ifw ug ->
        exists nug, EvalUGraphTrs ug ifw nug nifw /\
          UGraphDepsOk nug /\ UGraphUnique nug /\
          UGraphSource decls funcs mtrss nug gprocs /\ UGraphSt nifw nug /\
          HMapStrEmptyWf nifw.
    Proof.
      intros P gprocs procs; induction procs as [|proc rest IH];
        intros Hprefix ifw Hifw nifw flops nflops Hrun ug HP Hsub Hkeys
          Hdomain Hdeps Hunique Hsource Hstate.
      - simpl in Hrun; inversion Hrun; subst.
        exists ug; split; [constructor|repeat split; assumption].
      - assert (Htail: exists prefix, gprocs = prefix ++ rest).
        { destruct Hprefix as [prefix Hprefix]; subst gprocs.
          exists (prefix ++ [proc]); rewrite <-app_assoc; reflexivity. }
        assert (Hin: In proc gprocs).
        { destruct Hprefix as [prefix Hprefix]; subst gprocs.
          apply in_or_app; right; left; reflexivity. }
        simpl in Hrun.
        destruct (trsProc decls funcs mtrss proc ifw) as [[uifw uflops]|err] eqn:Hproc;
          unfold iffupds in Hrun; simpl in Hrun.
        + destruct (trsProc_imp_EvalUGraphTrs proc Hin Hifw Hproc Hsub Hdeps Hunique
            Hsource Hstate) as [next [Hstep [Hdn [Hun [Hsn [Hstn Hifwn]]]]]].
          change (EvalUGraphTrs ug ifw next (hmergeR ifw uifw)) in Hstep.
          destruct (graph_domain_trace Hdomain Hstep (SameGraph_refl ug)
            Hunique Hkeys HP Hsub) as [HPn Hsubn].
          assert (Hkn: UGraphKeysOk next) by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
          assert (Hdomainn: GraphDomain next P).
          { eapply SameGraph_domain; [eapply EvalUGraphTrs_same; exact Hstep|exact Hdomain]. }
          destruct (IH Htail _ Hifwn _ _ _ Hrun next HPn Hsubn Hkn Hdomainn
            Hdn Hun Hsn Hstn) as [final [Hrest Hfinal]].
          exists final; split; [eapply EvalUGraphTrs_trs; eassumption|exact Hfinal].
        + rewrite !hmergeR_empty in Hrun.
          eapply IH; eassumption.
    Qed.

  End WithBase.

  Section WithProcs.
    Variables (procs: Processes) (initialGraph: ugraph) (initialState: State).

    Hypotheses (HprocsU: ProcsWfUpd decls funcs mtrss procs)
      (HprocsD: ProcsWfDet decls funcs mtrss procs).

    Definition UNodeUpdComplFull (ug: ugraph) (un: unode) :=
      unodeUpdCompl ug un = true /\ updOnce un = updDone un.

    Definition UGraphUpdComplFull (ug: ugraph): Prop :=
      Forall (UNodeUpdComplFull ug) ug.

    Lemma fp_UGraphUpdComplFull:
      forall stf (Hstf: HMapStrEmptyWf stf) flops nflops,
        trsProcs decls funcs mtrss procs (stf, flops) = Sret (stf, nflops) ->
        forall ugf,
          UGraphSource decls funcs mtrss ugf procs ->
          UGraphSt stf ugf ->
          UGraphUpdComplFull ugf.
    Proof using All.
      intros; red.
      apply Forall_forall.
      intros un ?.
      split.
      2: { red in H5; rewrite Forall_forall in H5; specialize (H5 _ H6).
           red in H5; dest; assumption.
      }

      unfold unodeUpdCompl.
      destruct (getDepsUpdDone ugf (deps un)) eqn:Hud; [simpl|reflexivity].
      destruct (updDone un) eqn:Hun; [reflexivity|exfalso].

      pose proof H5 as Hust.
      eapply Forall_In in H5; [|eassumption].
      red in H5; dest.
      specialize (H8 Hun).

      eapply Forall2_In_left in H4; [|eassumption].
      destruct H4 as [proc [? ?]].
      eapply trsProcs_fp_ind in H3; [|eassumption..].
      destruct H9 as [[H9 [Huniq Hsucc]] | [_ [Hdone _]]]; [|congruence].
      red in H9; dest.
      specialize (H12 stf).
      specialize (H9 stf).
      specialize (Hsucc stf); rename Hsucc into H13.

      destruct (trsProc decls funcs mtrss proc stf) as [[pifw pflops]|] eqn:Hp.
      - simpl in H12; subst pifw.
        destruct H9.
        + rewrite H9 in H13.
          destruct H13; elim H12; reflexivity.
        + destruct H9 as [uvs [? ?]].
          rewrite H9 in *.
          rewrite H12 in *.
          assert (forall v, hfind [HEltVid v] (hmergeR stf (HMapStr uvs)) =
                              match hfind [HEltVid v] (HMapStr uvs) with
                              | Some v0 => Some v0
                              | None => hfind [HEltVid v] stf
                              end) as Hmf
            by (apply hmergeR_hfind; [apply HMapStrEmptyWf_HMapStrEmpty; assumption|red; auto]).
          rewrite H3 in Hmf.
          destruct (map fst uvs) as [|uk uks] eqn:Hku; [elim H10; reflexivity|].
          specialize (H8 uk (or_introl eq_refl)).
          specialize (Hmf uk); rewrite H8 in Hmf.
          destruct uvs as [|[huk huv] uvs]; inv Hku; simpl in *.
          rewrite vid_eqb_refl in Hmf; discriminate.

      - destruct H13 as [dk [? ?]].
        rewrite <-H11 in H13.
        rewrite getDepsUpdDone_existsb in Hud.
        apply Bool.negb_true_iff in Hud.
        rewrite existsb_false_forall in Hud.
        specialize (Hud _ H13).
        apply Bool.negb_false_iff in Hud.
        unfold getUpdDone in Hud.
        destruct (getNode ugf dk) as [dun|] eqn:Hdn; [|discriminate].
        apply getNode_Some_In in Hdn; dest.

        eapply Forall_In in Hust; [|eassumption].
        red in Hust; dest.
        specialize (H18 Hud _ H16).
        elim H18; assumption.
    Qed.

    Lemma TrsProcsRep_graph_result:
      forall (P: State -> Prop) inits stf flops,
        TrsProcsRep decls funcs mtrss procs inits stf flops ->
        HMapStrEmptyWf inits -> forall iug,
        P inits -> UpdfSub iug inits -> UGraphKeysOk iug -> GraphDomain iug P ->
        UGraphDepsOk iug -> UGraphUnique iug ->
        UGraphSource decls funcs mtrss iug procs -> UGraphSt inits iug ->
        exists ugf, EvalUGraphTrs iug inits ugf stf /\ UGraphUpdComplFull ugf /\
          UGraphSt stf ugf /\ HMapStrEmptyWf stf.
    Proof.
      intros P inits stf flops Hrun.
      induction Hrun as [ifw1 ifwf flops Hrep IH ifw0 flops1 Hstep | ifw flops Hfix];
        intros Hifw ug HP Hsub Hkeys Hdomain Hdeps Hunique Hsource Hstate.
      - destruct (trsProcs_imp_EvalUGraphTrs_ind (P := P) (gprocs := procs) procs
          ltac:(exists nil; reflexivity) Hifw HMapEmpty Hstep HP Hsub Hkeys Hdomain
          Hdeps Hunique Hsource Hstate)
          as [next [Htrace [Hdn [Hun [Hsn [Hstn Hifwn]]]]]].
        destruct (graph_domain_trace Hdomain Htrace (SameGraph_refl ug)
          Hunique Hkeys HP Hsub) as [HPn Hsubn].
        assert (Hkn: UGraphKeysOk next) by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
        assert (Hdomainn: GraphDomain next P).
        { eapply SameGraph_domain; [eapply EvalUGraphTrs_same; exact Htrace|exact Hdomain]. }
        destruct (IH Hifwn next HPn Hsubn Hkn Hdomainn Hdn Hun Hsn Hstn)
          as [final [Hrest Hcomplete]].
        exists final; split; [eapply EvalUGraphTrs_trs; eassumption|exact Hcomplete].
      - exists ug; split; [constructor|].
        split; [eapply fp_UGraphUpdComplFull; eassumption|split; assumption].
    Qed.

    Lemma TrsProcsRep_imp_EvalUGraphTrs_ind:
      forall (P: State -> Prop) inits stf flops,
        TrsProcsRep decls funcs mtrss procs inits stf flops ->
        HMapStrEmptyWf inits -> forall iug,
        P inits -> UpdfSub iug inits -> UGraphKeysOk iug -> GraphDomain iug P ->
        UGraphDepsOk iug -> UGraphUnique iug ->
        UGraphSource decls funcs mtrss iug procs -> UGraphSt inits iug ->
        exists ugf, EvalUGraphTrs iug inits ugf stf /\ UGraphUpdComplFull ugf.
    Proof.
      intros P inits stf flops Hrun Hifw ug HP Hsub Hkeys Hdomain Hdeps Hunique Hsource Hstate.
      destruct (TrsProcsRep_graph_result (P := P) Hrun Hifw HP Hsub Hkeys Hdomain
        Hdeps Hunique Hsource Hstate) as [final [Htrace [Hcomplete _]]].
      exists final; split; assumption.
    Qed.

    Local Notation ugMInitsU := initialGraph.
    Local Notation initState := initialState.

    (** Conditions for the source's initial graph. *)
    Variable (P: State -> Prop).
    Hypotheses (HP: P initState)
      (Huu: UGraphUnique ugMInitsU)
      (Huk: UGraphKeysOk ugMInitsU)
      (Hud: UGraphDepsOk ugMInitsU)
      (Huf: GraphDomain ugMInitsU P)
      (Hup: UGraphSource decls funcs mtrss ugMInitsU procs)
      (Hus: UGraphSt initState ugMInitsU)
      (Hufs: UpdfSub ugMInitsU initState)
      (Hku: HMapStrEmptyWf initState).

    Theorem TrsProcsRep_imp_EvalUGraphTrs:
      forall stf flops,
        TrsProcsRep decls funcs mtrss procs initState stf flops ->
        exists ug2, EvalUGraphTrsFp ugMInitsU initState ug2 stf.
    Proof using All.
      intros.
      eapply TrsProcsRep_imp_EvalUGraphTrs_ind with (P := P) in H3;
        try eassumption.
      - destruct H3 as [ugf [? ?]].
        exists ugf; repeat split; try assumption.
        + apply Forall_forall; intros.
          red in H4; rewrite Forall_forall in H4; specialize (H4 _ H5).
          apply H4.
        + apply Forall_forall; intros.
          red in H4; rewrite Forall_forall in H4; specialize (H4 _ H5).
          apply H4.
    Qed.

  End WithProcs.

End Equivalence.
