Require Import Coq.Lists.List. Import ListNotations.
Require Import Lib.Lib Lang.Semantics Standard UpdGraph ProcUpdGraph TrsProc.

Set Implicit Arguments.

Section SourceShape.
  Context `{sz_ops} `{vid_ops} `{array_ops hmap}.

  Definition SameStrKeys (s1 s2: State): Prop :=
    exists bindings1 bindings2, s1 = HMapStr bindings1 /\ s2 = HMapStr bindings2 /\
      map fst bindings1 = map fst bindings2.

  Definition SameUpdateKeys (u1 u2: State): Prop :=
    (u1 = HMapEmpty /\ u2 = HMapEmpty) \/ SameStrKeys u1 u2.

  Lemma str_find_present: forall bindings key,
    hfind [HEltVid key] (HMapStr bindings) <> None <-> In key (map fst bindings).
  Proof.
    intros bindings key; simpl; pose proof (haccessV_Some bindings key) as Hpresent.
    destruct (haccessV bindings key); simpl in *; intuition congruence.
  Qed.

  Lemma same_keys_present: forall s1 s2,
    SameStrKeys s1 s2 -> forall key,
    hfind [HEltVid key] s1 <> None <-> hfind [HEltVid key] s2 <> None.
  Proof.
    intros s1 s2 (b1 & b2 & Hs1 & Hs2 & Hkeys) key; subst s1 s2.
    rewrite !str_find_present, Hkeys; reflexivity.
  Qed.

  Lemma projected_existsb: forall (bindings: list (vid_t * hmap)) key,
    existsb (fun vh => vid_eqb (fst vh) key) bindings =
      existsb (fun v => vid_eqb v key) (map fst bindings).
  Proof. induction bindings; intros; simpl; [reflexivity|rewrite IHbindings; reflexivity]. Qed.

  Lemma extra_keys: forall bindings updates,
    map fst (hbinUStr2 bindings updates) =
      filter (fun key => negb (existsb (fun v => vid_eqb v key) (map fst bindings))) (map fst updates).
  Proof.
    intros bindings updates; induction updates as [|[key value] rest IH]; [reflexivity|].
    simpl; rewrite projected_existsb.
    destruct (negb (existsb (fun v => vid_eqb v key) (map fst bindings))); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma same_keys_merge: forall s1 s2 u1 u2,
    SameStrKeys s1 s2 -> SameUpdateKeys u1 u2 ->
    SameStrKeys (hmergeR s1 u1) (hmergeR s2 u2).
  Proof.
    intros s1 s2 u1 u2 Hstates [[Hu1 Hu2]|Hupdates].
    - subst u1 u2; rewrite !hmergeR_empty; exact Hstates.
    - destruct Hstates as (b1 & b2 & Hs1 & Hs2 & Hkeys).
      destruct Hupdates as (v1 & v2 & Hu1 & Hu2 & Hupdatekeys); subst s1 s2 u1 u2.
      do 2 eexists; split; [reflexivity|]; split; [reflexivity|].
      rewrite !map_app, !hbinUStr1_vids_eq, !extra_keys, Hkeys, Hupdatekeys; reflexivity.
  Qed.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition activeUpdate (proc: Process) (s: State): State :=
    match trsProc decls funcs mtrss proc s with Sret u => fst u | Fail _ => HMapEmpty end.

  Lemma process_update_keys: forall un proc,
    UNodeSource decls funcs mtrss un proc -> forall s1 s2,
    SameStrKeys s1 s2 -> SameUpdateKeys (activeUpdate proc s1) (activeUpdate proc s2).
  Proof.
    intros un proc [[Hcompute [_ Hsuccess]]|[_ [_ Hempty]]] s1 s2 Hsame.
    - destruct Hcompute as [Hkeys [_ [Hdeps Hfun]]].
      pose proof (Hsuccess s1) as Hsuccess1; pose proof (Hsuccess s2) as Hsuccess2.
      pose proof (Hkeys s1) as Hkeys1; pose proof (Hkeys s2) as Hkeys2.
      rewrite Hfun in Hkeys1,Hkeys2.
      unfold activeUpdate.
      destruct (trsProc decls funcs mtrss proc s1) as [[acts1 nbas1]|err1] eqn:Hrun1;
        destruct (trsProc decls funcs mtrss proc s2) as [[acts2 nbas2]|err2] eqn:Hrun2;
        simpl in Hsuccess1,Hsuccess2,Hkeys1,Hkeys2.
      + destruct Hsuccess1 as [Hnonempty1 _], Hsuccess2 as [Hnonempty2 _].
        destruct Hkeys1 as [Hbad|(b1 & Hacts1 & Hkeys1)]; [contradiction|].
        destruct Hkeys2 as [Hbad|(b2 & Hacts2 & Hkeys2)]; [contradiction|].
        right; exists b1,b2; repeat split; simpl; congruence.
      + destruct Hsuccess1 as [_ Hpresent], Hsuccess2 as (key & Hin & Hmissing).
        eapply Forall_In in Hpresent; [|exact Hin].
        exfalso; apply (proj1 (same_keys_present Hsame key) Hpresent); exact Hmissing.
      + destruct Hsuccess2 as [_ Hpresent], Hsuccess1 as (key & Hin & Hmissing).
        eapply Forall_In in Hpresent; [|exact Hin].
        exfalso; apply (proj2 (same_keys_present Hsame key) Hpresent); exact Hmissing.
      + left; split; reflexivity.
    - assert (Hactive: forall s, activeUpdate proc s = HMapEmpty).
      { intros s; unfold activeUpdate; destruct (trsProc decls funcs mtrss proc s) eqn:Hrun;
          [eapply Hempty; exact Hrun|reflexivity]. }
      rewrite !Hactive; left; split; reflexivity.
  Qed.

  Lemma source_sweep_keys: forall ug procs,
    UGraphSource decls funcs mtrss ug procs ->
    forall s1 s2, SameStrKeys s1 s2 -> forall f1 f2 next1 next2 nf1 nf2,
    trsProcs decls funcs mtrss procs (s1,f1) = Sret (next1,nf1) ->
    trsProcs decls funcs mtrss procs (s2,f2) = Sret (next2,nf2) -> SameStrKeys next1 next2.
  Proof.
    intros ug procs Hsource; induction Hsource;
      intros s1 s2 Hsame f1 f2 next1 next2 nf1 nf2 Hrun1 Hrun2.
    - simpl in Hrun1,Hrun2; inversion Hrun1; inversion Hrun2; subst; exact Hsame.
    - pose proof (process_update_keys H3 Hsame) as Hupdates.
      unfold activeUpdate in Hupdates; simpl in Hrun1,Hrun2.
      destruct (trsProc decls funcs mtrss y s1) as [[a1 b1]|err1];
        destruct (trsProc decls funcs mtrss y s2) as [[a2 b2]|err2];
        unfold iffupds in Hrun1,Hrun2; simpl in Hrun1,Hrun2,Hupdates;
        (eapply IHHsource; [|exact Hrun1|exact Hrun2]; eapply same_keys_merge; eassumption).
  Qed.

  Lemma source_fix_keys: forall ug procs,
    UGraphSource decls funcs mtrss ug procs -> forall stable flops,
    trsProcs decls funcs mtrss procs (stable,HMapEmpty) = Sret (stable,flops) ->
    forall start final nf, TrsProcsRep decls funcs mtrss procs start final nf ->
    SameStrKeys stable start -> SameStrKeys stable final.
  Proof.
    intros ug procs Hsource stable flops Hfix start final nf Hrun.
    induction Hrun; intros Hsame; [|exact Hsame].
    apply IHHrun; eapply source_sweep_keys; eassumption.
  Qed.

  Theorem source_result_keys: forall ug procs,
    UGraphSource decls funcs mtrss ug procs -> forall s1 final1 f1,
    TrsProcsRep decls funcs mtrss procs s1 final1 f1 -> forall s2 final2 f2,
    TrsProcsRep decls funcs mtrss procs s2 final2 f2 ->
    SameStrKeys s1 s2 -> SameStrKeys final1 final2.
  Proof.
    intros ug procs Hsource s1 final1 f1 Hrun1; induction Hrun1;
      intros s2 final2 f2 Hrun2 Hsame.
    - inversion Hrun2; subst.
      + eapply IHHrun1; [eassumption|eapply source_sweep_keys; eassumption].
      + eapply IHHrun1; [exact Hrun2|eapply source_sweep_keys; eassumption].
    - eapply source_fix_keys; eassumption.
  Qed.
End SourceShape.
