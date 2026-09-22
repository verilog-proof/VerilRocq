Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics. Include SFMonadNotations.

Require Import Standard TrsProc ProcUpdGraph.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section StfStd.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss)
    (mprocs: Processes). (* Processes from the given module. *)

  Definition procs: Processes := getProcInputClk :: mprocs.

  Definition ipsIns (inputs: InitState): IPS :=
    (inputs, getProcInputClk) :: (List.map (fun mproc => (nil, mproc)) mprocs).

  Fixpoint combineIps (inits: list InitState) (procs: list Process): IPS :=
    match procs with
    | proc :: tprocs => match inits with
                        | init :: tinits => (init, proc) :: (combineIps tinits tprocs)
                        | nil => List.map (fun proc => (nil, proc)) procs
                        end
    | nil => nil
    end.

  Definition ipsFlops (flops: list InitState): IPS :=
    (nil, getProcInputClk) :: (combineIps flops mprocs).

  Definition ipsAll (inputs: InitState) (flops: list InitState): IPS :=
    (inputs, getProcInputClk) :: (combineIps flops mprocs).

  (** Compare flop bindings observationally: an execution can return
   * [HMapEmpty], whereas aggregating an empty list produces [HMapStr nil]. *)
  Definition TrsF (ins: InitState) (flops nflops: list InitState): Prop :=
    exists stf computed,
      TrsProcsRep decls funcs mtrss procs (initState (ipsAll ins flops)) stf computed /\
      HSEquiv computed (initState (ipsFlops nflops)).

  Definition StateOf (ins: InitState) (flops: list InitState) (stf: State): Prop :=
    exists nflops, TrsProcsRep decls funcs mtrss procs (initState (ipsAll ins flops)) stf nflops.

  Definition TrsI (st0 st1: State) (inputs: InitState): Prop :=
    ExecTimeSlot decls funcs mtrss procs st0 (inputsR procs inputs) (nilR procs) st1.

  Definition TrsC (st0 st1: State) (flops: list InitState): Prop :=
    ExecTimeSlot decls funcs mtrss procs st0 (flopsR flops) (nilR procs) st1.

  Lemma std_ipsIns_procs:
    forall ins, List.map snd (ipsIns ins) = procs.
  Proof using All.
    unfold procs; simpl; intros.
    f_equal.
    clear; induction mprocs; [reflexivity|simpl; congruence].
  Qed.

  Lemma std_ipsFlops_procs:
    forall flops, List.map snd (ipsFlops flops) = procs.
  Proof using All.
    unfold ipsFlops, procs; simpl; intros.
    f_equal.
    generalize dependent flops.
    induction mprocs; intros.
    - destruct flops; reflexivity.
    - destruct flops; simpl.
      + f_equal; clear.
        induction p; [reflexivity|simpl; congruence].
      + congruence.
  Qed.

  Lemma std_ipsAll_procs:
    forall ins flops, List.map snd (ipsAll ins flops) = procs.
  Proof using All.
    unfold ipsAll, procs; simpl; intros.
    f_equal.
    generalize dependent flops.
    induction mprocs; intros.
    - destruct flops; reflexivity.
    - destruct flops; simpl.
      + f_equal; clear.
        induction p; [reflexivity|simpl; congruence].
      + congruence.
  Qed.

  (** A certificate concerns one injection from one initial state. Its invariant
   * is preserved by individual active events and identifies a source fixed
   * point when the queue empties. Termination is required only for this slot.
   * No condition is imposed on unrelated states, queues, or update graphs. *)
  Definition InjectionReady (st0: State) (inits: list InitState)
    (ins: InitState) (flops: list InitState): Prop :=
    (exists Inv: State -> Region -> Prop,
      Inv st0 (initsR inits) /\
      (forall s act s' act',
        Inv s act ->
        ExecEvent decls funcs mtrss procs s act (nilR procs)
          s' act' (nilR procs) ->
        Inv s' act') /\
      (forall s, Inv s (nilR procs) -> StateOf ins flops s)) /\
    (exists s, ExecTimeSlot decls funcs mtrss procs st0
      (initsR inits) (nilR procs) s).

  Lemma StateOf_det: forall ins flops s1 s2,
    StateOf ins flops s1 -> StateOf ins flops s2 -> s1 = s2.
  Proof.
    intros ins flops s1 s2 [nf1 Hrun1] [nf2 Hrun2].
    exact (proj1 (TrsProcsRep_det Hrun1 Hrun2)).
  Qed.

  Lemma injection_ready_empty: forall st0 inits ins flops,
    initsR inits = nilR procs -> StateOf ins flops st0 ->
    InjectionReady st0 inits ins flops.
  Proof.
    intros st0 inits ins flops Hempty Hstate; split.
    - exists (fun s act => s = st0 /\ act = nilR procs).
      split; [split; [reflexivity|exact Hempty]|].
      split.
      + intros s act s' act' [_ Heq] Hstep; subst act.
        exfalso; eapply ExecEvent_nilR_false; eassumption.
      + intros s [Heq _]; subst s; exact Hstate.
    - exists st0; rewrite Hempty; constructor.
  Qed.

  Lemma injection_equiv: forall st0 inits ins flops,
    InjectionReady st0 inits ins flops ->
    forall stf,
      StateOf ins flops stf <->
      ExecTimeSlot decls funcs mtrss procs st0
        (initsR inits) (nilR procs) stf.
  Proof.
    intros st0 inits ins flops [[Inv [Hinit [Hstep Hdone]]] Hprogress].
    assert (Hsound: forall stf,
      ExecTimeSlot decls funcs mtrss procs st0
        (initsR inits) (nilR procs) stf -> StateOf ins flops stf).
    { intros stf Hslot. apply Hdone.
      eapply ExecTimeSlot_inits_invariant; eassumption. }
    intros stf; split.
    - intros Hsource. destruct Hprogress as [s Hslot].
      pose proof (StateOf_det Hsource (Hsound _ Hslot)) as Heq.
      subst s; exact Hslot.
    - apply Hsound.
  Qed.

  Section InjectionEquiv.
    Variables (ins0 ins1: InitState) (flops0 flops1: list InitState).

    (** These are event-invariant and termination obligations for the two
     * concrete injections. They must be established for the module and input
     * domain in use; they do not assert a whole-program equivalence. *)
    Hypothesis Hinputs: forall st0,
      StateOf ins0 flops0 st0 ->
      InjectionReady st0 (ins1 :: List.map (fun _ => nil) mprocs) ins1 flops0.
    Hypothesis Hflops: forall st1,
      StateOf ins1 flops0 st1 ->
      InjectionReady st1 (nil :: flops1) ins1 flops1.

    Lemma TrsI_equiv: forall st0,
      StateOf ins0 flops0 st0 -> forall st1,
      StateOf ins1 flops0 st1 <-> TrsI st0 st1 ins1.
    Proof.
      intros st0 Hstate st1.
      exact (injection_equiv (Hinputs Hstate) st1).
    Qed.

    Lemma TrsC_equiv: forall st0,
      StateOf ins1 flops0 st0 -> forall st1,
      StateOf ins1 flops1 st1 <-> TrsC st0 st1 flops1.
    Proof.
      intros st0 Hstate st1.
      exact (injection_equiv (Hflops Hstate) st1).
    Qed.

    Theorem stf_implies_std: forall stf00,
      StateOf ins0 flops0 stf00 -> forall stf11,
      StateOf ins1 flops1 stf11 ->
      exists stf10, TrsI stf00 stf10 ins1 /\ TrsC stf10 stf11 flops1.
    Proof.
      intros stf00 Hstart stf11 Hfinish.
      destruct (Hinputs Hstart) as [_ [stf10 Hslot]].
      assert (Hmid: StateOf ins1 flops0 stf10).
      { apply (proj2 (TrsI_equiv Hstart stf10)); exact Hslot. }
      exists stf10; split; [exact Hslot|].
      apply (proj1 (TrsC_equiv Hmid stf11)); exact Hfinish.
    Qed.

    Theorem std_implies_stf: forall stf00,
      StateOf ins0 flops0 stf00 -> forall stf10,
      TrsI stf00 stf10 ins1 -> forall stf11,
      TrsC stf10 stf11 flops1 -> StateOf ins1 flops1 stf11.
    Proof.
      intros stf00 Hstart stf10 Hi stf11 Hc.
      pose proof (proj2 (TrsI_equiv Hstart stf10) Hi) as Hmid.
      exact (proj2 (TrsC_equiv Hmid stf11) Hc).
    Qed.

    (** [TrsC] injects the supplied flop values; it does not execute [clkR].
     * Consequently this theorem equates stabilization results and makes no
     * claim that the injected values were computed by [TrsF]. *)
    Theorem stf_std_equiv: forall stf00,
      StateOf ins0 flops0 stf00 -> forall stf11,
      StateOf ins1 flops1 stf11 <->
      (exists stf10, TrsI stf00 stf10 ins1 /\ TrsC stf10 stf11 flops1).
    Proof.
      intros stf00 Hstart stf11; split.
      - apply stf_implies_std; exact Hstart.
      - intros [stf10 [Hi Hc]]. eapply std_implies_stf; eassumption.
    Qed.

    (** A computed-next-flop claim is available when the injected values have
     * separately been justified by a source transition. *)
    Corollary stf_std_equiv_computed:
      TrsF ins1 flops0 flops1 -> forall stf00,
      StateOf ins0 flops0 stf00 -> forall stf11,
      (StateOf ins1 flops1 stf11 /\ TrsF ins1 flops0 flops1) <->
      (exists stf10, TrsI stf00 stf10 ins1 /\ TrsC stf10 stf11 flops1).
    Proof.
      intros Hcomputed stf00 Hstart stf11.
      pose proof (stf_std_equiv Hstart stf11). tauto.
    Qed.
  End InjectionEquiv.
End StfStd.
