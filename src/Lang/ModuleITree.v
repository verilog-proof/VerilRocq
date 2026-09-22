From Stdlib Require Import Streams.Streams Program.Equality.
Require Import Lib.Common Lib.HMap.
Require Import Lang.Semantics.
From ExtLib Require Import Monad.
From FreeSim Require Import ModSemE Behavior Any STS.
From ITree Require Import ITree ITreeFacts.
From Paco Require Import paco.


Section ModuleITree.
  Context `{vid_ops}.

  Definition InputT := State.
  Definition OutputT := State.
  Definition StateT := State.
  
  (* Module's input/output events. *)
  Inductive moduleE : Type -> Type :=
  | Input : moduleE InputT
  | Output : OutputT -> moduleE unit.

  Definition Transition : Type := InputT -> StateT -> (StateT * OutputT).

  (* An auxiliary internal tree to define recursive calls. 
    Note that module always have outputs but we regard it as observable output events
    only if the `output_valid` predicate returns true.*)
  Definition module_itree_body (trs : Transition) (state : StateT) 
    : itree (callE StateT void +' moduleE +' eventE) void :=
    input <- trigger Input ;; (* Receive input *)
    '(next_state, output) <- Ret (trs input state) ;; (* Calculate the next state & output *)
    trigger (Output output) ;;; (* Emit output *)
    call next_state. (* Recursive call for the next cycle. *)

  (* Module as a dtree (itree with nondeterminism). *)
  Definition module_itree (trs : Transition) (state : StateT) (* the register states *) 
    : itree (moduleE +' eventE) void :=
      rec (module_itree_body trs) state.

  Definition filter_io_handler (fixed_input : InputT) (output_valid : OutputT -> bool) : (moduleE +' eventE) ~> itree (moduleE +' eventE)
    := (fun _ e => match e with
       | inl1 module_event => match module_event with 
          | Input => Ret fixed_input (* Return fixed_input for any input events. *)
          | Output o => (* Filter out invalid output events. *)
            (if (output_valid o) then trigger (Output o) else Ret tt)
        end
       | inr1 o => trigger o (* other events are passed through. *)
    end).
    
  Definition filter_io (fixed_input : InputT) (output_valid : OutputT -> bool) (I : itree (moduleE +' eventE) void) : itree (moduleE +' eventE) void :=
    interp (filter_io_handler fixed_input output_valid) I.
    
End ModuleITree.



Section Properties.
  From FreeSim Require Import ModSem. (* Should be imported here to avoid notation issues. *)
  Context `{vid_ops}.
  Context {CONF : EMSConfig}.
  
  (* We convert `moduleE` events to `eventE` syscalls. *)
  Definition moduleE_to_syscalls : (moduleE +' eventE) ~> itree eventE
    := (fun _ e => match e with
       | inl1 module_event => match module_event with 
          | Input => 
              input <- trigger (Choose InputT) ;;
              trigger (SyscallIn input↑) ;;; 
              Ret input
          | Output o =>
              trigger (SyscallOut "output_pc" o↑ (fun _ => True)) ;;;
              Ret tt
          end
       | inr1 o => trigger o
    end).
  
  (* When defining input events, we intentionally rule out the inputs for in-running traces that end with `Tr.nb`. *)
  CoInductive input_events: Stream (option Any.t) -> Tr.t -> Prop :=
  | input_events_in rv tl ins 
      (IND: input_events ins tl) :
        input_events (Cons (Some rv) ins) (Tr.cons (event_in rv) tl)
  | input_events_out fn args tl ins
      (IND: input_events ins tl) : 
        input_events ins (Tr.cons (event_out fn args) tl)
  | input_events_done rv :
        input_events (Streams.const None) (Tr.done rv)
  | input_events_spin :
        input_events (Streams.const None) Tr.spin
  | input_events_ub l :
        input_events l Tr.ub.
  
  Definition with_syscalls M s : itree eventE Any.t :=
    let I := (interp moduleE_to_syscalls (module_itree M s)) in
      ITree.map (fun v : void => match v return Any.t with end) I.
  
  Definition module_semantics M s : semantics :=
    (ModSemL.compile_itree (with_syscalls M s)).
  
  (* We coinductively define equlity for traces. *)
  Inductive _trace_eq (trace_eq: Tr.t -> Tr.t -> Prop) : Tr.t -> Tr.t -> Prop :=
  | _trace_eq_ret : forall v, 
        _trace_eq trace_eq (Tr.done v) (Tr.done v)
  | _trace_eq_spin :
        _trace_eq trace_eq (Tr.spin) (Tr.spin)
  | _trace_eq_ub :
        _trace_eq trace_eq (Tr.ub) (Tr.ub)
  | _trace_eq_nb :
        _trace_eq trace_eq (Tr.nb) (Tr.nb)
  | _trace_eq_cons : forall ev tr1 tr2 (R : trace_eq tr1 tr2 : Prop),
        _trace_eq trace_eq (Tr.cons ev tr1) (Tr.cons ev tr2).
  Hint Constructors _trace_eq : core.
  
  Definition trace_eq tr1 tr2 := paco2 _trace_eq bot2 tr1 tr2.
  Hint Unfold trace_eq : core.
  Lemma trace_eq_mon: monotone2 _trace_eq. Proof. pmonauto. Qed.
  Hint Resolve trace_eq_mon : paco.
    
  Lemma with_syscalls_unfold_one M state :
    with_syscalls M state =
        input <- trigger (Choose InputT) ;;
        trigger (SyscallIn input↑) ;;;
        tau;; tau;;
        let res := M input state in
        trigger (SyscallOut "output_pc" (snd res)↑ (fun _ => True)) ;;;
        tau;; tau;; tau;;
        (with_syscalls M (fst res)).
  Proof.
    apply bisim_is_eq.
    unfold with_syscalls, ITree.map, module_itree, rec, mrec.
    revert state. cofix CIH. intros state.
    pstep. red. cbn. apply EqVis. intros input. red. left.
    pstep. red. cbn. apply EqVis. intros u. red. left.
    do 2(pstep; red; cbn; apply EqTau; left).
    rewrite 2!subst_bind, !bind_ret_l. destruct (M input state). cbn.
    pstep. red. cbn. apply EqVis. left.
    rewrite !subst_bind, !bind_ret_l.
    do 3(pstep; red; cbn; apply EqTau; left).

    rewrite !subst_bind, bind_ret_r.
    apply eq_is_bisim. reflexivity.
  Qed.
  
  Theorem determinism M s tr1 tr2 inputs :
    Beh.of_program (module_semantics M s) tr1 ->
    Beh.of_program (module_semantics M s) tr2 ->
    input_events inputs tr1 ->
    input_events inputs tr2 ->
    trace_eq tr1 tr2.
  Proof.
    intros beh1 beh2 Hinputs1 Hinputs2.
    unfold Beh.of_program in beh1, beh2.
    assert (exists s', s' = s) as [s' Hs']. { eexists; reflexivity. }
    replace (initial_state (module_semantics M s)) with (with_syscalls M s') in beh1, beh2 by (rewrite Hs'; reflexivity).
    clear Hs'.
    punfold beh1. punfold beh2.
    revert_until s. pcofix CIH.
    intros. subst.
    
    (* First event: Choose Input (demonic). *)
    inversion beh1; subst. 1,4,6: try discriminate SRT; discriminate FINAL. 
    { (* Fail: beh1 = sb_spin. *)
      pinversion SPIN. { discriminate SRT. } clear SRT SPIN.
      (* The initial state is demonic (before Choose InputT) but the next state (before SyscallIn) does not spin. *)
      destruct STEP as (? & ? & STEP & [SPIN | FALSE]); [|destruct FALSE].
      cbn in STEP. rewrite with_syscalls_unfold_one, bind_trigger in STEP. cbn in STEP. dependent destruction STEP.
      pinversion SPIN; discriminate SRT. }
    { (* Fail: beh1 = sb_nb. *) inversion Hinputs1. }
    (* Success: beh1 = sb_demonic. *)
    clear SRT beh1. destruct STEP as (? & ? & STEP & -> & beh1). unnw.
    cbn in STEP. rewrite with_syscalls_unfold_one, bind_trigger in STEP. cbn in STEP. dependent destruction STEP.
    (* Repeat for beh2. *)
    inversion beh2; subst. 1,4,6: try discriminate SRT; discriminate FINAL. 
    { pinversion SPIN. { discriminate SRT. } clear SRT SPIN.
      destruct STEP as (? & ? & STEP & [SPIN | FALSE]); [|destruct FALSE].
      cbn in STEP. rewrite with_syscalls_unfold_one, bind_trigger in STEP. cbn in STEP. dependent destruction STEP. 
      pinversion SPIN; discriminate SRT. }
    { inversion Hinputs2. }
    clear SRT beh2. destruct STEP as (? & ? & STEP & -> & beh2). unnw.
    cbn in STEP. rewrite with_syscalls_unfold_one, bind_trigger in STEP. cbn in STEP. dependent destruction STEP.
    
    (* A simple tactic for automating the above process of program stepping. *)
    #[local] Ltac auto_step beh :=
      inversion beh; subst; 
      try match goal with SRT: state_sort _ _ = _|- _ => discriminate SRT end;
      try match goal with NB: input_events _ Tr.nb |- _ => inversion NB end;
      [ match goal with SPIN: Beh.state_spin _ _ |- _ =>
          repeat (punfold SPIN; destruct SPIN as [SRT STEP | _ STEP ]; [discriminate SRT|]; destruct STEP as (? & ? & STEP & [SPIN | FALSE]); [|destruct FALSE];
                apply ModSemL.step_tau_iff in STEP as [? ?]; subst);
          punfold SPIN; destruct SPIN as [SRT _|SRT STEP]; try discriminate SRT
        end | ].
    
    (* Second event: SyscallIn (vis). *)
    auto_step beh1.
    clear SRT beh1. destruct TL as [beh1 | F]; [|destruct F]. punfold beh1. 
    cbn in STEP. rewrite bind_trigger in STEP. dependent destruction STEP.
    auto_step beh2.
    clear SRT beh2. destruct TL as [beh2 | F]; [|destruct F]. punfold beh2. 
    cbn in STEP. rewrite bind_trigger in STEP. dependent destruction STEP.
    (* Unify the input values. *)
    inversion Hinputs1; subst. clear Hinputs1; rename IND into Hinputs1.
    inversion Hinputs2; subst. rename H4 into INPUT_EQ. clear Hinputs2; rename IND into Hinputs2.
    apply Any.upcast_inj in INPUT_EQ as [_ <-%JMeq_eq].
    
    (* 3rd&4th event: tau (demonic). *)
    do 2(auto_step beh1;
      clear SRT beh1; destruct STEP as (? & ? & STEP & -> & beh1); unnw; apply ModSemL.step_tau_iff in STEP as [_ HH]; subst).
    do 2(auto_step beh2;
      clear SRT beh2; destruct STEP as (? & ? & STEP & -> & beh2); unnw; apply ModSemL.step_tau_iff in STEP as [_ HH]; subst).
        
    (* 5th event: SyscallOut (vis). *)
    auto_step beh1.
    clear SRT beh1. destruct TL as [beh1 | F]; [|destruct F]. punfold beh1.
    cbn in STEP. rewrite bind_trigger in STEP. dependent destruction STEP.
    auto_step beh2.
    clear SRT beh2. destruct TL as [beh2 | F]; [|destruct F]. punfold beh2.
    cbn in STEP. rewrite bind_trigger in STEP. dependent destruction STEP.
    (* Unify the input streams. *)
    inversion Hinputs1; subst. clear Hinputs1; rename IND into Hinputs1.
    inversion Hinputs2; subst. clear Hinputs2; rename IND into Hinputs2.
    
    (* 6,7,8th event: tau *)
    do 3(auto_step beh1;
    [ clear SRT; destruct STEP as (? & ? & STEP & [SPIN | FALSE]); [|destruct FALSE];
      cbn in STEP; rewrite with_syscalls_unfold_one, bind_trigger in STEP; cbn in STEP; dependent destruction STEP;
      pinversion SPIN; discriminate SRT|];
    clear SRT beh1; destruct STEP as (? & ? & STEP & -> & beh1); unnw; apply ModSemL.step_tau_iff in STEP as [_ HH]; subst).
    
    do 3(auto_step beh2;
    [ clear SRT; destruct STEP as (? & ? & STEP & [SPIN | FALSE]); [|destruct FALSE];
      cbn in STEP; rewrite with_syscalls_unfold_one, bind_trigger in STEP; cbn in STEP; dependent destruction STEP;
      pinversion SPIN; discriminate SRT|];
    clear SRT beh2; destruct STEP as (? & ? & STEP & -> & beh2); unnw; apply ModSemL.step_tau_iff in STEP as [_ HH]; subst).
    
    pstep. econstructor. left.
    pstep. econstructor. right. eapply CIH; eassumption.
  Qed.
  
End Properties.
