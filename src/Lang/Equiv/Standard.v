Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Analysis Lang.Syntax Lang.Semantics.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section ListMap.
  Context {A B: Type}.
  Variable (f: A -> list B).
  Fixpoint list_map (al: list A): list B :=
    match al with
    | nil => nil
    | cons a al' => (f a) ++ (list_map al')
    end.
End ListMap.

Section Standard.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Definition Value := hmap.
  Definition State := Value.

  Inductive EvalUnit :=
  | EvalUnitAlways (isComb: bool) (stmt: @VStatementItem vid_t)
  | EvalUnitAssign (lv e: @VExpr vid_t)
  | EvalUnitModuleIns (mins: @VModuleIns vid_t)
  | EvalUnitInputClk.

  Inductive Event: Set :=
  | EventClkPosedge: Event
  | EventUpd (upds: State): Event
  | EventEval (forActive: bool) (cpos: hpath) (eunit: EvalUnit): Event.

  (* Definition MRel := State -> Event -> State -> State -> Prop. *)

  (* Record MTrsExt := *)
  (*   { mtrs_mod: @VModuleDecl vid_t; *)
  (*     mtrs_mtrs: MTrs; *)
  (*     mtrs_mrel: MRel; *)
  (*   }. *)

  (* Definition MTrssExt := TrsFMap MTrsExt. *)

  Section WithDeclFuncs.
    Variables (decls: Decls) (funcs: Funcs).
    Variable (mtrss: MTrss).

    Definition stvu := vid_t.

    (** Sensitivity list *)
    Section StvList.
      Variable cpos: hpath.

      Definition getStvListP (p: hpath): list stvu :=
        match hpathTop p with
        | Some v => [v]
        | _ => nil
        end.

      Fixpoint getSLExpr (e: @VExpr vid_t): list stvu :=
        match e with
        | VExprPriLiteral pl => nil
        | VExprId vid => match declfind decls cpos vid with
                         | Sret p => getStvListP p
                         | Fail _ => nil
                         end
        | VExprHier pe ce => getSLExpr pe
        | VExprPriSelect se ie => getSLExpr se
        | VExprPriSelectConstRange se le re => getSLExpr se
        | VExprPriSelectIdxRangeAdd se le re => getSLExpr se
        | VExprPriSelectIdxRangeSub se le re => getSLExpr se
        | VExprPriConcat es => list_map getSLExpr es
        | VExprPriMultConcat ne ces => (getSLExpr ne) ++ (list_map getSLExpr ces)
        | VExprTfCall tfid aes => list_map getSLExpr aes
        | VExprSystemTfCall tf aes => list_map getSLExpr aes
        | VExprCast sze e => (getSLExpr sze) ++ (getSLExpr e)
        | VExprUniOp op e => getSLExpr e
        | VExprIncOrDec iod => nil
        | VExprBinOp op le re => (getSLExpr le) ++ (getSLExpr re)
        | VExprCond ce te fe => (getSLExpr ce) ++ (getSLExpr te) ++ (getSLExpr fe)
        | VExprInside ie res => (getSLExpr ie) ++ (list_map getSLExpr res)
        end.

      (** Standard 9.2.2.2.1 Implicit always_comb sensitivities *)

      Section StatementCase.
        Variables
          (forReads: bool)
            (ef: @VExpr vid_t -> list stvu)
            (sf: @VStatementItem vid_t -> list stvu).

        Fixpoint getSLStatementCase (css: list (@VCaseItem vid_t (@VStatementItem vid_t)))
          : list stvu :=
          match css with
          | nil => nil
          | cons cs css' => (match cs with
                             | VCaseItemCase _ ce st =>
                                 (if forReads then ef ce else nil) ++ (sf st)
                             | VCaseItemDefault _ st => sf st
                             end) ++ (getSLStatementCase css')
          end.
      End StatementCase.

      Section StatementSeq.
        Variable (sf: @VStatementItem vid_t -> list stvu).

        Fixpoint getSLStatementSeq (stis: list (@VStatementItem vid_t))
          : list stvu :=
          match stis with
          | nil => nil
          | cons sti stis' => (sf sti) ++ (getSLStatementSeq stis')
          end.
      End StatementSeq.

      Fixpoint getSLStatementReads (sti: @VStatementItem vid_t): list stvu :=
        match sti with
        | VStatementItemBlockingAssignNormal lv e => getSLExpr e
        | VStatementItemNonblockingAssign lv e => getSLExpr e
        | VStatementCase cty ce css =>
            (getSLExpr ce)
              ++ (getSLStatementCase true getSLExpr getSLStatementReads css)
        | VStatementCond ce tsti ofsti =>
            (getSLExpr ce)
              ++ (match tsti with
                  | Some tst => getSLStatementReads tst
                  | _ => nil
                  end)
              ++ (match ofsti with
                  | Some (Some fst) => getSLStatementReads fst
                  | _ => nil
                  end)
        | VStatementItemReturn re => getSLExpr re
        | VStatementProcTimingControl tc psti => getSLStatementReads psti
        | VStatementSeqBlock stis => getSLStatementSeq getSLStatementReads stis
        | _ => nil (* not supported *)
        end.

      Fixpoint getSLStatementWrites (sti: @VStatementItem vid_t): list stvu :=
        match sti with
        | VStatementItemBlockingAssignNormal lv e => getSLExpr lv
        | VStatementItemNonblockingAssign lv e => getSLExpr lv
        | VStatementCase cty ce css =>
            getSLStatementCase false getSLExpr getSLStatementWrites css
        | VStatementCond ce tsti ofsti =>
            (match tsti with
             | Some tst => getSLStatementWrites tst
             | _ => nil
             end)
              ++ (match ofsti with
                  | Some (Some fst) => getSLStatementWrites fst
                  | _ => nil
                  end)
        | VStatementItemReturn re => nil
        | VStatementProcTimingControl tc psti => getSLStatementWrites psti
        | VStatementSeqBlock stis => getSLStatementSeq getSLStatementWrites stis
        | _ => nil (* not supported *)
        end.

      Definition getSLStatement (sti: @VStatementItem vid_t): list stvu :=
        List.filter (fun p => List.existsb (vid_eqb p) (getSLStatementWrites sti))
          (getSLStatementReads sti).

      Definition getSLModuleInsMInput (ivids: list vid_t) (npc: @VNamedPortConn vid_t): list stvu :=
        match npc with
        | VNamedPortConnI vid => if List.existsb (vid_eqb vid) ivids
                                 then match declfind decls cpos vid with
                                      | Sret p => getStvListP p
                                      | Fail _ => nil
                                      end
                                 else nil
        | VNamedPortConnE vid ie => if List.existsb (vid_eqb vid) ivids
                                    then (getSLExpr ie)
                                    else nil
        | VNamedPortConnW => nil
        end.

      Fixpoint getSLModuleInsMInputs (ivids: list vid_t) (npcs: @VNamedPortConns vid_t): list stvu :=
        match npcs with
        | VNamedPortConnsOne npc => getSLModuleInsMInput ivids npc
        | VNamedPortConnsCons npc npcs' =>
            (getSLModuleInsMInput ivids npc) ++ (getSLModuleInsMInputs ivids npcs')
        end.

      Definition getSLModuleInsMOutput (ovids: list vid_t) (npc: @VNamedPortConn vid_t): list stvu :=
        match npc with
        | VNamedPortConnI vid => if List.existsb (vid_eqb vid) ovids
                                 then match declfind decls cpos vid with
                                      | Sret p => getStvListP p
                                      | Fail _ => nil
                                      end
                                 else nil
        | VNamedPortConnE vid ie => if List.existsb (vid_eqb vid) ovids
                                    then (getSLExpr ie)
                                    else nil
        | VNamedPortConnW => nil
        end.

      Fixpoint getSLModuleInsMOutputs (ovids: list vid_t) (npcs: @VNamedPortConns vid_t): list stvu :=
        match npcs with
        | VNamedPortConnsOne npc => getSLModuleInsMOutput ovids npc
        | VNamedPortConnsCons npc npcs' =>
            (getSLModuleInsMOutput ovids npc) ++ (getSLModuleInsMOutputs ovids npcs')
        end.

      Definition getSLModuleIns (mins: @VModuleIns vid_t): list stvu :=
        match mins with
        | VModuleInsOne mid params (VHierInsOne iid (VPortConnsNamed npcs)) =>
            match mtrss mid with
            | Sret mtrs => getSLModuleInsMInputs mtrs.(mtrs_input_vids) npcs
            | Fail _ => nil
            end
        end.

      Definition getWritesModuleIns (mins: @VModuleIns vid_t): list stvu :=
        match mins with
        | VModuleInsOne mid params (VHierInsOne iid (VPortConnsNamed npcs)) =>
            match mtrss mid with
            | Sret mtrs => getSLModuleInsMOutputs mtrs.(mtrs_input_vids) npcs
            | Fail _ => nil
            end
        end.

    End StvList.

    Section Process.

      Record Trigger: Set :=
        { trig_stv: list stvu;
          trig_clk: bool;
        }.

      Definition TrigNone: Trigger :=
        {| trig_stv := nil; trig_clk := false |}.

      Definition TrigStv (stv: list stvu): Trigger :=
        {| trig_stv := stv; trig_clk := false |}.

      Definition TrigClk: Trigger :=
        {| trig_stv := nil; trig_clk := true |}.

      Definition TrigStvClk (stv: list stvu): Trigger :=
        {| trig_stv := stv; trig_clk := true |}.

      Record Process: Set :=
        { proc_trig: Trigger;
          proc_pos: hpath;
          proc_evu: EvalUnit }.

      Definition Processes := list Process.

      Section OnCurPos.
        Variable cpos: hpath.

        Definition getProcsVidExpr (vid: vid_t) (e: @VExpr vid_t): Processes :=
          [{| proc_trig := TrigStv (getSLExpr cpos e);
             proc_pos := cpos;
             proc_evu := EvalUnitAssign (VExprId vid) e |}].

        Definition getProcsNetDeclAssign (nda: @VNetDeclAssign vid_t): Processes :=
          match nda with
          | VNetDeclAssignOne vid oe => match oe with
                                        | Some e => getProcsVidExpr vid e
                                        | None => nil
                                        end
          end.

        Fixpoint getProcsNetDeclAssigns (ndas: @VNetDeclAssigns vid_t): Processes :=
          match ndas with
          | VNetDeclAssignsOne nda => getProcsNetDeclAssign nda
          | VNetDeclAssignsCons nda ndas' => (getProcsNetDeclAssign nda) ++ (getProcsNetDeclAssigns ndas')
          end.

        Definition getProcsVarDeclAssign (vda: @VVarDeclAssign vid_t): Processes :=
          match vda with
          | VVarDeclAssignVar vid vd oe => match oe with
                                           | Some e => getProcsVidExpr vid e
                                           | None => nil
                                           end
          end.

        Fixpoint getProcsVarDeclAssigns (vdas: @VVarDeclAssigns vid_t): Processes :=
          match vdas with
          | VVarDeclAssignsOne vda => getProcsVarDeclAssign vda
          | VVarDeclAssignsCons vda vdas' => (getProcsVarDeclAssign vda) ++ (getProcsVarDeclAssigns vdas')
          end.

        Definition getProcsParamAssign (pa: @VParamAssign vid_t): Processes :=
          match pa with
          | VParamAssignOne vid (VConstParamExprMinTypMax e) => getProcsVidExpr vid e
          end.

        Fixpoint getProcsParamAssigns (pas: @VParamAssigns vid_t): Processes :=
          match pas with
          | VParamAssignsOne pa => getProcsParamAssign pa
          | VParamAssignsCons pa pas' => (getProcsParamAssign pa) ++ (getProcsParamAssigns pas')
          end.

        Definition getProcsPkgGenItemDecl (pgid: @VPkgGenItemDecl vid_t): Processes :=
          match pgid with
          | VPkgGenItemDeclNet (VNetDeclOne nt pd ndas) => getProcsNetDeclAssigns ndas
          | VPkgGenItemDeclData (VDataDeclVarDecl (VVarDeclOne dt vdas)) => getProcsVarDeclAssigns vdas
          | VPkgGenItemDeclTask td => nil
          | VPkgGenItemDeclFunc fd => nil
          | VPkgGenItemDeclParam (VParamDeclData dti pas) => getProcsParamAssigns pas
          | VPkgGenItemDeclLocalParam (VLocalParamDeclOne dti pas) => getProcsParamAssigns pas
          end.

        Definition getProcsAssign (a: @VAssign vid_t): Processes :=
          match a with
          | VAssignO lv e => [{| proc_trig := TrigStv (getSLExpr cpos e);
                                proc_pos := cpos;
                                proc_evu := EvalUnitAssign lv e |}]
          end.

        Fixpoint getProcsAssigns (cass: @VAssigns vid_t): Processes :=
          match cass with
          | VAssignsOne a => getProcsAssign a
          | VAssignsCons a cass' => (getProcsAssign a) ++ (getProcsAssigns cass')
          end.

        Definition getProcsModuleCommonItem (mci: @VModuleCommonItem vid_t): Processes :=
          match mci with
          | VModuleCommonItemDecl (VModuleGenItemDeclPkg pgid) => getProcsPkgGenItemDecl pgid
          | VModuleCommonItemAssert cca => nil
          | VModuleCommonItemContAssign (VContAssignNet cass) => getProcsAssigns cass
          | VModuleCommonItemInitial stmt => nil
          | VModuleCommonItemAlways akwd (VStatementO sti) =>
              [{| proc_trig := match akwd with
                               | VAlwaysComb => TrigStv (getSLStatement cpos sti)
                               | _ => TrigClk
                               end;
                 proc_pos := cpos;
                 proc_evu := EvalUnitAlways (match akwd with
                                             | VAlwaysComb => true
                                             | _ => false
                                             end) sti |}]
          end.

        Definition getProcsMGenItem (mgi: @VModuleOrGenerateItem vid_t): Processes :=
          match mgi with
          | VModuleOrGenerateItemIns mins => [{| proc_trig := TrigStvClk (getSLModuleIns cpos mins);
                                                proc_pos := cpos;
                                                proc_evu := EvalUnitModuleIns mins |}]
          | VModuleOrGenerateItemCommon mci => getProcsModuleCommonItem mci
          end.

      End OnCurPos.

      Section GenModuleItems.
        Variable (gmif: @VGenerateModuleItem vid_t -> Processes).

        Fixpoint getProcsGenerateModuleItems (gmis: list (@VGenerateModuleItem vid_t)): Processes :=
          match gmis with
          | nil => nil
          | gmi :: gmis' => (gmif gmi) ++ (getProcsGenerateModuleItems gmis')
          end.
      End GenModuleItems.

      Fixpoint getProcsGenerateModuleItem (cpos: hpath) (gmi: @VGenerateModuleItem vid_t): Processes :=
        match gmi with
        | VGenerateModuleItemCond ce tgmi ofgmi => nil
        | VGenerateModuleItemBlock gmis => getProcsGenerateModuleItems (getProcsGenerateModuleItem cpos) gmis
        | VGenerateModuleItemModule mgi => getProcsMGenItem cpos mgi
        end.

      Definition getProcsNonPortModuleItem (pnp: @VNonPortModuleItem vid_t): Processes :=
        match pnp with
        | VNonPortGeneratedModuleIns (VGeneratedModuleInsO gmi) => getProcsGenerateModuleItem nil gmi
        | VNonPortModuleOrGenerateItem mgi => getProcsMGenItem nil mgi
        end.

      Definition getProcsModuleItem (mitem: @VModuleItem vid_t): Processes :=
        match mitem with
        | VModuleItemPortDecl pdec => nil
        | VModuleItemNonPort pnp => getProcsNonPortModuleItem pnp
        end.

      Fixpoint getProcsModuleItems (mitems: @VModuleItems vid_t): Processes :=
        match mitems with
        | VModuleItemsOne mitem => getProcsModuleItem mitem
        | VModuleItemsCons mitem mitems' => (getProcsModuleItem mitem) ++ (getProcsModuleItems mitems')
        end.

      Definition getProcsParamDecl (pdecl: @VParamDecl vid_t): Processes :=
        match pdecl with
        | VParamDeclData dti pas => getProcsParamAssigns nil pas
        end.

      Fixpoint getProcsParamPorts (pports: @VParamPorts vid_t): Processes :=
        match pports with
        | VParamPortsNil => nil
        | VParamPortsOne pdecl => getProcsParamDecl pdecl
        | VParamPortsCons pdecl spports => (getProcsParamDecl pdecl) ++ (getProcsParamPorts spports)
        end.

      Definition getProcInputClk: Process :=
        {| proc_trig := TrigNone;
          proc_pos := nil;
          proc_evu := EvalUnitInputClk |}.

      Definition getProcs (m: @VModuleDecl vid_t): Processes :=
        match m with
        | VModuleDeclAnsi mn pports pdecls mitems =>
            getProcInputClk :: (getProcsParamPorts pports) ++ (getProcsModuleItems mitems)
        end.

    End Process.

    (** Region:
     * Each process has a scheduled event (in this region) or nothing scheduled.
     * In other words, no two events can be scheduled for the same unit.
     * This is to ensure the execution ordering within the same unit.
     * Not enforcing this execution order trivially results in spurious behavior.
     *
     * The standard document does not explicitly specify this, but a related, similar rule is
     * provided in Section 4.6 Determinism. *)
    Definition Region := list (option Event). (* <-- aligned with Processes for the target module. *)

    (** Generate evaluation events for a given update event. *)
    Definition genEvalEvent (tev: Event) (proc: Process): option Event :=
      match tev with
      | EventUpd upds => if (List.existsb (fun v => match hfind [HEltVid v] upds with
                                                    | Some _ => true
                                                    | _ => false
                                                    end) (trig_stv (proc_trig proc)))
                         then Some (EventEval true (proc_pos proc) (proc_evu proc))
                         else None
      | EventClkPosedge => if (trig_clk (proc_trig proc))
                           then Some (EventEval false (proc_pos proc) (proc_evu proc))
                           else None
      | _ => None
      end.

    Inductive GenEvalEvents (tev: Event): Processes -> Region -> Region -> Prop :=
    | GenEvalEventsNil: GenEvalEvents tev nil nil nil
    | GenEvalEventsStepNone:
      forall proc poev noev,
        genEvalEvent tev proc = noev ->
        forall procs preg nreg,
          GenEvalEvents tev procs preg nreg ->
          GenEvalEvents tev (proc :: procs) (poev :: preg) (match noev with
                                                            | Some nev => Some nev
                                                            | None => poev
                                                            end :: nreg).

    Section WithProcs.
      Variable procs: Processes.

      (** Standard 4.3 Event simulation
       *   ..
       *   Every change in state of a net or variable in the system description being simulated is
       * considered an update event.
       *   ..
       *   Processes are sensitive to update events. When an update event is executed, all the
       * processes that are sensitive to that event are considered for evaluation in an arbitrary
       * order. The evaluation of a process is also an event, known as an evaluation event.
       *
       * NOTE: no preemption to avoid the known defect in the standard semantics.
       *)

      Definition execEvalEvent (s0: State) (cpos: hpath) (evu: EvalUnit): trsOk (State * State) :=
        match evu with
        | EvalUnitAlways isComb stmt =>
            match trsVStatementItem decls funcs [] cpos s0 isComb stmt [] with
            | Sret (uacts, unbas, retv) => Sret (uacts, unbas)
            | Fail f => Fail f
            end
        | EvalUnitAssign lv e =>
            match (pty <- lvposfind decls funcs cpos s0 [] lv;
                   v <- evalExpr decls funcs cpos s0 [] e;
                   trsVAssignV lv v pty) with
            | Sret uacts => Sret (uacts, [])
            | Fail f => Fail f
            end
        | EvalUnitModuleIns mins => trsVModuleIns decls funcs [] cpos s0 mtrss mins
        | EvalUnitInputClk =>
            (* Placeholder for input-update events; thus ignore its execution. *)
            (* Fail TrsNotSupported *)
            Sret ([], [])
        end.

      Inductive ExecEventRegion: option Event -> Region -> option Event -> Region -> Prop :=
      | ExecEventRegionStep:
        forall region region1 ev region2,
          region = region1 ++ ev :: region2 ->
          forall nregion nev,
            nregion = region1 ++ nev :: region2 ->
            ExecEventRegion ev region nev nregion.

      Definition EventUpdClk (ev: Event): Prop :=
        match ev with
        | EventClkPosedge => True
        | EventUpd upd => upd <> []
        | _ => False
        end.

      Definition eventUpdate (s: State) (ev: Event): State :=
        match ev with
        | EventUpd upd => hupds s upd
        | _ => s
        end.

      (* NOTE: a practical assumption (from the coding guidelines) is made that no mixed use of
       * blocking and nonblocking assignments. *)
      Inductive ExecEvent:
        State -> (* current state *)
        Region -> Region -> (* current active/NBA regions *)
        State -> (* next state *)
        Region -> Region -> (* next active/NBA regions *)
        Prop :=
      | ExecEventUpdClk: forall procs1 s1 act11 act12 nbas proc ev procs2 s2 act21 act22,
          GenEvalEvents ev procs1 act11 act21 ->
          GenEvalEvents ev procs2 act12 act22 ->
          procs = procs1 ++ proc :: procs2 ->
          s2 = eventUpdate s1 ev ->
          EventUpdClk ev ->
          ExecEvent s1 (act11 ++ Some ev :: act12) nbas s2 (act21 ++ None :: act22) nbas
      | ExecEventEvalActive: forall s1 act nact nba cpos evu uacts unbas,
          execEvalEvent s1 cpos evu = Sret (uacts, unbas) ->
          ExecEventRegion (Some (EventEval true cpos evu)) act (Some (EventUpd uacts)) nact ->
          ExecEvent s1 act nba s1 nact nba
      | ExecEventEvalNBA: forall s1 act nact nba nnba cpos evu curNba uacts unbas,
          execEvalEvent s1 cpos evu = Sret (uacts, unbas) ->
          ExecEventRegion (Some (EventEval false cpos evu)) act None nact ->
          ExecEventRegion curNba nba (Some (EventUpd unbas)) nnba ->
          ExecEvent s1 act nba s1 nact nnba.

      Inductive ExecEvents:
        State -> (* current state *)
        Region -> Region -> (* current active/NBA regions *)
        State -> (* next state *)
        Region -> Region -> (* next active/NBA regions *)
        Prop :=
      | ExecEventsNil: forall s act nba, ExecEvents s act nba s act nba
      | ExecEventsStep:
        forall s0 act0 nba0 s1 act1 nba1,
          ExecEvent s0 act0 nba0 s1 act1 nba1 ->
          forall s2 act2 nba2,
            ExecEvents s1 act1 nba1 s2 act2 nba2 ->
            ExecEvents s0 act0 nba0 s2 act2 nba2.

      Definition nilR: Region := List.map (fun _ => None) procs.

      Definition InitState := list (vid_t * Value).

      Definition initsR (inits: list InitState): Region :=
        List.map (fun init => match init with
                              | nil => None
                              | _ => Some (EventUpd (HMapStr init))
                              end) inits.

      Definition inputsR (inputs: InitState): Region :=
        initsR (inputs :: (List.map (fun _ => nil) (tl procs))).

      Definition flopsR (flops: list InitState): Region :=
        initsR (nil :: flops).

      Definition clkR: Region :=
        match nilR with
        | _ :: tlR => Some EventClkPosedge :: tlR
        | nil => nil
        end.

      (* execute_region { *)
      (*     while (region is nonempty) { *)
      (*         E = any event from region; *)
      (*         remove E from the region; *)
      (*         if (E is an update event) { *)
      (*             update the modified object; *)
      (*             schedule evaluation event for any process sensitive to the object; *)
      (*         } else { /* E is an evaluation event */ *)
      (*             evaluate the process associated with the event and possibly *)
      (*             schedule further events for execution; *)
      (*         } *)
      (*     } *)
      (* } *)
      Definition ExecActiveRegion
        (s1: State) (* current state *)
        (act: Region) (* current active region, to be executed exhaustively *)
        (s2: State) (* resulting state after executing the active region *)
        (nba: Region) (* newly scheduled NBA region while executing active region *)
        : Prop :=
        ExecEvents s1 act nilR s2 nilR nba.

      (* execute_time_slot {
       *     while (any region in {Active, NBA} is nonempty) {
       *         execute_region (Active);
       *         R = first nonempty region in {Active, NBA};
       *         if (R is nonempty)
       *             move events in R to the Active region;
       *     }
       * }
       *)
      Inductive ExecTimeSlot: State -> (* current state *)
                              Region -> (* Active region *)
                              Region -> (* NBA region *)
                              State -> (* next state *)
                              Prop :=
      | ExecTimeSlotEmpty: forall s, ExecTimeSlot s nilR nilR s
      | ExecTimeSlotActive:
        forall acts,
          acts <> nilR ->
          forall s0 s1 nbas,
            ExecActiveRegion s0 acts s1 nbas ->
            forall s2,
              ExecTimeSlot s1 nilR nbas s2 ->
              ExecTimeSlot s0 acts nilR s2
      | ExecTimeSlotNBA:
        forall s0 nbas s1,
          nbas <> nilR ->
          ExecTimeSlot s0 nbas nilR s1 ->
          ExecTimeSlot s0 nilR nbas s1.

      (** Predicates *)

      (** The equivalence proof starts with one update slot per process and an
       * empty NBA region. Arbitrary regions can contain unscheduled evaluation
       * events, have the wrong length, or have both regions nonempty. *)
      Definition NbaFree: Prop :=
        forall s1 inits s2 nba,
          List.length inits = List.length procs ->
          ExecActiveRegion s1 (initsR inits) s2 nba ->
          nba = nilR.

      Definition ExecTimeSlotProg: Prop :=
        forall s1 inits,
          List.length inits = List.length procs ->
          exists s2, ExecTimeSlot s1 (initsR inits) nilR s2.

      Definition StdOk: Prop :=
        NbaFree /\ ExecTimeSlotProg.

    End WithProcs.

  End WithDeclFuncs.

  Section Facts.
    Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

    Lemma initsR_no_clk:
      forall inits, Forall (fun oe => oe <> Some EventClkPosedge) (initsR inits).
    Proof using .
      unfold initsR; intros.
      apply Forall_forall; intros.
      apply in_map_iff in H3.
      destruct H3 as [init [? ?]]; subst.
      destruct init; discriminate.
    Qed.

    Lemma Forall2_app_length_inv:
      forall A B (R: A -> B -> Prop) al1 al2 bl1 bl2,
        Forall2 R (al1 ++ al2) (bl1 ++ bl2) ->
        length al1 = length bl1 ->
        Forall2 R al1 bl1 /\ Forall2 R al2 bl2.
    Proof using .
      induction al1; simpl; intros.
      - destruct bl1; [|discriminate].
        split; [constructor; fail|].
        assumption.
      - destruct bl1; [discriminate|].
        simpl in *.
        inv H3; inv H4.
        specialize (IHal1 _ _ _ H10 H5); dest.
        split; [|assumption].
        constructor; assumption.
    Qed.

    Lemma getProcs_not_nil:
      forall m, getProcs decls mtrss m <> nil.
    Proof using .
      destruct m; simpl; intros; discriminate.
    Qed.

    Lemma ExecTimeSlot_nilR_inv:
      forall procs s1 s2,
        ExecTimeSlot decls funcs mtrss procs s1 (nilR procs) (nilR procs) s2 ->
        s1 = s2.
    Proof using .
      intros procs s1 s2 Hets.
      inv Hets.
      - reflexivity.
      - elim H3; reflexivity.
      - elim H3; reflexivity.
    Qed.

    Lemma ExecTimeSlot_act_nilR_inv:
      forall procs nba s1 s2,
        ExecTimeSlot decls funcs mtrss procs s1 (nilR procs) nba s2 ->
        ExecTimeSlot decls funcs mtrss procs s1 nba (nilR procs) s2.
    Proof using .
      intros procs nba s1 s2 Hets.
      inv Hets.
      - constructor.
      - elim H3; reflexivity.
      - assumption.
    Qed.

    Lemma ExecTimeSlot_nba_nilR_inv:
      forall procs act s1 s2,
        ExecTimeSlot decls funcs mtrss procs s1 act (nilR procs) s2 ->
        exists si nbas,
          ExecActiveRegion decls funcs mtrss procs s1 act si nbas /\
            ExecTimeSlot decls funcs mtrss procs si (nilR procs) nbas s2.
    Proof using .
      intros act procs s1 s2 Hets.
      inv Hets.
      - exists s2, (nilR act); split; constructor.
      - exists s3, nbas.
        split; assumption.
      - elim H3; reflexivity.
    Qed.

    Lemma genEvalEvent_Some:
      forall upds proc nev,
        genEvalEvent (EventUpd upds) proc = Some nev ->
        nev = EventEval true (proc_pos proc) (proc_evu proc).
    Proof using .
      unfold genEvalEvent; intros.
      find_if_inside.
      - congruence.
      - discriminate.
    Qed.

    Lemma genEvalEvent_None:
      forall upds proc,
        genEvalEvent (EventUpd upds) proc = None ->
        Forall (fun v => match hfind [HEltVid v] upds with
                         | Some _ => False
                         | None => True
                         end) (trig_stv (proc_trig proc)).
    Proof using .
      unfold genEvalEvent; intros.
      destruct (existsb _ _) eqn:Heb; [discriminate|].
      clear -Heb.
      induction (trig_stv (proc_trig proc)).
      - constructor.
      - apply Bool.orb_false_elim in Heb; dest.
        constructor.
        + destruct (hfind [HEltVid a] upds); [discriminate|auto].
        + apply IHl; assumption.
    Qed.

    Lemma GenEvalEvents_length:
      forall ev procs act1 act2,
        GenEvalEvents ev procs act1 act2 ->
        length procs = length act1 /\ length procs = length act2.
    Proof using .
      induction 1; simpl; intros; dest; [intuition|].
      rewrite <-H5, <-H6; intuition.
    Qed.

    (** Update-only initial regions cannot schedule NBA evaluation events. *)
    Lemma ExecEventRegion_in : forall ev act nev nact,
      ExecEventRegion ev act nev nact -> In ev act.
    Proof.
      intros ev act nev nact Hregion; destruct Hregion; subst.
      apply in_or_app; right; left; reflexivity.
    Qed.

    Lemma ExecEvent_has_event : forall procs s act nba s' act' nba',
      ExecEvent decls funcs mtrss procs s act nba s' act' nba' ->
      exists ev, In (Some ev) act.
    Proof.
      intros procs s act nba s' act' nba' Hexec; destruct Hexec.
      - exists ev; apply in_or_app; right; left; reflexivity.
      - eexists; eapply ExecEventRegion_in; eassumption.
      - eexists; eapply ExecEventRegion_in; eassumption.
    Qed.

    Lemma ExecEvent_nilR_false : forall procs s nba s' act' nba',
      ExecEvent decls funcs mtrss procs s (nilR procs) nba s' act' nba' -> False.
    Proof.
      intros procs s nba s' act' nba' Hexec.
      destruct (ExecEvent_has_event Hexec) as [ev Hin].
      apply in_map_iff in Hin; destruct Hin as [proc [Heq _]]; discriminate.
    Qed.

    Definition ActiveOnly (oe : option Event) : Prop :=
      match oe with
      | None | Some (EventUpd _) | Some (EventEval true _ _) => True
      | _ => False
      end.

    Lemma region_active_only : forall ev act nev nact,
      ExecEventRegion ev act nev nact ->
      Forall ActiveOnly act -> ActiveOnly ev /\
        (ActiveOnly nev -> Forall ActiveOnly nact).
    Proof.
      intros ev act nev nact Hex Hact.
      destruct Hex as [region region1 ev region2 Heq nregion nev Hneq].
      subst region nregion.
      apply Forall_app in Hact; destruct Hact as [Hpre Htail].
      inversion Htail; subst.
      split; [assumption|].
      intros Hnev; apply Forall_app; split; [assumption|].
      constructor; assumption.
    Qed.

    Lemma gen_update_active_only : forall upd procs act nact,
      GenEvalEvents (EventUpd upd) procs act nact ->
      Forall ActiveOnly act -> Forall ActiveOnly nact.
    Proof.
      intros upd procs act nact Hgen; induction Hgen; intros Hact.
      - constructor.
      - inversion Hact; subst.
        constructor; [|apply IHHgen; assumption].
        destruct (genEvalEvent (EventUpd upd) proc) as [nev|] eqn:HgenEv; [|assumption].
        apply genEvalEvent_Some in HgenEv; subst nev; exact I.
    Qed.

    Lemma exec_event_active_only : forall procs s act nba s' act' nba',
      ExecEvent decls funcs mtrss procs s act nba s' act' nba' ->
      Forall ActiveOnly act ->
      Forall ActiveOnly act' /\ nba' = nba.
    Proof.
      intros procs s act nba s' act' nba' Hexec; destruct Hexec; intros Hact.
      - apply Forall_app in Hact; destruct Hact as [Hpre Htail].
        inversion Htail; subst.
        destruct ev; simpl in *; try contradiction.
        split; [|reflexivity].
        apply Forall_app; split.
        + eapply gen_update_active_only; eassumption.
        + constructor; [exact I|].
          eapply gen_update_active_only; eassumption.
      - split; [|reflexivity].
        eapply region_active_only in H4; [|eassumption].
        apply H4; exact I.
      - eapply region_active_only in H4; [|eassumption].
        destruct H4 as [Hfalse _]; contradiction.
    Qed.

    Lemma exec_events_active_only : forall procs s act nba s' act' nba',
      ExecEvents decls funcs mtrss procs s act nba s' act' nba' ->
      Forall ActiveOnly act -> nba' = nba.
    Proof.
      intros procs s act nba s' act' nba' Hexec; induction Hexec; intros Hact.
      - reflexivity.
      - apply exec_event_active_only in H3; [|assumption].
        destruct H3 as [Hact1 Hnba1].
        rewrite (IHHexec Hact1); assumption.
    Qed.

    Lemma initsR_active_only : forall inits,
      Forall ActiveOnly (initsR inits).
    Proof.
      intros inits; unfold initsR; apply Forall_forall.
      intros oe Hin; apply in_map_iff in Hin.
      destruct Hin as [init [Heq _]]; subst oe.
      destruct init; exact I.
    Qed.

    Lemma NbaFree_inits : forall procs,
      NbaFree decls funcs mtrss procs.
    Proof.
      intros procs s inits s' nba Hlen Hexec.
      unfold ExecActiveRegion in Hexec.
      eapply exec_events_active_only; [exact Hexec|].
      apply initsR_active_only.
    Qed.

    Lemma ExecTimeSlot_inits_events : forall procs s inits s',
      ExecTimeSlot decls funcs mtrss procs s (initsR inits) (nilR procs) s' ->
      ExecEvents decls funcs mtrss procs s (initsR inits) (nilR procs)
        s' (nilR procs) (nilR procs).
    Proof.
      intros procs s inits s' Hslot.
      apply ExecTimeSlot_nba_nilR_inv in Hslot.
      destruct Hslot as [si [nba [Hactive Hnext]]].
      assert (Hnba: nba = nilR procs).
      { eapply exec_events_active_only; [exact Hactive|apply initsR_active_only]. }
      subst nba. apply ExecTimeSlot_nilR_inv in Hnext. subst si.
      exact Hactive.
    Qed.

    Lemma ExecTimeSlot_inits_invariant : forall procs (Inv: State -> Region -> Prop),
      (forall s act s' act',
        Inv s act ->
        ExecEvent decls funcs mtrss procs s act (nilR procs)
          s' act' (nilR procs) -> Inv s' act') ->
      forall s inits s',
        Inv s (initsR inits) ->
        ExecTimeSlot decls funcs mtrss procs s (initsR inits) (nilR procs) s' ->
        Inv s' (nilR procs).
    Proof.
      intros procs Inv Hstep.
      assert (Hpres: forall s act nba s' act' nba',
        ExecEvents decls funcs mtrss procs s act nba s' act' nba' ->
        Forall ActiveOnly act -> nba = nilR procs -> Inv s act -> Inv s' act').
      { intros s act nba s' act' nba' Hrun; induction Hrun;
          intros Hact Hnba Hinv; [exact Hinv|].
        pose proof (exec_event_active_only H3 Hact) as [Hact1 Hnba1].
        subst nba0 nba1.
        apply IHHrun; [exact Hact1|reflexivity|].
        eapply Hstep; eassumption. }
      intros s inits s' Hinit Hslot.
      apply ExecTimeSlot_inits_events in Hslot.
      eapply Hpres; [exact Hslot|apply initsR_active_only|reflexivity|exact Hinit].
    Qed.

  End Facts.

End Standard.
