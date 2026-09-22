Revamping Verilog Semantics for Foundational Verification
=========================================================

Getting Started
---------------

This artifact contains the Rocq (Coq) development accompanying the paper *Revamping Verilog Semantics for Foundational Verification*.

### Directory Content

- `src`: Core framework and case study
  + `Lib`: General-purpose libraries used in the framework
  + `Lang`: Formal syntax and semantics of Verilog (*corresponds to Section 3 of the paper*)
    * `Equiv`: Equivalence between the standard and our semantics (*Section 4*)
  + `Ex`: Total correctness of a RISC-V pipelined processor (*Section 5*)
- `dep`: External dependencies (this artifact already includes all the files; i.e., no need to run `git pull`)
  + `coqutil`: Various data structures and utility lemmas, from https://github.com/mit-plv/coqutil
  + `FreeSim`: The FreeSim library mentioned in the paper
	* We made minor modifications to make it compatible with Coq 8.18.
	* The original version is available at: https://github.com/CCR-project/FreeSim
  + `riscv-coq`: Specification of RISC-V, from https://github.com/mit-plv/riscv-coq

### Requirements

- Make
- OCaml Package Manager (`opam`)
- GMP development files (`libgmp-dev` on Debian/Ubuntu)

This branch targets Rocq 9.0.1 through its `coq` compatibility package and uses OCaml 4.14.4.

### Build Instructions

From the top-level directory, run the following commands. They use a dedicated `verilrocq-9.0` switch and leave the currently selected switch unchanged.

1. `opam switch create verilrocq-9.0 ocaml-base-compiler.4.14.4 --no-switch`
2. `opam repo add --switch=verilrocq-9.0 coq-released https://coq.inria.fr/opam/released`
3. `opam pin add --switch=verilrocq-9.0 -n coq-freesim.1.0.0 ./dep/FreeSim`
4. `opam exec --switch=verilrocq-9.0 --set-switch -- make builddep`: respond with yes (Y) to the following prompts.
   - "Package coq-verilog-builddep does not exist, create as a NEW package? [Y/n]"
   - "Do you want to continue? [Y/n]"
5. `opam exec --switch=verilrocq-9.0 -- make clean`
6. `opam exec --switch=verilrocq-9.0 -- make -j$(nproc)`

Run `make clean` through the selected switch whenever changing Coq/Rocq versions, because compiled `.vo` files are version-specific.

Run on an Apple M2 Pro with 16GB RAM, the full proof check takes about 4 minutes; we do not expect it to take more than 10 minutes.


Proof Artifact Structure
------------------------

We provide the main correspondences between our paper and the artifact source code.

### Section 3. Formal Semantics of Verilog as a Transition Function

- 3.2 Syntax: `src/Lang/Syntax.v`
  + Fig. 2. Formal syntax of Verilog (excerpts)
    * Expressions: `VExpr` in `Syntax.v`:L128
    * L-values: `VLValue` in `Syntax.v`:L189
    * Event expressions: `VEventExpr` in `Syntax.v`:L230
    * Statements: `VStatement` in `Syntax.v`:L541
    * Blocks: `VModuleOrGenerateItem` in `Syntax.v`:L784
    * Generate blocks: `VModuleItems` in `Syntax.v`:L842
    * Modules: `VModuleDecl` in `Syntax.v`:L862

- 3.3 Semantic Domain: `src/Lib/HMap.v`
  + Hierarchical maps: `hmap` in `HMap.v`:L64

- 3.4 Semantic Transfer Function: `src/Lang/Semantics.v`
  + Fig. 3. Semantics for expressions, L-values, and statements (excerpts)
    * Expressions: `evalExpr` in `Semantics.v`:L292
    * L-values: `lvposfind` in `Semantics.v`:L348
    * Statements: `trsVStatementItem` in `Semantics.v`:L468
  + Fig. 4. Semantics for blocks and generate-blocks (excerpts)
    * Blocks: `trsVModuleOrGenerateItem` in `Semantics.v`:L655
    * Generate blocks: `trsVModuleItems` in `Semantics.v`:L712
  + Fig. 5. Semantics for modules
    * Modules: `trsVModuleDecl` in `Semantics.v`:L735

- 3.5 State-Transition Function: `src/Lang/Semantics.v`
  + Least fixed point of a semantic transfer function: `trsM_iff_rep` in `Semantics.v`:L745
    * As stated in the paper: "to define and use the function, the user must provide a proof that the fixpoint computation terminates."
  + State-update function: `trsM_IFF` in `Semantics.v`:L769
  + State-transition function: `trsT` in `Semantics.v`:L782

### Section 4. Equivalence Between the Standard and Our Semantics

The equivalence proof in this branch is in `src/Lang/Equiv/*.v`.

- `executable_clock_equiv` in `ClockEquivalence.v` relates the fixed point of the module's executable `trsVModuleDecl` evaluator, followed by `trsNext`, to an input time slot followed by a clock time slot in `Standard.v`. `ExecutableTrsF` merges the computed updates with the old registers, preserving fields left unwritten. The theorem derives the next flop bindings and their transition relation.
- `flat_module_lfp` and `flat_module_rep` in `ModuleBridge.v` connect `TrsProcsRep` to the evaluator's `LFP` and finite `trsM_iff_rep` iterations. The `FlatModule` fragment permits ports, always blocks, single identifier continuous assignments, single uninitialized net/variable declarations, assertions, and instances. Parameter ports and generate blocks are outside this fragment.
- The hypotheses are `ModuleWf` and `ClockWf`. `ModuleWf` supplies the update graph, its ordering and dependency conditions, and the input/flop domains. `ClockWf` checks local sampling, disjoint update slots, validity of the merged next register state, and an `UpdateCompletion` witness. Clocked processes currently require nonempty update-binding lists; a binding can contain `HMapEmpty` to preserve its old value. These conditions have not been derived for every module covered by the paper's source-level guidelines.
- `module_process_settled` derives each process's active-state stability from `ModuleWf` and a source fixed point. `module_clock_plan` and `clock_wf_of_outputs` use this result to construct the sampling plan from local NBA outputs, so combinational stability need not be supplied as another hypothesis.
- `completion_slot_iff` in `UpdateCompletion.v` proves that partial updates and their completed register values have the same time-slot executions. Its witness checks sensitivity keys, update effects, and domain preservation under individual updates and process outputs. The scheduling equivalence follows from these local checks.
- `ClockSampling.v` proves that every completed clock active region produces the sampled NBA updates. `NbaSameSlot` in `Standard.v` places each update in its originating process's NBA slot, preventing one process from overwriting another process's pending update.
- `ClockExamples.v` constructs both well-formedness witnesses for two registers with `q <= r` and `r <= q`, applies `executable_clock_equiv`, and proves that every completed clock time slot swaps their values.
- `AssumptionExamples.v` constructs `ModuleWf` and `ClockWf` for `always_ff @(posedge clk) if (en) q <= d` and applies the general executable equivalence theorem. For every completed clock schedule, `en = 0` retains `q` and `en = 1` loads `d`; input changes are also covered. It includes regressions for `always_comb` sensitivity extraction.
- `MixedExamples.v` constructs both witnesses for `always_comb y = q; always_ff @(posedge clk) q <= d`, derives its clock sampling plan, and applies `executable_clock_equiv`. Its clock-result theorem includes the combinational evaluation after the NBA update: both `q` and `y` become `d`.

The graph is ordered by whole processes. This is stricter than an acyclic signal dependency graph. `GroupedCombinationalChain` in `AssumptionExamples.v` has `always_comb begin x = a; z = y; end` and `always_comb y = x`. Its signal dependencies form `a -> x -> y -> z`, but its process graph admits no rank. The executable evaluator also remains at the input-only seed for every iteration count: the missing `y` causes the first block to fail and discard its partial result for `x`. Supporting this case requires a change to block evaluation or a proved normalization of blocks.

`IndexedRead` checks the sensitivity and process-success conditions for `y = a[i]`. Sensitivity extraction includes index reads and separates them from lvalue writes; instance write extraction uses output-port metadata. Packed bit writes have a separate evaluator limitation: the proved `packed_bit_update_ignored` example shows that the current merge leaves `q` unchanged for `q[0] <= 1` when `q` is represented by `HMapBits`. Both semantics share this update evaluator, so their equivalence does not by itself establish the evaluator's agreement with IEEE Verilog for such writes.

The supporting stabilization theorem `stf_std_equiv` in `StfStd.v` compares states after supplied input and flop injections. Confluence is proved through update graphs by `eval_ugraph_confl_state_eq` in `UpdGraph.v`.

### Section 5. Modular Verification of a Pipelined RISC-V Processor

- 5.2 Verilog Module Behavior in ITree: `src/Lang/ModuleITree.v`
  + Theorem 5.1 (Determinism): `src/Lang/ModuleITree.v`:L142
- 5.3 Formal Specification of RISC-V: `src/Ex/RvCore/FormalSpec.v`
- 5.4 Pipelined Processor Implementation: `src/Ex/RvCore/Core.v`
- 5.5 Behavioral Refinement Between `P_{impl}` and `S_{riscv}`
  + Theorem 5.2 (Adequacy)
    * This theorem is stated and proven in the external `FreeSim` library.
    * We use the theorem in our end-to-end proof in `src/Ex/RvCore/EndToEnd.v`:L80.
  + End-to-end theorem: `Theorem core_follow_riscv_formal` in `src/Ex/RvCore/EndToEnd.v`:L47


Reusability Guide
-----------------

- The main reusable part of the artifact is the formal syntax and semantics of Verilog.
- Users may want to design Verilog modules and define their state-transition functions by following the examples in `src/Ex/RvCore/Mem.v`. For example:
  + `ICache.M.m` contains a Verilog module definition, supported by rich notation provided by the framework.
  + `ICache.mtrs` defines the state-transition function for the module.
