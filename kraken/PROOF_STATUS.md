# Planner proof status

Read [Theorems/PlannerModel.lean](Theorems/PlannerModel.lean),
[Theorems/PlannerAssembly.lean](Theorems/PlannerAssembly.lean), then
[Theorems/Main.lean](Theorems/Main.lean). These files contain the review
definitions and proofs. Shared input, encoding, and memory definitions stay in
separate files because the implementation proofs also use them.
The entry point is the C++ method `Planner::run`. `Shuffle::run` is outside
these claims. The review definitions are in `Theorems/`; assembly proofs are in
`FlatShuffler/`; correspondence proofs are in `ShufflerBridge/`.

The general correspondence covers plans, blocked results, and model errors.
Normal returns permit only Done or Blocked. A model error uses the separate
assertion-exit outcome. That outcome reaches external `exit` with argument 1;
the proof stops before the external implementation runs.

The normal-return theorem adds two sufficient input conditions: each target value
is junk, can be generated, is in the source, or is spilled; and the target has no
more function return labels than the source. It excludes assertion exit but still
permits Blocked. The size, encoding, memory, and register assumptions still apply.

`Shuffler.Planner.run_correct` also proves that each returned plan matches the
target. Its trace type proves legal abstract operations from the source stack.
`planner_assembly_returns_correct_plan_or_blocked` transfers this claim to the
output stack and operations. Target wildcards accept any value. Loads use the
final spill set. These claims do not prove spill-memory contents, EVM execution,
optimality, or that Blocked means no plan exists.

The general postcondition transfer uses `PlannerResultMatchesModel` to state which
observations match the Lean result. It applies to every property that holds for all
observations admitted by that comparison. The no-assertion corollary uses this
transfer with `planner_model_correct`. It adds no assembly instruction proof.
Error text, a final high-level error state, padding, and unused buffer tails are
outside the comparison. The spill comparison covers input source and target
variables only. See `Theorems/PlannerModel.lean` for each outcome's comparison.

The proof assembly is generated from `c/shuffler/stack/Shuffler.cpp` and contains
the production C++ methods. Test wrappers are compiled separately. The C harness
only links the methods for tests and byte checks; it is outside the proved code.
Instruction and layout checks connect the parsed assembly and recorded binary
host to method bytes. This connection, compiler correctness, hardware behavior,
external `exit`, and agreement with Solidity are outside the Lean proof.

`lake build` checks the full composition. `test/modules_test.sh` checks the public
interfaces and invalid input cases. `test/axioms_test.sh` audits all listed final
and transfer theorems and tests the audit's rejection cases. The audit permits
`propext`, `Classical.choice`, `Quot.sound`, and generated `bv_decide` verifier-result
axioms. It checks the latter's names and types; their results remain trusted axioms.
It rejects holes, user axioms, and `native_decide` axioms. Commands are in `README.md`.
Run each Lean check one process at a time.
