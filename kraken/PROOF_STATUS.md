# Planner proof status

The proof boundary is the C++ method `Planner::run`. The assertion-exit proofs pass.

## Interfaces

`Bbu.plan_correct` uses `Unit.PlannerRunThm` on `plannerRunAsm`.
`Bbu.plan_binary_correct` uses the same contract in the binary host.
`PlanBridge.plan_correct` connects that method contract to `Shuffler.Planner.run`.
`PlanBridge.plan_binary_correct` gives the same connection in the binary host.

`PlanBridge.Input` contains a planner, its wildcard strategy, and the initial state.
Its result is a status and state. There is no test-wrapper error word or argument-rejection result.
The Shuffler connection requires canonical slots and initial dropped bytes that are zero,
as required by the planner model. The method contract supplies the buffer ownership and sizes.
The bridge does not assume that target slots are available; assertion cases remain covered.

The C++ `Status` and `Resolution` types have no assertion-failure value. Failed assertions call
`exit(1)`. The flat model retains `.assertionFailed` as an abstract error outcome, which the
assembly exit contract connects to `exit(1)`. Normal resolve results exclude assertion failure.

The assembly input is generated directly from `c/shuffler/stack/Shuffler.cpp`.
It contains 28 C++ methods and no test wrappers. Tests and fuzzing compile `test_wrappers.cpp`
separately. `test/assembly_interfaces_test.sh` checks that both builds contain the same C++
method bodies. The binary layout and instruction checks cover only those methods.

The wrapper assembly proofs and their input-rejection contracts have been removed.
The shared byte-array and vector lemmas are in `Unit/Memory.lean` and `Unit/VectorLemmas.lean`.
The production method contracts still cover assertion exits and normal returns.

## Checks for this change

- Full Lean build, including `PlanBridge.Final`: passed (3685 build jobs).
- `lake test` and public import checks: passed.
- Axiom audit of all 15 final theorems and the audit's negative tests: passed.
- CMake configuration, C++ build, and all three CTest tests: passed, including the sanitizer suite.
- Fuzzer port build and fixed-result tests: passed.
- Equality of the C++ method bodies in the proof and test builds: passed.
- The assembly check rejects an added C symbol, a changed method body, and an empty input.
- The new inconsistent-mapping regression requires `exit(1)` and passes.
- Assembly generation, compiler failure, dependency, and proof-cache tests: passed.
- Binary instruction checks, binary layout, struct layout, field generation, and label tests: passed.
- Pop, surplus, lowest-height, and planner model comparisons: passed. The planner comparison
  covers 409376 cases and 409376 cases with the wildcard strategy changed.

All Lean checks use `LEAN_NUM_THREADS=1` and `nice`.
The Kraken dependency is unchanged. No proof holes, user axioms, or heartbeat increases were added.
