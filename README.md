# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Proof audit

Read these Lean files in order:

1. [PlannerModel.lean](kraken/Theorems/PlannerModel.lean): correctness of the actual
   Lean planner, input conditions, result comparison, and agreement with the flat model.
2. [PlannerAssembly.lean](kraken/Theorems/PlannerAssembly.lean): machine conditions,
   memory effects, and the connection to the instruction proof.
3. [Main.lean](kraken/Theorems/Main.lean): assembly/model agreement, exclusion of
   assertion exit, property transfer, and correctness on success.

The supporting definitions are in [PlannerInput.lean](kraken/Theorems/PlannerInput.lean),
[ValueEncoding.lean](kraken/Theorems/ValueEncoding.lean), and
[NativeInterface.lean](kraken/Theorems/NativeInterface.lean). The implementation
proofs use these definitions, so they must precede the review theorems.

The main claims are:

- `planner_model_correct` proves that the actual Lean planner returns a plan or
  Blocked. Each returned plan matches the target and contains a legal abstract trace.
- `planner_assembly_returns_correct_plan_or_blocked` transfers that result to
  assembly and excludes assertion exit.
- `planner_assembly_transfers_model_postcondition` transfers any property of the
  results covered by the model comparison to the assembly contract.
- `planner_assembly_returns_normally` excludes assertion exit for valid planner
  inputs. It follows from the transfer and `planner_model_correct`.
- `planner_assembly_matches_model` also covers input errors and requires an
  assertion exit to match a model error.

The assembly claims also have binary forms. `Shuffler.Planner.run_correct` is the
theorem over the top-level Lean model. Target wildcards accept any value. Loads
use the final spill set. The claims do not prove spill-memory contents, EVM
execution, plan optimality, or that Blocked means no plan exists.

Valid inputs require each target value to be junk, freely generated, in the source,
or spilled, and require enough source function return labels. Size, encoding,
memory, and register conditions also apply. Blocked results remain possible.
The Lean files in `kraken/Theorems/` contain the review definitions and their proofs.
`kraken/FlatShuffler/` contains the models and assembly proofs.
`kraken/ShufflerBridge/` contains the correspondence proofs for emission, spills,
and the planner.
Import `Theorems.Main` from a Lean file that starts with `module`.

## Development

Run `nix develop` for the proof and C++ toolchains. With a separate installation,
use [elan](https://github.com/leanprover/elan), CMake, Ninja, and GCC 15.3.0.

Run `lake update` once after checkout.
The pinned Kraken dependency is used without source changes.
Fetch the Mathlib cache with `MATHLIB_CACHE_FROM=forks lake exe cache get`.

Then run `lake build` to check all proofs.
The build includes the Shuffler model, assembly proofs, correspondence proofs,
and their composition in `Theorems.Main`.
Lake uses CMake to generate `build/kraken/c/build_bottom_up.S` from the C++23
shuffler source before it checks the assembly proofs. CMake checks the source
and header dependencies on each build. The assembly is a build output and is
not kept in source control. It contains the C++ methods used by the proofs.
The test harnesses and fuzzer use `build/kraken/c/test_wrappers.S`.
The build checks that both files contain the same C++ method bodies.
Both Lake packages use the root `lean-toolchain` (`nightly-2026-10-20`).
Mathlib is pinned to a commit of its nightly testing repository for that compiler.

Both local packages treat compiler warnings as errors. Warnings from the pinned
Kraken dependency remain visible; they do not fail the local proof build.

`Theorems.Main` combines two proof modules through contracts over shared flat
data. Kraken and Shuffler implementation imports stay private. A file that
imports this combined theorem must start with `module` to retain that boundary.
The model and machine imports stay separate because Batteries and Kraken both
define `List.allSome`.
The public predicates have types over the shared data and keep their bodies private.
Run `kraken/test/modules_test.sh` to check the boundary.
It also checks the transfer interfaces, normal-return status bounds, and rejection
of inputs that lack available target values or source function return labels.

The assembly parser reads `build/kraken/c/build_bottom_up.S`. The binary checks
read the C++ method bytes from `build/kraken/c/bbu_harness`, which links those
methods for the buildBottomUp tests. The C test driver and test wrappers are
outside the proved code. `kraken/test/bin_check.sh` compares the parsed instructions
with the method bytes. `kraken/test/bin_layout.sh --check` checks the recorded
instruction layout used by `FlatShuffler/BinHost.lean`. The Lean theorem does not
itself extract or decode executable bytes.

Run `lake test` to run the property tests.
Run `kraken/test/axioms_test.sh` to audit the final theorems and test the audit.
The Lean CI job also runs the assembly, layout, and model comparison checks in
`kraken/test/`. The Fuzz job builds and tests the C FFI with the same Lean compiler.

From the repository root, build and test the C++ shuffler with CMake:

```
cmake -S . -B build -G Ninja
cmake --build build
ctest --test-dir build --output-on-failure
```

CMake writes `build/compile_commands.json` for clangd. It contains the C++23 build
settings for the shuffler and its tests. Test programs are in `build/kraken/c/`.

## Differential fuzzing

`Fuzz/fuzz.cpp` is a fuzz target that runs `buildMapping`, `removeSurplus`, `permute`,
`permuteAtLowestHeight`, `buildBottomUp`, `Emission.run` and `Planner.run` of the C++ shuffler from
the `solidity` submodule and of the Lean model on the same case, and aborts when the results differ.
It calls the Lean model through the Lean C FFI. Every input decodes to a case. Except for
`Planner.run`, every case satisfies the preconditions of the function under test. A `Planner.run`
case can have a target variable that is not on the source stack and not spilled, or more function
return labels in the target than in the source. For these cases the results must also be the same.
The case language is described in `Fuzz/Oracle.lean`.

The fuzz target also runs the port in `kraken/c` on each case that it has a unit for, and aborts
when the port result differs from the Lean model result. It links the asm
`build/kraken/c/test_wrappers.S`. `Fuzz/build.sh` generates it with CMake and checks
its C++ method bodies against the proof assembly. `Fuzz/port.cpp` converts a case to
the C interface of the port, and has one entry in `units` for each port function.
For `buildBottomUp`, the comparison omits the final destinations, which its C interface does not give.

The port runs each check in a child process so that an assembly assertion can
return `err` to the fuzzer. This adds a process start for each port check.
The fuzzer binds the assembly's external `exit` call to `_Exit` in that child
to avoid libFuzzer's exit handler.

Build and run with libFuzzer:

```
git submodule update --init solidity
nix develop -c Fuzz/build.sh build/fuzz
mkdir -p build/corpus
build/fuzz/fuzz -fork=8 -ignore_crashes=1 -len_control=0 -max_len=512 -max_total_time=600 build/corpus
```

`-len_control=0` is necessary: with short inputs every decoded choice is the lowest one. Without it,
a fault put into `removeSurplus` was not found in 3 minutes. `-fork` with `-ignore_crashes`
continues after a difference.

Build and run with AFL++:

```
nix develop -c sh -c 'CC=afl-clang-fast CXX=afl-clang-fast++ Fuzz/build.sh build/afl'
mkdir -p build/afl-in && printf '\0' > build/afl-in/seed
AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 nix develop -c afl-fuzz -i build/afl-in -o build/afl-out -- build/afl/fuzz
```

Both builds replay an input file and print `port <tab> case <tab> port <tab> lean` for a difference
of the port and the model, and `solc <tab> case <tab> c++ <tab> lean` for a difference of solc and
the model:

```
build/fuzz/fuzz build/afl-out/default/crashes/<file>
```

`Fuzz/build.sh` also runs `port_test` (the port against fixed model results) and `Fuzz/ci_test.sh`.
`Fuzz/ci.sh <build-dir> <seconds> [jobs]` fuzzes on `jobs` cores (default: all) and prints the
difference of each crash. It exits with 1 if there is a port difference or a crash without a
difference line, with 2 if each crash is a solc difference, and with 0 if there is no crash.

CI (`.github/workflows/fuzz.yml`) runs `Fuzz/ci.sh`: 30 minutes for each push to `main` and 2 minutes
for other pushes and pull requests, with the corpus kept in the Actions cache. A difference fails the
job and the inputs are uploaded as the `fuzz-crashes` artifact.
