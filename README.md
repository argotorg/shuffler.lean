# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Run `LEAN_NUM_THREADS=1 nice lake update` once after checkout.
The pinned Kraken dependency is used without source changes.
Fetch the Mathlib cache with `MATHLIB_CACHE_FROM=forks nice lake exe cache get`.

Then run `LEAN_NUM_THREADS=1 nice lake build` to check all proofs.
The build includes the Shuffler model, assembly proofs, correspondence proofs,
and their composition in `PlanBridge.Final`.
Both Lake packages use the root `lean-toolchain` (`nightly-2026-10-20`).
Mathlib is pinned to a commit of its nightly testing repository for that compiler.

Both local packages treat compiler warnings as errors. Warnings from the pinned
Kraken dependency remain visible; they do not fail the local proof build.

`PlanBridge.Final` combines two proof modules through contracts over shared flat
data. Kraken and Shuffler implementation imports stay private. A file that
imports this combined theorem must start with `module` to retain that boundary.
The public predicates have types over the shared data and keep their bodies private.
Run `LEAN_NUM_THREADS=1 nice kraken/test/modules_test.sh` to check the boundary.

Run `LEAN_NUM_THREADS=1 nice lake test` to run the property tests.
Run `LEAN_NUM_THREADS=1 nice kraken/test/axioms_test.sh` to audit the final theorems and test the audit.
The Lean CI job also runs the assembly, layout, and model comparison checks in
`kraken/test/`. The Fuzz job builds and tests the C FFI with the same Lean compiler.

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
`kraken/c/build_bottom_up.S`, not a new compilation of the C++. `Fuzz/port.cpp` converts a case to
the C interface of the port, and has one entry in `units` for each unit of the port (now:
`buildBottomUp`, without the final destinations, which the C interface does not give). The other
kinds are checked against solc only.

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
