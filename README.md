# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Then run `lake build` to compile the project.

Run `lake test` to run the property tests.

## Differential fuzzing

`Fuzz/fuzz.cpp` is a fuzz target that runs `buildMapping`, `removeSurplus`, `permute`,
`permuteAtLowestHeight`, `buildBottomUp`, `Emission.run` and `Planner.run` of the C++ shuffler from
the `solidity` submodule and of the Lean model on the same case, and aborts when the results differ.
It calls the Lean model through the Lean C FFI. Every input decodes to a case. Except for
`Planner.run`, every case satisfies the preconditions of the function under test. A `Planner.run`
case can have a target variable that is not on the source stack and not spilled, or more function
return labels in the target than in the source. For these cases the results must also be the same.
The case language is described in `Fuzz/Oracle.lean`.

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

Both builds replay an input file and print `case <tab> c++ <tab> lean` for a difference:

```
build/fuzz/fuzz build/afl-out/default/crashes/<file>
```
