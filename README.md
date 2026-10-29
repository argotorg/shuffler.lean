# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Then run `lake build` to compile the project.

Run `lake test` to run the property tests.

## Differential fuzzing

`Fuzz/fuzz.cpp` is a fuzz target that runs `buildMapping`, `removeSurplus`, `permute` and
`buildBottomUp` of the C++ shuffler from the `solidity` submodule and of the Lean model on the same
case, and aborts when the results differ. It calls the Lean model through the Lean C FFI. Every input
decodes to a valid case. The case language is described in `Fuzz/Oracle.lean`.

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

Known differences. Every difference found so far has equal values on the stack or a function return
label `R`:

- On stacks with equal values, Lean `permute` and `buildBottomUp` emit swaps that C++ does not emit,
  report a different blocked slot, or are blocked where C++ is not. Lean `permute` does not regroup
  equal values. `permute;v0 v0;1 0` gives `ok v0 v0;` in C++ and `ok v0 v0;SWAP1` in Lean.
- Lean `Dup` accepts `R`, C++ `Stack::dup` asserts. `bottomup;R;R R;0;` gives `err` in C++ and
  `ok R R;DUP1` in Lean.
