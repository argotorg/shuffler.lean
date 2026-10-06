# Differential tests against solc

The oracle uses Solidity commit
[`cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`](https://github.com/argotorg/solidity/tree/cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912).
This is the commit recorded by this repository's `solidity` submodule.
`prepare_oracle.py` fetches three files at that commit and checks each full
file against a fixed SHA-256 digest. It copies the selected definitions
without changes. A changed cached file causes an error. The generated
include files retain the upstream license notice.

The C++ oracle runs the actual `Emission::permute` body from
`libyul/backends/evm/ssa/stack/Shuffler.cpp`. It includes duplicate-value
normalization and suppression of swaps between equal values. The following
code also comes from the upstream files without changes:

- The `Mapping` class and the `StackOffset` and `StackDepth` types.
- The reached `Emission` methods for destinations, final positions, depths,
  swap reachability, swapping, and blocked results.
- The reached `Stack` methods for swapping, index-to-depth conversion,
  size, swap validity, and swap range.

The small adapter supplies constructors, storage, and a C interface.
`StackData` contains unsigned IDs in place of full solc `StackSlot` objects.
The algorithm uses only equality and ordering of these values. The trace
adapter stores the depth of each swap. `yulAssert` maps to the active C++
`assert`; assertions are not disabled. The adapter initializes the upstream
mapping from the input permutation and returns data, trace, and blocked
results. This tests the internal Permute operation. It does not test the
whole solc compiler, the full shuffle planner, or `StackSlot` construction.
The internal upstream method assumes a nonempty stack. Empty and invalid
inputs test the generated C API separately.

`fuzz.c` is a small C driver with a fixed-seed random generator. It generates
permutations and value arrays, including duplicates and the largest
unsigned value. `check_case.c` compares status, trace, error fields, and the
complete data array, including data after a blocked swap. It also replays
the trace and checks the required final values on success. Each generated
buffer has exactly its required capacity. A failure prints the complete
input. `tests.c` covers all permutations and binary-value arrays through
length five, plus distinct-value arrays, empty input, rejected sizes,
invalid permutations, length 1024, depths 16 and 17, and an error after a
successful swap.

Run from an environment with Python 3, range-v3 headers, GCC, and Clang:

```sh
sh spikes/clight-permute/tests/matrix.sh path/to/generated/permute.c
```

This builds the core as C11 and the oracle as C++20. It tests GCC and Clang
at `-O2`, at `-O3`, and with AddressSanitizer and UndefinedBehaviorSanitizer.
Strict alias analysis stays enabled. Each run reports its compiler, target,
flags, case count, and seed. No CompCert executable is needed.

If LeakSanitizer reports that it cannot run in the execution environment,
use `ASAN_OPTIONS=detect_leaks=0` for that run. This keeps AddressSanitizer
and UndefinedBehaviorSanitizer active, but does not test for memory leaks.
Do not use this setting to suppress an actual leak report.

For one compiler or another random seed:

```sh
CC=gcc CXX=g++ PERMUTE_TEST_FLAGS='-O2 -fstrict-aliasing' \
  PERMUTE_FUZZ_CASES=20000 PERMUTE_FUZZ_SEED=12345 \
  sh spikes/clight-permute/tests/run.sh path/to/generated/permute.c /tmp/permute-tests
```

The new test code is GPL-3.0-or-later. The extracted solc definitions retain
the upstream GPL version 3 or later grant. Their legacy SPDX line says
`GPL-3.0`; the full upstream notice gives the “or any later version” option.
range-v3 uses the Boost Software License 1.0. These tests do not use any
CompCert code. Passing these tests is evidence about the tested executions;
it is not a proof of equivalence or absence of undefined behavior.

## Coverage-guided fuzzing

From the repository root, enter the shell described in the parent README:

```sh
sh spikes/clight-permute/tests/build-guided.sh
ASAN_OPTIONS=detect_leaks=0 sh spikes/clight-permute/tests/run-guided.sh -seed=2654435769
```

The second command runs until interrupted. The leak-check setting is for
this execution environment; omit it when LeakSanitizer works. AddressSanitizer
and UndefinedBehaviorSanitizer remain enabled. libFuzzer saves inputs that
add coverage features in `build/guided/corpus`, and failure inputs in
`build/guided/artifacts`. A comparison failure calls `abort`, so the fuzzer
can save and replay the input. Pass an artifact path to
`build/guided/fuzz/permute-fuzz` to replay it.

[guided.c](guided.c) supplies the C callback. It decodes bytes into unsigned
values and shuffle choices that always construct a valid permutation.
Another mode accepts raw destinations and classifies the permutation
before dispatch. Valid nonempty cases use the same solc differential
checker as `fuzz.c`. Empty, oversized, and malformed cases check the C API
contract; solc's internal operation does not accept these cases. The byte
format is documented in the harness. [seed_corpus.py](seed_corpus.py)
supplies 40 seeds for duplicates, size limits, depth limits, both blocked
return sites, equal top values, and rejected inputs. Missing bytes decode
as zero; short inputs still exercise the implementation.

The guided build uses Clang 21.1.8, `-O1`, libFuzzer edge instrumentation,
ASan, and UBSan. Both the generated C and the C++ oracle are instrumented.
The fuzzer's `cov` and `ft` counts include the harness and reached library
code. They are not branch coverage percentages for Permute.

## Branch coverage

While the fuzzer runs, use a second shell to take a coverage snapshot:

```sh
sh spikes/clight-permute/tests/guided-coverage.sh
```

This copies the current corpus and replays it through a separate `-O0`
build with Clang source coverage. Snapshotting tolerates inputs removed by
libFuzzer's corpus reduction and skips incomplete hash-named files. Each
report keeps its input snapshot, replay log, raw profile, merged profile,
LLVM JSON, text metrics, uncovered outcomes, and HTML under
`build/guided/report.*`. The active fuzz run is unchanged.

The report selects the generated `permute.c` and the unmodified
`solc_permute.inc`. It includes lambdas and macro expansions in the C++
Permute body. Helper files, the adapter, and standard-library/range-v3
internals are outside these two source totals. The script reports LLVM's
branch totals and also every exported true/false outcome. LLVM omits the
impossible false side of constant `while (1)` and `while (true)` conditions
from its standard totals; the supplemental count retains those sides.
No defensive error or failed assertion is removed from either total.

Literal 100% coverage cannot be reached under the input contracts. Three
generated C outcomes and one C++ assertion failure are unreachable. See
[BRANCH_REACHABILITY.md](BRANCH_REACHABILITY.md) for the source locations,
proof links, and arguments. Coverage and source analysis remain separate:
an unreachable outcome is reported as uncovered, never as covered.

## Fuzzer choice

Use [AFL++](https://aflplus.plus/), rather than the original AFL, when
choosing that family of fuzzers. It supports source instrumentation,
persistent execution, and comparison-guided mutation. There is no one
best engine for every target.

[libFuzzer](https://llvm.org/docs/LibFuzzer.html) fits this small in-process
C/C++ differential target and uses the existing Clang toolchain. LLVM now
maintains it for bug fixes; its original authors moved to Centipede, and
major new libFuzzer features are not planned. The callback is separate
from the proof and printer. The AFL++ build uses the same callback through
its libFuzzer-compatible persistent driver.

## AFL++

The pinned shell includes AFL++ 5.00c. It uses the free AGPL license option;
see the parent [license report](../LICENSING.md). Build and run it with:

```sh
sh spikes/clight-permute/tests/build-afl.sh
ASAN_OPTIONS=detect_leaks=0:abort_on_error=1:symbolize=0 \
UBSAN_OPTIONS=halt_on_error=1:abort_on_error=1 \
sh spikes/clight-permute/tests/run-afl.sh
```

Both implementations and the harness use AFL++ instrumentation, ASan,
and UBSan. The C core is compiled as C11; the oracle is C++20. This run
starts with the 40 boundary seeds, separately from the libFuzzer corpus.
The command runs until interrupted. AFL++ keeps its corpus and saved
failures under `build/afl/findings/default`. To replay its corpus and
measure the same source-level branches:

```sh
sh spikes/clight-permute/tests/guided-coverage.sh \
  spikes/clight-permute/build/guided \
  spikes/clight-permute/build/afl/findings/default/queue
```

This execution environment routes core dumps through an external utility,
which makes AFL++ reject startup. For this run, a separate deliberate-crash
probe first confirmed that AFL++ saved a crash under the chosen settings.
The actual run used `ulimit -c 0`, `AFL_NO_UI=1`, and
`AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1`, in addition to the sanitizer
settings above. The host's core-dump configuration was not changed. This
override is not a default in the runner; check crash detection before
using it on another host.

The run results, exact branch totals, and artifact paths are in
[FUZZ_RESULTS.md](FUZZ_RESULTS.md). Fuzzer bitmap percentages include other
instrumented code and are not the Permute branch percentages.

## Harness and report tests

```sh
python3 spikes/clight-permute/tests/test_coverage_report.py
ASAN_OPTIONS=detect_leaks=0 python3 spikes/clight-permute/tests/test_guided.py
```

The decoder tests inspect routing and decoded arrays through linker
wrappers, then call the actual differential or rejection checker. They
compile the generated C and pinned solc oracle with ASan and UBSan. The
report tests check missing, malformed, inconsistent, macro, lambda, and
constant-condition records; missing coverage must cause an error.

## Fil-C

[run-filc.sh](run-filc.sh) builds the actual C and C++ implementations with
the pinned Fil-C package and its libraries. It checks runtime linkage,
runs separate bounds-error probes, runs the exhaustive and random drivers,
and replays retained guided inputs. See [FILC_RESULTS.md](FILC_RESULTS.md)
for the commands, dependency licenses, results, and detection limits.
