<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Permute fuzz results

Both coverage-guided campaigns passed without a differential mismatch,
ASan finding, or UBSan finding. Each final corpus covers all 72 reachable
branch outcomes in the two selected Permute source files. Raw LLVM
coverage is **72/76 (94.74%)**, not 100%. The three C defensive-error
outcomes and one C++ assertion failure remain uncovered. Their separate
reachability arguments are in [BRANCH_REACHABILITY.md](BRANCH_REACHABILITY.md).

These runs took place on 2026-10-06 on x86-64 Linux. They compare the
generated C with the actual pinned solc C++ operation through the adapter
described in [README.md](README.md). They do not run the whole solc binary.

## Campaigns

| Engine | Executions | Seed | Retained snapshot | Findings |
| --- | ---: | ---: | ---: | --- |
| LLVM 21.1.8 libFuzzer | 381,174 | 2654435769 | 482 files, 761,131 bytes | None |
| AFL++ 5.00c | 228,026 | 2654435769 | 364 files, 1,017,096 bytes | No saved crashes or hangs; no timeouts |

libFuzzer ran for about 259 seconds and reported peak RSS of 444 MB.
AFL++ reports 118 seconds and 100% stability. Its 21.12% bitmap coverage
includes the harness and library code; it is not Permute branch coverage.
The runs started independently from the 40 boundary seeds. Counts include
repeated inputs. A corpus snapshot can retain seed files that are not in
libFuzzer's current reduced in-memory corpus.

Both engines compiled the C core as C11 and the actual C++ oracle as
C++20 with Clang 21.1.8, `-O1`, ASan, UBSan, frame pointers, and no
sanitizer recovery. The runtime settings were:

```text
libFuzzer: ASAN_OPTIONS=detect_leaks=0
AFL++: ASAN_OPTIONS=detect_leaks=0:abort_on_error=1:symbolize=0
       UBSAN_OPTIONS=halt_on_error=1:abort_on_error=1
```

Leak checking was disabled because this container does not support
LeakSanitizer. These runs do not establish absence of memory leaks.
The runners used a maximum input length of 8195 and a ten-second input
timeout. Each engine was interrupted after the accepted coverage target
was met. libFuzzer's interrupt exit code was 72; AFL++ exited with zero.

The host routes core dumps through an external utility. Before the AFL++
run, a separate deliberate-crash probe confirmed that AFL++ saved one
expected crash with `ulimit -c 0` and
`AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1`. This probe is not a Permute
finding. Its source, log, and statistics are in `results/afl-crash-probe`.
The host settings were not changed.

## Branch results

Both saved corpora give these totals when replayed in the separate
Clang `-O0` source-coverage build:

| Source | LLVM covered / total | Percentage | All exported outcomes |
| --- | ---: | ---: | ---: |
| Generated `permute.c` | 46/49 | 93.88% | 46/56 |
| solc `Emission::permute`, including lambdas and macros | 26/27 | 96.30% | 26/28 |
| Total | 72/76 | 94.74% | 72/84 |

The supplemental export count includes the impossible false sides of
seven C `while (1)` conditions and one C++ `while (true)` condition.
LLVM excludes those eight constant alternatives from its standard count.
Neither table removes the four unreachable error outcomes. Helpers,
adapters, and library internals are outside these two source totals.

## Saved evidence and replay

`results/libfuzzer` and `results/afl` contain the original fuzz logs,
build logs, raw LLVM JSON, summary and branch reports, corpus replay logs,
and corpus archives. AFL++ statistics are also saved. The JSON retains
the original absolute source paths. The coverage JSON SHA-256 values are:

```text
libFuzzer b4041a59ed1d913cf8951cf0be6d6f0b7b1ee76183fa9ea0c274eed8b9209f23
AFL++     d80f550f26d6cfc61b5292de73039104e9eff21dfd41eb28208dc979c95c0aa0
```

To replay either saved corpus from the repository root in the pinned
shell (replace `libfuzzer` with `afl` for the second corpus):

```sh
sh spikes/clight-permute/tests/build-guided.sh
mkdir -p spikes/clight-permute/build/saved-libfuzzer
tar -xzf spikes/clight-permute/tests/results/libfuzzer/corpus.tar.gz \
  -C spikes/clight-permute/build/saved-libfuzzer
ASAN_OPTIONS=detect_leaks=0 \
  spikes/clight-permute/build/guided/fuzz/permute-fuzz -runs=0 \
  spikes/clight-permute/build/saved-libfuzzer/corpus
sh spikes/clight-permute/tests/guided-coverage.sh \
  spikes/clight-permute/build/guided \
  spikes/clight-permute/build/saved-libfuzzer/corpus
```

Each archive contains only corpus files. Its adjacent `corpus.sha256`
lists the file hashes relative to the extraction directory.

The C and printer hashes for both campaigns are:

```text
permute.c  a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78
printer.ml c03fd138ad37c039a0adfa1470ab3c0711c7d4b83a9b39a25949a44420e33dec
```

`results/sources.sha256` also records the harness and oracle source hashes.
The solc revision is `cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`.
`prepare_oracle.py` checks the full upstream file hashes before extracting
the unchanged reached definitions.

## Other checks

[Fil-C 0.686](FILC_RESULTS.md) passed 4,435 exhaustive cases, boundary and
rejection cases, 100,000 random cases, and 802 unique retained corpus
inputs. Both implementations used the Fil-C runtime. Separate C and C++
probes detected writes beyond the allocation bounds but did not detect a
one-element overrun within the allocator's rounding. The report retains
that limit. This was random testing and replay, not guided Fil-C fuzzing.

The earlier GCC 15.3.0 and Clang 21.1.8 matrix passed all six configurations
(`-O2`, `-O3`, ASan+UBSan for each compiler). Each configuration ran 4,435
exhaustive cases, 20,000 random cases, and the boundary/rejection cases.
The random inputs were the same across configurations.

After the guided harness was added, the Clang ASan+UBSan regression passed
again. Its log is saved. The 13 coverage-report tests and eight guided
harness test groups also passed. These checks include malformed report
data, invalid permutations, input truncation, all mode bytes, full unsigned
values, and seed round trips through the actual differential checker.

Fuzzing is evidence for the executions tested. It is not a universal
equivalence proof or a proof that either compiled program has no memory
errors.
