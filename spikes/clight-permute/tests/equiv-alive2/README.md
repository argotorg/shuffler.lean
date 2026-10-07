# C/C++ symbolic equivalence checks

Alive2 did not establish the requested equivalence. The trial reached
recursive range-v3 calls that its intraprocedural comparison does not
verify against the C implementation. The work therefore continued with
KLEE. This directory retains both tool selections; successful results
below are **KLEE results**, not Alive2 results.

The actual generated C and pinned solc C++ oracle are compiled into the
same LLVM module. The oracle retains the reached vector and range-v3
bodies. No replacement sorting or Permute algorithm is used. Both calls
receive equal input values and separate arrays. The assertion harness
compares status, complete final/partial data, trace length, the written
trace prefix, blocked offset, and excess depth. Scratch outputs and the
unwritten trace suffix are outside the public observation contract.

## Complete finite domains

Every input value is an unrestricted symbolic 32-bit unsigned integer.
Duplicates are included. Each permutation is a separate concrete case;
the runner enumerates every permutation at the selected lengths.
The completed runs currently establish:

| Length | Permutations | Completed paths per permutation | Partial paths or errors |
| --- | ---: | ---: | --- |
| 1 | 1 | 1 | 0 |
| 2 | 2 | 3 | 0 |
| 3 | 6 | 13 | 0 |
| 4 | 24 | 75 | 0 |
| 5 | 120 | 541 | 0 |

The corrected campaigns cover 153 cases and 66,805 marked paths. The
[retained audit](../results/resumed-2026-10-06/README.md) combines lengths
one through four from the earlier corrected run with the completed new
length-five run. It checks source and bitcode hashes and reads every
completion witness again. Each path uses the completion check below.

These are complete symbolic checks for the stated finite domains under
KLEE's LLVM and allocation models. They do not prove all inputs through
length 1024. In particular, lengths below 18 cannot reach blocked swaps.
There is no loop-unroll bound in these KLEE runs. A time or memory limit,
an error artifact, or any partial path makes the runner fail.

## Reproduce

The separate [C API rejection checks](rejected-inputs.md) use symbolic
malformed permutations and empty/oversized calls. They do not extend the
C/C++ comparison to inputs outside the solc operation's contract.

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/tests/equiv-alive2/klee-shell.nix'
python3 spikes/clight-permute/tests/equiv-alive2/run-klee.py --sizes 1,2,3,4 --jobs 4
python3 spikes/clight-permute/tests/equiv-alive2/test_klee_coverage.py
python3 spikes/clight-permute/tests/equiv-alive2/test_completion.py
python3 spikes/clight-permute/tests/equiv-alive2/test_profiles.py
python3 spikes/clight-permute/tests/equiv-alive2/test_exploration.py
python3 spikes/clight-permute/tests/equiv-alive2/test_program_symbols.py
python3 spikes/clight-permute/tests/equiv-alive2/path-loss.py --output /tmp/permute-klee-path-loss
python3 spikes/clight-permute/tests/equiv-alive2/mutations.py --output /tmp/permute-klee-mutations
python3 spikes/clight-permute/tests/equiv-alive2/matrix.py --output /tmp/permute-klee-matrix
python3 spikes/clight-permute/tests/equiv-alive2/profile-campaign.py --output /tmp/permute-klee-profiles
```

The default sizes are two and three. `--sizes 5` requests all 120
permutations of length five. `--sizes 18 --permutation ...` can select
one larger permutation. The parser accepts lengths through 1024; this
is not a claim that those domains can be explored within available time.
`--core PATH` selects a separate C source copy. `--solc-permute PATH`
overlays a separate upstream-body copy after the original source hashes
have been checked. These options support mutation tests. They do not edit
production source. `--output` must name a new directory, so old evidence
cannot silently be replaced.

`--value-groups 0,1,0` is an explicit restricted input domain. It creates
two unrestricted symbolic unsigned integers, then forms the input
`[A,B,A]`. A and B may be equal. The manifest records the full group
pattern. This option permits selected long-array checks; it does not
cover all values or all permutations at that length. `profile-campaign.py`
selects swap, reverse, and rotation patterns at lengths 17 through 1024.
Long permutation names use a SHA-256 suffix to respect file-name limits.

The earlier corrected campaign used `--sizes 1,2,3,4,5 --jobs 4
--max-time 240s --output spikes/clight-permute/build/equiv-alive2/klee-complete-checked`.
It was stopped after completing lengths one through four and part of
length five. The resumed run used `--sizes 5 --jobs 4 --max-time 240s
--output spikes/clight-permute/build/equiv-alive2/klee-resumed-n5` and
completed all 120 length-five cases.
Each case keeps build logs, linked bitcode, KLEE logs, solver statistics,
instruction records, and generated concrete witnesses. The manifest
records source and linked-bitcode hashes, completed/partial paths, and
error artifacts. It checks the source hashes again after each proof.
For a report made during the initial coverage-parser version, recompute
the counters after the run finishes:

```sh
python3 spikes/clight-permute/tests/equiv-alive2/klee_coverage.py \
  spikes/clight-permute/build/equiv-alive2/klee-complete/manifest.json
```

The parser now excludes call-arc summaries from instruction totals. Its
counts are instruction coverage of three selected functions, not branch
coverage or coverage of every library function.

## Early-exit defect and completion check

The first result gate accepted an actual solc-body mutant containing
`if (m_data[0] == 0U) std::exit(0);`. For length three and permutation
`[1,0,2]`, KLEE reported 17 completed paths, no partial paths, no errors,
and positive coverage of both implementations. Four paths ended before
the result comparisons. Inputs include `[0,0,0]` and `[0,255,4294967295]`.
This was a false equivalence result in the harness.

`completion.c` now calls the comparison function, then creates a one-byte
symbolic object named `checks_completed`. The runner reads every terminal
KTest. Each must contain the declared input object followed by this final
marker. The number of KTests must equal the completed-path count. Thus an
early process exit cannot pass merely because KLEE labels it completed.
The mutant is now rejected for four missing markers. The unchanged case
passes with 13 marked paths. Seven tests cover the KTest parser, missing
or misplaced markers, input-domain changes, corrupt files, and lost tests.

The before/after proof artifacts remain under `build/equiv-alive2/klee-exit-probe`
and `klee-exit-probe-fixed`. This finding concerns the harness, not a found
wrong result in the unchanged C implementation. The complete small-domain
campaign, mutation controls, and selected large profiles have completed
with the corrected gate. Old artifacts retain their original result fields.

## Safety and runtime model

The result gate also checks the pinned KLEE statistics database. It rejects
inhibited forks, abnormal state termination, and skip-fork warnings. A
completion marker proves only that a retained path reached the assertions;
it does not show that all feasible branches were retained. The
[extended controls](../results/extended-2026-10-06/README.md) demonstrate a
false pass after a fork limit, followed by rejection under the new policy.

Before linking the trusted drivers, the runner uses `llvm-nm` to inspect the
C, C++ oracle, and allocator-wrapper bitcode. Program modules may not define
or reference `klee_` symbols. These controls belong to the separate harness.
This prevents a tested source from silently adding a `klee_assume` condition
to the declared input domain. The symbol reports and module hashes are
retained in each case directory. A policy rejection is not a semantic
counterexample; no KLEE proof is run for that case.

All input files use `-O0 -g -Xclang -disable-O0-optnone`, with vectorization
disabled. The build adds signed-overflow, shift, integer-division, and
array-bound checks, with no sanitizer recovery. KLEE runs with its UBSan
runtime, division/shift checks, normal memory checking, active assertions,
and `--external-calls=none`. The final run selects `--libc=none`: only
KLEE's freestanding memory routines are linked. Earlier trial logs used
`--libc=klee`; those are not the final campaign.

KLEE's built-in allocator/new/delete model supplies successful allocations.
It reports an eight-byte allocation alignment assumption, which meets
the reached types' alignment needs here. Allocation failure and C++
exception behavior are outside the checked domain. C++ uses
`-fno-exceptions`. This experiment does not replace solc's reached vector
or range-v3 code with contracts. Unreached throw, nothrow-allocation, and
library-assertion declarations can remain in bitcode. An actual call to
an unsupported external function causes the run to fail. The runner also
rejects logged calls to KLEE's concrete external-call whitelist.

For large arrays, range-v3 reaches the nothrow allocation wrapper. The
runner compiles the unchanged GCC `new_opnt.cc` at revision
`4db0e8df15bef836558857c291c323add11d035c`, checked against SHA-256
`4c2466f46ae448de78523a245600acbbbca8680409e7f477f1939de28bac48c0`.
It calls the ordinary-new model described above. The wrapper is compiled
with exceptions disabled; the successful-allocation assumption remains.
The first length-1024 attempt stopped with an unsupported external call
before this body was linked. It was rejected, not counted as a proof.

The full input arrays are initialized. Scratch arrays and trace storage
start without explicit initialization, as the production contract permits.
KLEE is not an uninitialized-read detector for every LLVM `undef` case;
the separate Clight initialization proof and MSan checks remain relevant.
The proof concerns the `StackSlot`-ID oracle described in the parent test
README, not full solc compiler execution or allocation failures.

## Mutation evidence

The same harness rejected nine faulty source copies:

- C success status, data swap, trace depth, and trace count changes.
- A C write outside `out`, reported as a pointer error.
- A C signed addition overflow, reported as an overflow error.
- C++ data corruption, removal of equal-value swap suppression, and an
  early return from the misplaced-slot search.

The early-exit mutant above is a tenth faulty control. It is rejected by
the completion check and has no KLEE error file. Two equivalent source
changes passed: adding unsigned zero to a C zero
store, and replacing solc's `while (true)` with `for (;;)`. Each control
uses length three, permutation `[1,0,2]`, and full symbolic values. Logs
and error witnesses are under `build/equiv-alive2/klee-mutations-final`.
The controls establish that these checks can accept an equivalent change
and reject differences in the reached observations and safety conditions.
They do not establish a complete mutation score for untested branches.

## Pins and licenses

The tool shell uses the repository's Nixpkgs pin
`c7def046b9a883d46974757852106483d741586f` with `allowUnfree = false`.
The older packaged KLEE 3.2 is marked broken for its newer LLVM dependency.
This shell instead builds upstream KLEE commit
[`9a36a6782b814fe1fa37439652b875114faa0e20`](https://github.com/klee/klee/tree/9a36a6782b814fe1fa37439652b875114faa0e20),
whose upstream CI includes LLVM 19. The unpacked source hash is
`sha256-ZftUYugRlpKOhCwEaZmEETredZ4nm3AOldf95JNgWRQ=`.
The executable reports KLEE 3.3-pre, LLVM 19.1.7, and KLEE assertions ON.
The Nix build does not run the complete upstream KLEE test suite. Local
positive, pointer-error, integer-error, and equivalence-mutation controls
were run; these do not replace that suite.

| Selected component | Terms |
| --- | --- |
| KLEE, KDAlloc, and freestanding memory runtime | [University of Illinois/NCSA](https://github.com/klee/klee/blob/9a36a6782b814fe1fa37439652b875114faa0e20/LICENSE.TXT) |
| KLEE UBSan runtime, Clang/LLVM 19.1.7 | Apache-2.0 with LLVM exceptions; retained LLVM notices |
| Z3 4.16.0, the selected solver | MIT |
| STP 2.4.1, MiniSat 2.2.1, CryptoMiniSat 5.11.21, CaDiCaL | MIT; STP is linked by the packaged build but is not selected as the solver |
| gperftools 2.18.1 | BSD-3-Clause |
| SQLite 3.53.3 | Public-domain dedication and SQLite blessing |
| Host libstdc++ / libgcc 15.3.0 | GPL-3.0-or-later with GCC runtime library exception |
| Linked GCC nothrow allocation wrapper | GPL-3.0-or-later with GCC Runtime Library Exception 3.1 |
| Host glibc | LGPL; not the target libc model |
| libunwind, libffi, libxml2 | MIT |
| zlib | Zlib |
| liblzma 5.8.3 | [0BSD](https://github.com/tukaani-project/xz/blob/v5.8.3/COPYING) |
| Optional built klee-uclibc | LGPL; not selected in these proof runs |
| range-v3 0.12.0 | Boost Software License 1.0 |
| New harnesses / solc bodies | GPL-3.0-or-later |

The reached KLEE and sanitizer runtime files were inspected along with
the tool package and shared-library list. The legacy KLEE libc contains
BSD advertising-clause files; the final `--libc=none` selection avoids
linking that libc. No noncommercial-only tool or solver is selected.
This verifier is separate from production linking.

The Alive2 trial used version 21.0, commit
`913e1556032ee70a9ebf147b5a0c7e10086b7490`, with LLVM/Clang 21.1.8 and
Z3 4.16.0. Alive2 and Z3 use MIT; the LLVM terms are above. The package
also links hiredis 1.4.1 under BSD-3-Clause; no Redis server or caching is
used. Its source pin is `sha256-LL6/Epn6iHQJGKb8PX+U6zvXK/WTlvOIJPr6JuGRsSU=`.
Unsupported attributes/metadata and an incomplete unrolling trial are
retained under ignored `build/equiv-alive2`. No Alive2 proof is claimed.

The remaining route to all sizes requires a proved relation between
duplicate normalization, the two loop states, mapping updates, and trace
emission, plus termination and library contracts. See the independent
[translation review](../../../../docs/verified-permute/review-translation.md).
