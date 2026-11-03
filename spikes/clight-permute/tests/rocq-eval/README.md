<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Clight execution and generated C

This test compares the actual `Permute.permute` AST with `permute.c`.
It executes the existing `ClightEval.execute`, which uses CompCert values,
arithmetic, and memory operations. It does not reimplement the algorithm.

`Driver.v` allocates six separate CompCert blocks for a nonempty call.
Only data and permutation are initialized. Scratch arrays, trace storage,
and output words start undefined. The temporary environment is the exact
`ClightCall.call_temps`, including undefined local temporaries. Empty and
oversized calls use null unused pointers and one writable output block.

The compared record contains the return code, all three output words,
final data, final permutation, and written trace prefix. Comparing the
permutation tests the exact AST/printer relation; the public C contract
does not specify its contents after a valid call. Unwritten memory is not
read. Invalid output lengths and any interpreter `None` fail the check.

`interpreted_call` connects a successful interpreter return to the complete
Clight call, using `execute_sound` and `permute_call`. The build compiles
fresh project dependencies, checks this theorem with `coqchk`, and applies
the existing axiom and unsafe-setting policy. Only the audited LGPL
CompCert subset is used. No C parser or CompCert compiler pass is used.

Extraction, the OCaml compiler/runtime, text adapters, native C compilers,
and the comparison runner remain trusted test infrastructure. This is
finite execution evidence, not a translation proof. Interpreter fuel is
a recursive depth bound, not a total instruction counter. A fuel failure
does not imply that C fails to terminate.

From the repository root, enter the proof shell:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
```

The audited CompCert dependencies must already be built. Use new output
directories for each build and campaign:

```sh
python3 spikes/clight-permute/tests/rocq-eval/build.py --output /tmp/permute-eval-build
ROCQ_EVAL_BUILD=/tmp/permute-eval-build python3 spikes/clight-permute/tests/rocq-eval/test_compare.py
python3 spikes/clight-permute/tests/rocq-eval/compare.py --build /tmp/permute-eval-build --output /tmp/permute-eval-small --profile small
python3 spikes/clight-permute/tests/rocq-eval/compare.py --build /tmp/permute-eval-build --output /tmp/permute-eval-boundary --profile boundary
```

The small corpus exhausts all permutations and all vectors over
`{0, UINT_MAX}` at lengths 1 through 4. It also includes seeded cases at
lengths 1 through 8 and malformed permutations. The boundary corpus uses
selected permutations and values at lengths 16 through 1024, including
the depth and size limits. Neither corpus covers all uint32 inputs.

The native matrix uses GCC and Clang at `-O0`, `-O2`, and `-O3`. The runner
checks source and binary hashes before a campaign. It retains the exact
inputs and every output record. The tests use independently stated
expected records, exhausted fuel, invalid protocol input, and the shared
C mutation matrix.

The [recorded campaigns](../results/extended-2026-10-06/rocq-eval/README.md)
pass 925 small cases and 185 boundary cases on all six builds. Eight
regression tests also pass. These results cover the listed inputs only.
