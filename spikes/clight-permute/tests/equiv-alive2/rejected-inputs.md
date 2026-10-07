<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Symbolic C API rejection checks

The public Clight-to-model theorem assumes a valid permutation. These
checks cover separate C API behavior: empty calls, oversized calls, and
malformed permutations. They call the actual generated `permute.c`.
They do not call the solc operation, which requires valid input.

For each selected nonzero length, all permutation entries, data values,
and initial output words are unrestricted symbolic unsigned 32-bit values.
The driver assumes that the permutation is malformed. It defines validity
independently: every entry must be in range and all entries must differ.
It requires return code 2, three zero output words, and unchanged data and
permutation arrays. Scratch contents and the unwritten trace are not observed.

Size 0 selects a separate check with a symbolic length: every length that
is zero or greater than 1024. Only `out` is allocated; the other five
pointers are null. Empty calls must return 0 and oversized calls must
return 2. Both must write three zero output words.

Run from the repository root, in the KLEE shell:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/tests/equiv-alive2/klee-shell.nix'
python3 spikes/clight-permute/tests/equiv-alive2/test_rejected.py
python3 spikes/clight-permute/tests/equiv-alive2/run-rejected.py \
  --sizes 0,1,2,3,4,5 --max-time 120s \
  --output spikes/clight-permute/build/equiv-alive2/rejected-new
```

The output directory must be new. The manifest records source and bitcode
hashes, path counts, errors, and completion checks. Every terminal witness
must have the declared input and the completion marker created after all
assertions. A timeout, partial path, error, source change, or missing marker
prevents a pass. Inhibited forks and abnormal state termination also
prevent a pass. The compiled C module may not contain KLEE control symbols;
only the separate driver supplies symbolic inputs and assumptions.
Compiler and solver versions and commands are retained.

Nine tests exercise the runner with the actual production C and changed
copies. They check the baseline, wrong rejection status, changed data,
changed permutation, a missing output write, an out-of-range index, a null
access after size rejection is weakened, early exit, and an equivalent
unsigned expression. Assertion and memory controls require actual KLEE
witnesses; compile errors and timeouts do not count as detection.

The checks use the same pinned Clang/KLEE shell and error checks as the
C/C++ comparison. This driver needs no dynamic allocation or C++ runtime.
KLEE's LLVM semantics and its initialization limits still apply. These
results are supporting evidence, not a universal Rocq rejection theorem
or a proof of the Clight-to-C printer.

The extended run completed lengths 1 through 6 and length 8, plus the
empty/oversized domain. Lengths 16, 17, 18, 32, and 64 hit the 120-second
limit with partial paths and no error witness; they are incomplete.
The run is retained under `build/equiv-alive2/rejected-extended/`.
A later run with a 1,800-second limit per case completes lengths 16,
17, and 18 with 31, 33, and 35 marked paths. All pass without errors,
partial paths, or lost forks. Its
[archive](../results/extended-2026-10-06/rejected-depth-extended/manifest.json)
retains source snapshots, bitcode, statistics, and all witnesses.
Lengths 32 and 64 remain incomplete.
See the [archive](../results/extended-2026-10-06/README.md), its per-case manifest, and the
[working status](../../../../docs/verified-permute/WORKING_STATUS.md) for
completed sizes and limits. Do not infer completion for all requested
sizes from a successful earlier case.
