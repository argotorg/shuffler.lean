<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Direct Clight/C execution evidence

The [test contract](../../../rocq-eval/README.md) defines the inputs,
observations, and trusted components. The actual Clight AST and actual
generated C agree on all selected cases in both campaigns:

| Campaign | Cases | Success | Blocked | Rejected |
| --- | ---: | ---: | ---: | ---: |
| [Small](small/results.json) | 925 | 683 | 0 | 242 |
| [Boundary](boundary/results.json) | 185 | 101 | 68 | 16 |

Each campaign compares the interpreter with GCC and Clang at `-O0`,
`-O2`, and `-O3`. All six builds agree on all records. The small campaign
exhausts permutations and binary value vectors at lengths 1 through 4,
then adds seeded valid and malformed inputs at lengths 1 through 8.
The boundary campaign uses selected inputs through length 1024.

The [eight regression tests](logs/validated-tests.log) pass on the final
build. They include fourteen control inputs, nine faulty C changes, one
equivalent C change, early exit, timeout, missing fuel, malformed input,
and different record counts. The initial
[mutation test](logs/tests-first.log) missed the equal-value swap branch.
A targeted case fixed that coverage gap. The
[record-count test](logs/record-count-red.log) found that the new comparison
helper accepted equal prefixes of different lengths. Its
[corrected test](logs/record-count-green.log) passes. Both corrections
precede the final campaigns.

The [wrapper theorem](sources/Driver.v) connects successful interpretation
to a complete Clight call. The [kernel policy](build/kernel-policy.log)
reports 12 allowed upstream axioms and no unsafe typing settings.
This is not a proof of the extraction, printer, native compiler, or full
input domain.

[archive.json](archive.json) lists retained source copies, compiler and
kernel logs, inputs, all seven output streams per campaign, and their
hashes. [build.json](build/build.json) also identifies all original source,
dependency object, and executable hashes. The original build remains in
`spikes/clight-permute/build/rocq-eval/validated/`.

The Nix compiler wrapper's fortify options are disabled for this matrix
because they require optimization and otherwise prevent the `-O0` build.
The remaining wrapper options are recorded in [hardening.json](build/hardening.json).
No production definition, printer, or C source changed for these tests.
