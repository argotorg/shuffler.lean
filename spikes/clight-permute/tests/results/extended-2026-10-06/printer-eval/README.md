<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Generated Clight/printer evidence

All 128 generated programs pass on 50 input cases each, across GCC and
Clang at `-O0`, `-O2`, and `-O3`. This gives 6,400 interpreter cases and
38,400 native comparisons. There are 128 distinct printed source hashes.
The [test contract](../../../printer-eval/README.md) states the generator's
grammar, input domain, observations, and trust limits.

The campaign is split into a [pilot](pilot/results.json), seeds 0 through
7, and an [extension](extended/results.json), seeds 8 through 127. Every
program uses the same 18 boundary vectors and 32 seeded random vectors.
The inputs are eight-word unsigned arrays. This does not cover every
input or every program accepted by the printer.

The [retained audit](retained-audit.json) checks the complete seed set,
source and binary hashes, 50 records per program, and all six output
streams against the interpreter. Each output record has exactly 20
unsigned words. Native standard error is empty. Each program's printed
C and interpreter output are retained here; the identical native output
streams remain in the original build directories and their hashes are
in the audit.

The [printer controls](controls-validated/results.json) have all five
expected outcomes on six selected programs and 26 inputs per program:

- The unchanged printer passes.
- An added-parentheses change passes.
- Changing subtraction to addition is detected. One program has output
  mismatches; five have process or output-record errors after index
  arithmetic changes.
- Changing less-than to greater-than gives mismatches in all six programs.
- Reversing greater-or-equal gives mismatches in five programs.

Compile errors do not count as mutation detection. The
[test log](logs/validated-controls.log) also records rejection of exhausted
fuel and invalid input length.

The [literal control](literal-checked/results.json) checks a hand-calculated
20-word record in the interpreter and all six C builds. Its source uses
unsigned overflow, underflow, a wrapping array index, array updates, and
80-bit-shifted identifiers, with no local temporaries. The
[production round trip](logs/production-roundtrip.log) prints exactly the
existing `permute.c` from the generic extraction.

The [generic wrapper theorem](sources/Generic.v) connects an interpreter
return to a full Clight call under explicit declaration conditions.
The [kernel policy](validated/kernel-policy.log) reports 12 allowed
upstream axioms and no unsafe typing settings. The extraction, generator,
adapters, printer, native compilers, and comparison runner remain trusted
test components. The known undefined-temporary printer gap remains open.

[archive.json](archive.json) records retained file hashes. The
[build manifest](validated/build.json) records the original sources,
proof base, and executable hashes. The complete original artifacts are
under `spikes/clight-permute/build/printer-eval/`.
