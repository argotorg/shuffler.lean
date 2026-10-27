<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Generated programs through the printer

This tool sends the same generated Clight function to the existing
interpreter and the unchanged production `printer.ml`. It compiles the
printed C with GCC and Clang at `-O0`, `-O2`, and `-O3`, then compares
complete output records for selected inputs.

The generator uses the printer's current function interface. Each program
has eight data words, eight words in the second array, and three output
words. The second array contains arbitrary unsigned values; this test is
not a permutation algorithm. Unused pointer arguments are null in both
executions. Output memory and local temporaries start undefined. Each
generated body initializes the output and all local temporaries before
use. Only the first output word is fixed at zero, because these programs
do not write a swap trace.

The generated bodies contain:

- unsigned addition and subtraction, including wraparound;
- all five comparison operators accepted by the printer;
- loads and stores, with both literal and arithmetic array indices;
- nested conditions and sequences;
- two nested bounded loops, an inner `break`, and early returns;
- unchanged, renamed, and 80-bit-shifted identifiers.

The record compares the return value, all three output words, and every
word of both arrays. Every element is an unsigned 32-bit value. Each
program uses the same recorded corpus of boundary values and seeded
random vectors. Different program seeds select different ASTs. These
are finite tests of this generator's output, not coverage of every AST
accepted by the printer.

`Generic.v` uses the actual parameter binder and undefined-temporary
initializer. Its `generated_call` theorem connects an interpreter return
to a full Clight call, under explicit declaration conditions. It does not
prove the OCaml printer's declaration checks or its C output. The kernel
check uses the existing axiom policy and only the audited LGPL CompCert
subset. Extraction, the generator, adapters, compiler, and result checker
remain trusted test components.

The regression controls compile copies of the actual printer. They change
subtraction to addition, less-than to greater-than, and greater-or-equal
to less-or-equal. Each must produce a rejected comparison for at least one
tested program. The unchanged printer and an added-parentheses control
must pass every selected program. Compilation errors do not count as a
detected mutation. Invalid input records and exhausted interpreter fuel
must also fail.

Use the proof shell and a completed [Clight execution build](../rocq-eval/README.md):

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
python3 spikes/clight-permute/tests/printer-eval/build.py --base /tmp/permute-eval-build --output /tmp/printer-eval-build
PRINTER_EVAL_BUILD=/tmp/printer-eval-build PRINTER_EVAL_CONTROLS=/tmp/printer-controls python3 spikes/clight-permute/tests/printer-eval/test_controls.py -v
python3 spikes/clight-permute/tests/printer-eval/literal.py --build /tmp/printer-eval-build --output /tmp/printer-literal
python3 spikes/clight-permute/tests/printer-eval/run.py --build /tmp/printer-eval-build --output /tmp/printer-programs --programs 128
python3 spikes/clight-permute/tests/printer-eval/sanitize.py --build /tmp/printer-eval-build --output /tmp/printer-sanitized --programs 128
```

Output directories must be new. The build checks the base proof hashes,
and the campaign checks its source and executable hashes. Inputs, printed
C, compiler diagnostics, output streams, per-program results, and the
final result are retained. A failed build has no final success manifest.
The printer retains its fixed `Permute.permute` header in these generated
files. That comment is not provenance evidence for a generated test
program; use its seed, source hash, and retained generator instead.
The compiler matrix disables Nix fortify options because they require
optimization. It suppresses unused-parameter and unused-assigned-variable
warnings, since some generated bodies do not use every interface field.
Other enabled warnings remain errors.

The [completed campaign](../results/extended-2026-10-06/printer-eval/README.md)
has 128 programs and 50 inputs per program. All six builds agree with the
interpreter, for 38,400 native comparisons. Five printer controls and a
hand-calculated arithmetic example have their expected results.

The sanitizer campaign also passes all 128 programs on the same 6,400
cases. It uses Clang `-O1` with AddressSanitizer and UBSan. A buffer
overflow and an invalid shift produce the required diagnostics and
nonzero exits. Leak detection is disabled: LeakSanitizer cannot inspect
threads in this execution environment. These generated functions use
stack objects only; no leak result is claimed.
