<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Sanitizer check of generated programs

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

All 128 programs pass on the same 50 inputs each, for 6,400 cases.
Clang `-O1` builds use AddressSanitizer and UBSan, with recovery disabled.
Every output agrees with a fresh run of the extracted Clight interpreter.
Standard error is empty for all unchanged programs.

`results.json` records source and binary hashes, comparisons,
and controls. Each `seed-*` directory retains the printed C, compile
command, diagnostics, reference output, and sanitized output. The original
instrumented executables remain under
`spikes/clight-permute/build/printer-eval/sanitizer-extended/`.

Both negative controls compile and fail at runtime as required:

- One-past-end store (`control-bounds/sanitized.stderr`): AddressSanitizer
  reports `stack-buffer-overflow`; the process exits nonzero.
- Shift by 32 (`control-shift/sanitized.stderr`): UBSan reports an invalid
  shift exponent; the process exits nonzero.

The initial pilot failed during LeakSanitizer's thread scan. Its
diagnostic (`initial-leak-sanitizer-failure/seed-0/sanitized.stderr`) says
that LeakSanitizer cannot work under ptrace. The corrected campaign uses
`ASAN_OPTIONS=detect_leaks=0`. AddressSanitizer and UBSan stay enabled.
These generated functions use stack objects only. No leak result is
claimed, and the failed pilot remains recorded as a failure.

The runner (`sources/sanitize.py`) and archive hashes (`archive.json`) are
retained. These finite checks add memory and undefined-behavior evidence
for the selected generator domain. They do not prove the printer correct
or close its known undefined-temporary gap.
