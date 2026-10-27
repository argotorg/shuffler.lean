<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Assignment proof controls

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

All 19 expected outcomes pass. `results.json` records each
source hash, compiler exit, and required failure location.

- Seven weakened checker copies compile after removal of all 21 example
  tests. Each then fails the soundness theorem or its branch-join lemma.
  The unchanged checker and a parentheses control pass.
- Five changed execution-record definitions fail the required coverage,
  erasure, or path theorem. They hide unsafe assignments, reverse a branch,
  omit a condition read, reset assignments at a later loop iteration, or
  count a set target as assigned before its source is read. The unchanged
  record model and a parentheses control pass.
- Real compiler failures from a missing import, invalid syntax in the
  theorem, and an unrelated failed lemma are excluded from soundness
  failure results.

These are failures of the retained proof scripts at named statements.
They are supporting controls, not a replacement for theorem review or
the [kernel-checked execution proof](../assignment-execution-proof/README.md).
The seven checker changes also have independent negative examples in the
[initial checker archive](../assignment-check/README.md).

`sources/proof_controls.py` is the runner.
Each case retains its source and diagnostics. The original examples and
production sources were not changed. `archive.json` records
79 file hashes, checked against the result records when archived.
The build is `spikes/clight-permute/build/initialization/proof-controls-execution/`.
