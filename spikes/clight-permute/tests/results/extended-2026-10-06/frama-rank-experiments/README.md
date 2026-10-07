<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Frama-C rank experiments at pause

Work is paused at the user's request on 2026-10-07. These copied-source
experiments do not change production C or `tests/frama-c/lemmas.acsl`.

The [all-integer experiment](rank-all-integers/goals.json) proves one of
three explicit lemma goals. Its strengthened bounds statement is:

```c
lemma moved_bounds{L}:
  \forall unsigned int *p, integer k;
    0 <= moved(p,k) <= (k <= 0 ? 0 : k);
```

All three induction branches pass CVC5. This is a WP/SMT result, not a
Rocq kernel proof. The generalized frame and update statements remain
unproved: their positive induction branches time out. Repeated induction
does not close them. WP uses earlier lemmas as premises for later ones;
the update result cannot be accepted while frame is unproved.

The two prior experiments are retained for diagnosis. No complete rank
library or main-loop termination proof is claimed. The production memory
pass remains [641/642 valid](../frama-memory-strategy/README.md).

After the user resumes work, try instantiating the positive induction
hypothesis at `n - 1`, then the array-frame premise at the required index.
If the generalized results pass, retain the original lemma statements as
corollaries and check every prerequisite together before use in C proofs.
The main-loop measure must handle equal-value exchanges, which can skip
trace increments; trace length alone does not establish progress.

[archive.json](archive.json) records hashes for 80 retained files, including
sources, proof scripts, SMT obligations, logs, and the diagnostic runner.
The runner's exit code is not a proof-completion check; inspect each goal
report. The saved tool-test log records all 25 tests passing.
