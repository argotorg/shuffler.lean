<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Continued verification evidence

Work is now paused at the user's request on 2026-10-07. This overrides the
earlier deadline. The [process scan](pause-processes.json) records no active
verification process. The [final rank experiments](frama-rank-experiments/README.md)
prove one of three copied-source lemma goals. The
[larger rejection campaign](rejected-large-extended/README.md) remains
incomplete at lengths 32 and 64. All evidence is retained.

This work follows the user's instruction to continue testing until
2026-10-07 11:00 CEST. The central claim remains the
[Clight-to-Rocq theorem](../../../../../docs/verified-permute/README.md).
These runs test the supporting workflow. They do not close the printer or
Lean relation.

## Completed and incomplete runs

- [C API rejection](rejected/manifest.json): all malformed permutations and
  unsigned 32-bit values at lengths 1 through 6 and length 8 pass. All empty
  and oversized calls pass with null unused pointers. Lengths 16, 17, 18,
  32, and 64 hit the 120-second limit with partial paths and no error witness.
  The campaign reports failure because those cases are incomplete.
- [Longer rejection run](rejected-depth-extended/manifest.json): lengths 16,
  17, and 18 complete with 31, 33, and 35 marked paths. All pass with no
  errors, partial paths, or lost forks. The earlier failed campaign remains
  unchanged; lengths 32 and 64 are still incomplete.
- [Length-six pilot](n6-pilot/manifest.json): permutation `[1,0,2,3,4,5]`
  times out at 600 seconds, with 4,121 completed paths and 522 partial paths.
- [Longer length-six run](n6-swap/manifest.json): that same permutation
  completes all 4,683 marked paths in about 614 seconds. No error or lost
  fork is recorded. This covers one permutation, not all 720 at length six.
- [Fresh small-domain run](klee-exploration-checked/manifest.json): nine
  cases and 85 marked paths at lengths one through three pass with the
  added exploration policy.

## Findings and controls

[F8 and F9](../../../../../docs/verified-permute/FINDINGS.md) describe the
two new result-gate defects and their fixes.

The [unlimited faulty run](path-loss-unlimited/manifest.json) reports an
assertion witness at input 42. The [limited run](path-loss-false-pass/manifest.json)
reports success after discarding that branch. Its retained witness has
input zero and a completion marker. The
[wrapper](fork-limit-wrapper.py) records the explicit fork-limit and seed
options used for this control.

The [regression before the fix](path-loss-red/results.json) has two
unexpected acceptances. The [regression after the fix](path-loss-fixed/results.json)
has all four expected outcomes. Both the limited faulty source and limited
baseline are rejected for lost forks. The unrestricted baseline passes;
the unrestricted faulty source has an assertion witness.

The [KLEE assumption probe](klee-assume-probe/result/manifest.json) reports
success after an assumption inside the tested C removes input 42.
The source and witness are retained beside that manifest. The new symbol
policy rejects such a program before symbolic execution. Separate
`llvm.assume` and `klee_silent_exit` probes were rejected by the existing
checks; those probes are not false passes.

The [saved post-fix report](klee-assume-probe/fixed/program-symbols.json)
rejects the same `klee_assume` source before KLEE starts. The
[final controls](path-loss-symbols-checked/results.json) retain all four
expected fork-loss outcomes with both policies enabled.
[Final source hashes](final-gate-sources.json) identify the archived runner,
policy, test, and audit files. The logs are in `final-gate-logs/`.

## Retained evidence audit

The [generated printer programs](printer-eval/README.md) add 128 ASTs,
6,400 interpreter cases, and 38,400 native comparisons. All pass, as do
the printer controls and a hand-calculated arithmetic example.
The [sanitizer follow-up](printer-sanitizers/README.md) checks the same
6,400 cases with AddressSanitizer and UBSan, with diagnostic controls.
The [candidate assignment check](assignment-check/README.md) tests the
temporary-read condition and rejects the known self-copy prefix. The later
[path proof](assignment-path-proof/README.md) covers complete paths and
finite prefixes. The [execution proof](assignment-execution-proof/README.md)
connects terminating Clight executions to that model while retaining
branch decisions and intermediate states. Memory initialization and the
C translation are separate. The concrete divergence/prefix link is open.
The [proof controls](assignment-proof-controls/README.md) have all 19
expected outcomes, including changed checker and execution-model rules.
The [Frama-C initialization check](frama-initialization/README.md) proves
nine selected obligations on production C. A parentheses control passes;
removing the target store leaves its fill invariant unproved. This is
not a complete source-C proof.
The subsequent [full memory pass](frama-memory-strategy/README.md) has
641/642 explicit goals valid. Only main-loop termination remains unproved.

The later [direct Clight/C comparisons](rocq-eval/README.md) pass 1,110
selected cases across six GCC/Clang builds. Their archive includes the
checked wrapper theorem, inputs, output records, and regression controls.

The [exploration audit](retained-exploration-audit.json) checks 167 retained
cases and 71,587 completion witnesses. Every case has zero inhibited forks
and abnormal termination counters. The
[symbol audit](retained-symbols-audit.json) checks the C, C++ oracle, and
allocator-wrapper bitcode from all 167 cases; none contains a KLEE control
symbol.

This total combines the full lengths-one-through-five domain, the selected
length-six permutation, and thirteen restricted large profiles. The last
two groups do not extend the complete-domain claim beyond length five.

`source-map.json` maps the earlier manifests to archived source copies and
their hashes. The original run directories still contain the complete
bitcode and KTests. The comparison runner has since gained result checks;
the audits use its archived prior source hash rather than claim that the
old runs used the new runner. `fork-fix-sources/` records the first policy
fix before the later symbol-boundary change.

No new production C counterexample was found. The new defects concern the
supporting verification gates. Passing these controls does not establish
that every possible form of incomplete verification is detected.
