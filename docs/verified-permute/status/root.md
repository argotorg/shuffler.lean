<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Root agent handoff

Snapshot: 2026-10-06 22:04 UTC. Deadline: 2026-10-07 09:00 UTC.
See [the main status](../WORKING_STATUS.md) and [findings](../FINDINGS.md).

## Root-owned uncommitted files

- `spikes/clight-permute/check-assumptions.py`: strict parser/allowlist for
  the six inherited assumptions. Rejects missing required theorem reports.
- `spikes/clight-permute/test-assumptions.py`: 11 tests passed against the
  original 209-claim report, including new axioms and missing claims.
- `spikes/clight-permute/check-proofs.sh`: now records the theorem list,
  checks assumptions, and compiles the independent public type fixture.
- `spikes/clight-permute/tests/proof-challenge/`: mutation manifest, runner,
  guard controls, and `ProofContract.v`.
- `spikes/clight-permute/Reachability.v`: arbitrary-size model success/blocked
  iff theorem. Scratch predecessor compiled; promoted extra corollary needs
  checking.
- `spikes/clight-permute/ClightReachability.v`: written actual-call corollary;
  not yet compiled because the first command used the wrong Nix path.
- `spikes/clight-permute/audit-deps.py`: allowlist extended for those two
  reachability modules.

Do not edit agent-owned symbolic or Frama-C files without coordination.

## Completed root runs

1. Original pure Rocq shell now reads `flake.lock` directly and avoids the
   worktree `getFlake` hash problem. The five-module check passed. This fix
   is committed.
2. Original Clight proof source copies match the committed sources. Saved
   proof/source hashes and libFuzzer/AFL/Fil-C corpus archive hashes checked.
3. Hardened integrated proof check passed before the two reachability
   modules were added. Log: `/tmp/permute-check-hardened.log`.
4. Mutation run finished: 34/34 expected results. All 32 behavior-change
   candidates compile, then fail a dependent proof. Both definitional
   equivalent controls compile all affected proofs and the public contract.
   Results: `spikes/clight-permute/build/proof-challenge/results.json`.
   Log: `/tmp/permute-proof-mutations.log`. Every case retains its mutated
   source and compiler log. This demonstrates rejection by the existing
   proof scripts; a script rejection alone is not a behavioral witness.
5. Scratch reachability proof compiled and reports no assumptions for both
   iff theorems. Log: `/tmp/permute-reachability.log`.

## Failed or incomplete root runs

The guard tests found that the actual admitted theorem, false-axiom theorem,
impossible-precondition theorem, and `True` postcondition theorem all pass
`coqc` and `coqchk`. That is the intended setup. The type fixture rejects
the two weakened statements.

However, every assumptions check currently rejects the guard report,
including baseline, because `guards.py` merges compiler warnings into stdout.
The first rejected line is:

```text
File "./GuardAssumptions.v", line 1, characters 0-40:
```

Fix the driver to capture `coqc` stdout as the report and stderr as a
separate diagnostic log. Do not weaken the strict report parser. Then
repeat all five controls. Results currently in
`build/proof-challenge/guards/results.json` are not an all-pass result.

The `ClightReachability.v` compile command failed during Nix import, not
during Rocq checking. From repository root, use the normal shell path.
From `spikes/clight-permute`, use `import ./shell.nix`.
Log: `/tmp/permute-clight-reachability.log`.

## Tool sessions

These session identifiers are useful for collecting final exit status;
their output files already show completion/failure:

- 44435: hardened proof check, completed with exit zero.
- 27864: AST/model mutation run, output shows all 34 expected results.
- 63534: guard controls, output shows expected-result failures from warnings.
- 51836: scratch reachability compilation, completed with exit zero.

The three child agents have their own running sessions and status files.

## Pending integration and commits

- Fix guard report capture; test unsafe typing flags as a separate lead.
- Finish reachability module compilation and full `coqchk` integration.
- Implement the coverage source/binary manifest check with negative tests.
- Review/archive MSan evidence from `build/msan`, then commit its scripts
  and report. This run is complete; do not repeat it without a new reason.
- Review/archive `build/challenge` and commit source/metamorphic tests.
- Archive AST/model mutation and guard evidence, excluding compiled objects.
- Review symbolic false-pass fixes and repeat their retained cases.
- Add `.frama-c/` to the spike's ignored cache paths; do not commit that cache.
- Keep the symbolic and Frama-C work separate in later commits.

Useful shell from repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
```

Default shell does not include Python. A currently available interpreter is
`/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/bin/python3`.

Do not mark the goal complete or stop the search before the deadline.
