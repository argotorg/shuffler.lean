<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Root agent handoff

Final snapshot: 2026-10-06 22:14 UTC. **Stopped by user request.** The
earlier 2026-10-07 09:00 UTC deadline no longer requires this agent to run.
See [the main status](../WORKING_STATUS.md) and [findings](../FINDINGS.md).

## Final changes after the initial snapshot

- Fixed `guards.py` to save Rocq stdout as the assumptions report and
  stderr separately. The repeat passed baseline, admitted, and explicit
  false-axiom controls. Root stopped Python PID 61876 and its current
  `coqchk` child PID 63288 at 22:14:35 UTC. The last two controls in this
  repeat are incomplete. Preserve that distinction.
- Retried promoted reachability compilation with the correct Nix path.
  It failed on duplicate logical `SolcModel` objects in the source root
  and `build/proofs`. The next agent should compile isolated copies with
  one load path; no proof fix was attempted after the stop.
- The 34-case AST/model mutation run finished before the stop. All 32
  changed candidates and both equivalent controls had expected results.
- All child agents saved their final status and stopped their jobs.
- New printer-gap evidence includes a kernel-checked full-Permute prefix
  transfer theorem and an independent Frama-C initialization failure.

Older sections below describe the initial 22:04 snapshot; this final
section takes precedence where status changed.

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

The goal is unfinished. Leave it paused for the continuing agent.
