<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Verification summary — 2026-10-07

**Status: paused.** Work and evidence are saved in commit `fb9a9ae`.
No verification jobs are running.

The aim is to test the proposed C ↔ Lean verification pipeline before use
on larger programs. Permute is the test case. The current checked theorem
connects the actual Clight implementation to the Rocq model. The full
C ↔ Lean chain is not proved.

## Completed work

- **Proof review:** separated specifications from proof scripts and added
  a readable public theorem. Kernel checks, independent theorem-type
  checks, and assumption checks pass.
- **Verification tools:** found and fixed cases where incomplete symbolic
  runs, restricted input domains, stale results, or unchecked assumptions
  could give false confidence. Negative controls test these checks.
- **Assignment proof:** proved prior assignment of temporary names for
  supported terminating Clight executions, including the Permute body.
  All 19 proof controls have their expected results.
- **Independent execution checks:** 1,110 selected Clight/C cases agree
  across six compiler builds. Another 128 generated programs pass 38,400
  native comparisons. Symbolic C/C++ comparisons cover all permutations
  and unsigned 32-bit values at lengths 1–5 under the recorded runtime model.
- **Frama-C:** 641/642 memory obligations are valid. Initialization controls
  and all 25 tool tests pass. The experimental rank bounds lemma also passes.

## Remaining work

1. **Finish the source-C proof.** Prove the rank frame/update lemmas and
   main-loop termination, then complete the full functional contract.
   The 641/642 result is not a complete memory-contract proof.
2. **Close the Clight-to-C translation gap.** A changed Clight program can
   pass its proof yet print an uninitialized C read. The assignment checker
   is not a production gate. Memory initialization, concrete execution
   prefixes, extraction, and printing still need separate arguments.
3. **Extend supporting checks where useful.** General malformed-input
   rejection has no universal call theorem. Length-32 and length-64 symbolic
   rejection runs remain incomplete; their partial results are saved.
4. **Keep the Lean ↔ Rocq bridge as future work.** The models differ, and
   no checked relation or proof transfer exists. This remains outside scope.

No new bug was found in unchanged production C. Confirmed findings concern
the translation contract and verification tools. Passing tests does not
establish that the whole pipeline is free of bugs.

Start review with the [core definitions and theorem](README.md), then the
[trust boundary](trust-boundary.md), [findings](FINDINGS.md), and
[supporting evidence](../../spikes/clight-permute/tests/results/extended-2026-10-06/README.md).
The [handoff](WORKING_STATUS.md) contains the detailed state for resuming work.
