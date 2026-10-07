<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Verification summary — 2026-10-07

**Status: paused at the user's request.** No verification jobs are running.
The [Frama-C evidence](../../spikes/clight-permute/tests/results/frama-c-2026-10-07/README.md)
records the latest work and the checks that remain incomplete.

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
- **Frama-C:** all six components pass individually: safety 641/641,
  termination 337/337, target 313/313, trace 393/393, status 495/495, and
  success 570/570. These are 2,749 obligations, including helper lemmas.
  A check of the saved inputs and reports confirms the same C, input domain,
  and coverage of the full ACSL contract. Seven control suites and all 52
  tool tests pass. These results use Frama-C/WP and SMT solvers, not Rocq.

## Remaining work

1. **Finish the Frama-C validation.** The fresh combined run was stopped
   during its trace component and has no completed root result. The status
   source controls reject both faulty changes, but one expected property
   is wrong, so that suite reports failure. The success source controls
   stopped after their baseline passed. Preserve these limits when using
   the six completed component proofs.
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
