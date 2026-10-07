<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Frama-C evidence — 2026-10-07

Work stopped at the user's request. All six components have complete
individual proof reports. The fresh combined run and two source control
suites are incomplete. No proof or solver process from this task remains.

The production C has SHA-256
`a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78`.
Production C, Rocq, the Clight AST, and the printer are unchanged.

## Component results

Paths in this table are relative to `spikes/clight-permute/build/frama-c/`
inside [component-proofs.tar.gz](component-proofs.tar.gz).

| Component | Valid / scheduled goals | Saved directory |
| --- | ---: | --- |
| Safety | 641/641 | `full-final-20261007/safety` |
| Termination | 337/337 | `full-final-20261007/termination` |
| Target | 313/313 | `full-final-20261007/target` |
| Trace | 393/393 | `trace-promoted-20261007/trace` |
| Status | 495/495 | `status-promoted-v14-20261007/status` |
| Success | 570/570 | `success-source-controls-final-20261007/baseline` |

The total is **2,749 obligations**, including helper lemmas and repeated
facts across components. The [saved-component audit](saved-component-audit.json)
checks the saved source hashes, complete reports, named prerequisites, and
tactic subgoals with the current checker. It also checks the same C tokens
and input clauses, matching logical definitions, and full contract coverage.
It performs no new prover run and does not create a root proof-run summary.

The domain is every valid permutation at lengths 1–1024, arbitrary initialized
unsigned 32-bit data, and six valid, disjoint arrays with the stated capacities.
Only input data and permutation require initialization. Scratch arrays do not.
Zero length and malformed permutations are outside this contract.

Safety, target, trace, and success prove partial correctness. Termination
proves termination on the same C and inputs. Status excludes result two.
The proved `guarded_success_iff` lemma combines the guarded success conditions
and the status bound into the original `success_iff` clause. Read the
[contract and tool guide](../../frama-c/README.md) before reviewing the reports.

## Controls and remaining work

[controls.tar.gz](controls.tar.gz) contains these unmodified result directories.

| Suite | Cases | Recorded result |
| --- | ---: | --- |
| `lemma-controls-final-20261007` | 7 | Pass; five faulty lemma changes rejected |
| `termination-controls-final-20261007` | 4 | Pass; missing decrement and wrong store rejected |
| `initialization-final-20261007` | 3 | Pass; missing target store rejected |
| `target-controls-v6-20261007` | 3 | Pass; wrong source index rejected |
| `trace-controls-20261007` | 4 | Pass; wrong depth and missing swap rejected |
| `status-lemma-controls-20261007` | 4 | Pass; missing unused-slot premise and wrong sign rejected |
| `success-lemma-controls-20261007` | 4 | Pass; missing exchange premise and status bound rejected |
| `status-source-controls-20261007` | 4 | Fail; expected failed property does not match |

All suites include an unchanged baseline and a parentheses control. A rejected
proof can time out; rejection alone does not prove that a mutant is incorrect.
Whole-component source controls include prerequisite assertions and lemmas.
The initialization suite checks its nine selected initialization obligations.

The status source suite passes both positive controls. Both faulty variants
are rejected. For `wrong-target`, `collect_value` and `injective_selected`
fail, but the control expects `collected_changed`. The original `pass: false`
result is preserved. Correct that expectation and check it when work resumes.

The success source suite is in `component-proofs.tar.gz`. Its 570/570 baseline
is complete. The parentheses run was interrupted, and the `false-success`
and `missing-swap` variants were not run. There is no root `results.json`.
The earlier incomplete success control attempt is in the diagnostic archive.

`full-final-20261007` completed safety, termination, and target, then stopped
during trace. There is no root `summary.json`. Do not report this as a completed
combined run. Complete both source control suites and a fresh combined run
in new directories when the user requests more work.

All **52 tool tests pass** in the pinned Nix shell. [tool-tests.log](tool-tests.log)
records the final run:

```sh
nix develop --offline --impure \
  --expr 'import ./spikes/clight-permute/tests/frama-c/shell.nix' \
  --command python3 -m unittest discover \
  -s spikes/clight-permute/tests/frama-c -p 'test_*.py'
```

## Diagnostics and trust limits

[diagnostics.tar.gz](diagnostics.tar.gz) retains the early focused and corrected
termination controls, the memory-dependent variant probes, and two earlier
incomplete runs (`full-composed-20261007` and `success-source-controls-20261007`).

- The focused termination control omitted a failed `swap_endpoints`
  prerequisite. Whole-component checks reject the mutant. This is
  [F10](../../../../../docs/verified-permute/FINDINGS.md#f10-a-focused-frama-c-mutation-test-omitted-a-failed-prerequisite),
  a control-scope error; the production runner did not accept that proof.
- A memory-dependent loop variant gave a false decrease condition in a
  terminating one-cell probe. The ghost-counter proof avoids that encoding
  issue. It proves counter bounds and permits no ghost write to real state.
- A missing reverse-scan invariant was corrected in the success annotations.
  This was an annotation gap, not a production C defect.
- An earlier 10-second safety timeout cleared in the final 30-second run.
  The final success baseline also closes the earlier 569/570 result.

No new bug was found in unchanged production C. These results trust ACSL,
Frama-C/WP, the `Typed+ref` memory model, tactics, Why3, CVC5, Z3, and the result
checker. They use machine integers and the x86-64 machine description.
They do not provide proof terms to Rocq. The C printer, compiler, and
Lean–Rocq links remain outside this evidence. No Alt-Ergo, `clightgen`,
`ccomp`, or CompCert compiler pass was used.

## Archive contents

The four archives preserve selected evidence from the ignored build tree.
The run directories retain annotated C, logs, commands, manifests, goal JSON,
SMT obligations, and tactic sessions where generated. Partial runs retain
only the files produced before interruption. Paths remain relative to the
repository root. Extract into a new directory to keep earlier evidence intact.

[sources.tar.gz](sources.tar.gz) contains:

- Tool and production source snapshots before and after whitespace cleanup,
  plus the final status documents, Nix shell, lock file, and license audit.
- The local Why3 configuration used by the controls and its solver wrappers.
- The saved-report audit script and the archive script under
  `spikes/clight-permute/build/frama-c/wrapup-20261007/`.

Historical per-run hashes identify the tools at run time. The final source
snapshot does not replace them. Saved proof input bytes are unchanged.
Only trailing whitespace was removed from four current annotation files;
the audit compares generated and saved annotations after that normalization.

Each archive has an `ARCHIVE_MEMBERS.json` with a SHA-256 for every regular
file and the target of each symbolic link. Solver binary links retain their
Nix store targets; the archives do not copy those binaries. Archive creation
reads every member back and checks its size, hash, and exact membership.
[SHA256SUMS](SHA256SUMS) covers the archives and the plain-text evidence files.
