<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Resumed supporting evidence

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

Read the [core definitions and public theorem](../../../../../docs/verified-permute/README.md)
first. These runs test parts of the workflow. They do not prove the complete
C ↔ Lean relation. The separate [proof archive](../../../proof-results/reviewed-2026-10-06/README.md)
contains the checked theorem, type fixtures, policy controls, and proof mutations.

| Check | Result | Evidence and limit |
| --- | --- | --- |
| KLEE | All 153 cases and 66,805 marked paths pass at lengths one through five. | Summary (`klee-summary.json`), audit log (`klee-audit.log`), and audit script (`klee-audit.py`). All valid permutations and unrestricted unsigned 32-bit values, including duplicates, under the recorded LLVM and successful-allocation models. |
| SAW completion controls | Unchanged baseline, C early exit, C++ early exit, and stale-result control all have the expected result. | Results (`saw-completion.json`) and log (`saw-completion.log`). Selected controls; not a full equivalence proof. |
| Frama-C memory run | 635/642 valid; one unknown and six timeouts. The driver reports incomplete. | Summary (`frama-memory-summary.json`), goals (`frama-memory-goals.json`), and manifest (`frama-memory-manifest.json`). This does not replace the earlier 642/644 result. Initialization and termination remain open. |
| Printer initialization reproduction | The Clight prefix proof passes; GCC and Clang diagnose the printed uninitialized self-copy. | Run log (`undef-copy.log`), GCC log (`undef-copy-gcc.log`), and Clang log (`undef-copy-clang.log`). This confirms a gap in the accepted printer subset; it is not a failure of unchanged production C. |
| Native coverage replay | 72/76 LLVM outcomes and 72/84 exported outcomes. | Replay log (`coverage.log`) and build manifest (`coverage-build-manifest.json`). The reporting script checks source and binary identity before replay. Coverage does not prove correctness. |

The KLEE audit uses only lengths one through four from
the retained manifest (`klee-retained-manifest.json`), then all length-five
cases from the new manifest (`klee-n5-manifest.json`). The retained manifest
also contains an incomplete length-five campaign; those cases are excluded.
The new run log (`klee-n5.log`) is retained unchanged.

The audit checks the exact permutation sets, source and linked-bitcode
hashes, logs, error files, path counts, and every terminal KTest completion
marker. Bitcode and KTests remain in the two `build/equiv-alive2/` campaign
directories named in the summary. They are not copied into this archive.

The Frama-C driver tests pass in its Nix shell: 24 tests, recorded in
`frama-tests.log`. The earlier test attempt outside that
shell failed because a solver was unavailable; its
log (`frama-tests-without-shell.log`) is retained too.

No production C bug was found in these runs. The Lean ↔ Rocq relation is
future work. The printer translation proof and full C/C++ equivalence also
remain open. See the [trust boundary](../../../../../docs/verified-permute/trust-boundary.md).
