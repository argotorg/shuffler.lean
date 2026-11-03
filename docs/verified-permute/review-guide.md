<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Permute review guide

The development starts after `0e92d2a`. Review the commits in this order.
The copied CompCert sources have their own licenses and form most of the
line count in the dependency commit. They are byte-for-byte upstream files.

| Commit | Review scope |
| --- | --- |
| `1268680` | Initial Rocq finite-permutation model |
| `d31d159` | Initial termination, result, trace, and orbit-count proofs |
| `ae02b74` | Initial execution tests, shell, and port evaluation |
| `c7459bd` | LGPL source selection, hashes, import audit, licenses, and C memory review |
| `db97c18` | Direct Clight AST, extraction, 109-line printer, printer tests, and generated C |
| `5443805` | Duplicate-aware model and proofs |
| `a6b482e` | Interpreter soundness and memory lemmas |
| `e037c4c` | Statement and swap-loop proofs |
| `bca311f` | Validation and normalization proofs |
| `bb27b60` | Complete-call theorem, integrated checks, and saved proof evidence |
| `2aa9d2a` | Actual pinned solc oracle and differential tests |
| `064a552` | libFuzzer, AFL++, branch reports, saved corpora, and results |
| `7b03cde` | Symbolic-tool and ACSL literature review |
| `05b3d59` | Fil-C checks, runtime controls, and saved results |

The main theorem is
[`ClightCorrect.permute_call_correct`](../../spikes/clight-permute/ClightCorrect.v).
It proves the actual Clight call against `SolcModel.solc_permute` for valid
permutations of lengths one through 1024. Empty and oversized calls have
separate theorems. Malformed permutation rejection is tested, not proved
for all inputs. The relation to the original Lean model is not proved;
that model omits the solc duplicate rules.

The [printer review](../../spikes/clight-permute/PRINTER_REVIEW.md) and
[C semantics review](c-semantics-review.md) state the trusted translation
and C memory conditions. GCC and Clang remain trusted. The CompCert
compiler theorem is not used.

The [proof evidence](../../spikes/clight-permute/proof-results/README.md)
records the checked modules, assumptions, and source hashes. The
[fuzz results](../../spikes/clight-permute/tests/FUZZ_RESULTS.md) retain raw
coverage totals and the four unreachable error outcomes. Test binaries and
tool distributions stay under ignored build directories; source, scripts,
logs, reports, and corpus archives are committed.

Later symbolic-tool experiments must state their proven size range,
runtime assumptions, and incomplete cases separately from this Rocq proof.
