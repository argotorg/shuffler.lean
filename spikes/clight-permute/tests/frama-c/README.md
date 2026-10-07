<!-- SPDX-License-Identifier: GPL-3.0-or-later -->

# Source-C proof with Frama-C

This is independent evidence for the emitted `permute.c`. It does not prove
the C printer or establish a new Rocq-to-C theorem.

The input domain is `1 <= n <= 1024`, a valid permutation, arbitrary
initialized `uint32` data, and six valid, disjoint arrays. Only the input
data and permutation require initialization. The scratch arrays do not.
This contract does not cover zero length or malformed permutations.

## Saved state: 2026-10-07

Work is paused at the user's request. All six components pass individually:
safety 641/641, termination 337/337, target 313/313, trace 393/393, status
495/495, and success 570/570. A check of the saved inputs and reports confirms
full contract coverage on the same C and input domain. All 52 tool tests
and seven control suites pass. See the [evidence](../results/frama-c-2026-10-07/README.md).

The fresh combined run stopped during trace and has no completed root result.
The status source control suite reports failure because one expected failed
property is wrong; both faulty variants are rejected. The success source
controls stopped after the baseline passed. Correct and check the status
expectation, complete the success controls, and run `full` in a new directory
when work resumes. No proof job remains active.

## Review order

1. Read `CONTRACT` in [annotate.py](annotate.py). It states the full contract.
2. Read [composition.py](composition.py). It checks that each component has
   the same real C and input conditions. It compares complete clauses,
   including quantified formulas and the definitions used by the contract.
3. Read the component annotations and helper lemmas below.
4. Read [run.py](run.py). A run fails if any scheduled goal, helper lemma,
   or tactic subgoal lacks a proof. Missing reports and missing named
   obligations also cause failure.

| Component | Claim | Annotation source |
|---|---|---|
| `safety` | Bounds, valid accesses, initialization, output count, and write set | `annotate.py` |
| `termination` | Every call in the input domain terminates | `termination.py`, `lemmas.acsl` |
| `target` | The target is initialized and contains the original data at each destination | `target.py` |
| `trace` | Trace bounds, exact replay, and a value change at each step | `trace_annotations.py`, `trace.acsl` |
| `status` | The return value is zero or one | `status.c` |
| `success` | The guarded success and blocked conditions | `success.c` |

`status.c` and `success.c` are annotation snapshots of the production C.
They are proof inputs. The generator rejects them if their real C tokens
differ from `permute.c`. Each component proves its own loop facts and helper
lemmas. It does not assume a claim from another component.

The safety, target, trace, and success components prove partial correctness.
The termination component proves termination for the same C and inputs.
The status component excludes return value two. The checked lemma
`guarded_success_iff` then combines the two guarded reachability conditions
into the full `success_iff` clause. The full gate checks this exact coverage.

The only ghost writes update a local termination counter. All other ghost
statements are empty snapshot labels. The generator checks the permitted
ghost statements. No ghost statement can write real C state.

## Commands

Run from the repository root. Use a fresh name for each run.

```sh
nix develop --offline --impure \
  --expr 'import ./spikes/clight-permute/tests/frama-c/shell.nix' \
  --command python3 spikes/clight-permute/tests/frama-c/run.py \
  --mode full --name review-full --timeout 30
```

Use `--mode memory` for safety and termination, or a component name for an
individual proof. `annotate.py` retains the original combined annotation
layout for review and comparison. The runner's `full` mode uses the six
components above.

```sh
nix develop --offline --impure \
  --expr 'import ./spikes/clight-permute/tests/frama-c/shell.nix' \
  --command python3 -m unittest discover \
  -s spikes/clight-permute/tests/frama-c -p 'test_*.py'
```

`check_lemmas.py`, `check_termination.py`, `check_contracts.py`, and
`check_initialization.py` run positive and negative controls. Source controls
check the whole component, including all prerequisites. Lemma controls
check the complete selected lemma library. A timeout is a rejection, not
a proof that the mutated program is incorrect.

## Trust scope

These checks trust the ACSL specification, Frama-C/WP, its memory model and
tactics, Why3, the SMT solvers, and the result checker. Solver results are
not imported into Rocq. The model is `Typed+ref` with machine integers and
the x86-64 machine description. The commands enable no user axioms and no
alternate context-variable model. The full check includes separate RTE
and initialization obligations.

The shell permits only free packages. See [LICENSE_AUDIT.md](LICENSE_AUDIT.md).
These runs use Frama-C, Why3, CVC5, and Z3. They do not use Alt-Ergo,
`clightgen`, `ccomp`, or CompCert compiler passes.
