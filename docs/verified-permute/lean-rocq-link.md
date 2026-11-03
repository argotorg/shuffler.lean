<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# A checked Lean ↔ Rocq link

This is a proposed design, not an implemented bridge. The current Lean
definition must first acquire the duplicate normalization and equal-value
rules already in the Rocq model. No current theorem proves the two models
equivalent.

## Model correspondence before general proof transfer

For the proof of concept, start with a restricted translation of executable
definitions. Represent both models in one formal setting and prove that
related inputs produce related outputs. The output relation must include
success or blocking, complete or partial data, exact trace order, and all
blocked fields. The mathematical natural numbers, bounded C words, finite
indices, and permutation composition also need explicit relations.

A possible sequence is:

1. Align the Lean definition and state the observations to preserve.
2. Select a small executable language with a formal semantics.
3. Export the actual Lean definition and its required dependencies into
   that language. Reject unsupported constructs.
4. Check a certificate connecting the exported term to the actual Lean
   function. An exporter that merely prints a plausible second definition
   leaves the same kind of trust gap as an unchecked C printer.
5. Interpret the exported term in the environment used for the
   correspondence proof and prove agreement with `SolcModel.solc_permute`.
6. Compose that result with `PermuteCorrect.clight_refines_model`.

The certificate format, checker, and interpretation theorem are work to be
designed and proved. Two independently implemented interpreters with similar
source text are not automatically a checked cross-system link.

An untrusted translator is acceptable if a checked certificate establishes
the required source-to-target relation for every accepted output. This
approach can reject inputs outside a small supported fragment. It need not
translate all of Mathlib or all Lean proofs to test the workflow.

## Importing proofs is a different task

Tactics produce proof terms. Proof transfer would translate those terms and
their theorem statements, not replay the tactic scripts. A target kernel can
then check the translated proof. The statement translation must preserve
meaning; proving an incorrectly translated statement is not sufficient.

Lean and Rocq have different conversion and typing rules. Relevant parts
include universe constraints, inductive recursors, definitional proof
irrelevance, quotients, and classical axioms. The bridge must handle the
features used by the exported dependency closure or reject that closure.
An axiom allowlist must remain explicit.

Another route is a Lean proof checker implemented and proved sound in Rocq.
That would establish a judgment such as “this term proves this type under
the formalized Lean rules.” It does not by itself provide the corresponding
native Rocq proposition. That requires a further interpretation theorem.

## Existing building blocks

The following project descriptions were read during the review. No bridge
tool was installed, and no interoperability result is claimed.

| Project | Documented role | What it does not supply here |
| --- | --- | --- |
| [lean4export](https://github.com/leanprover/lean4export) | Exports Lean declarations and transitive dependencies in a documented format. | A proof that the exported definition agrees with our Rocq model. |
| [Lean4Lean](https://github.com/digama0/lean4lean) | Implements the Lean kernel in Lean and includes metatheory and implementation verification. | A Lean checker verified in Rocq. |
| [nanoda](https://github.com/ammkrn/nanoda_lib) | An external Lean type checker that reads exported declarations. | A native Rocq proof of an imported theorem. |
| [MetaRocq](https://github.com/MetaRocq/metarocq) | Rocq term representations, formal typing, checking, and certified translation infrastructure. | A ready-made Lean frontend or a Lean-to-Rocq soundness theorem. |
| [Logipedia](https://github.com/Deducteam/Logipedia) | A project for sharing formal proofs through a common logical framework. | A demonstrated bridge for this Lean/Mathlib and Rocq/MathComp development. |

Pin versions and audit assumptions before a trial. In particular, do not
copy a sample external checker's axiom list without review. An imported
compiler-trust axiom would be a new trust condition for this pipeline.
