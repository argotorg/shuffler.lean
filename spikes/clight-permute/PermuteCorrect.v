(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Public theorem statements. The long implementation proofs are imported.
   This proves Clight-to-model refinement, not C-to-C++ equivalence. *)
From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot all_fingroup.
Require Export PermuteSpec.
Require Import ClightCorrect ClightReachability.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem clight_refines_model d (source : 'I_d.+1 -> nat) (destinations : 'S_d.+1)
    (arrays : buffers) ge initial :
  valid_call source destinations arrays initial ->
  exists final code result,
    clight_returns d arrays ge initial final code /\
    matches_model source destinations arrays final code result.
Proof.
intros [Size [Separate [Values [Data [Permutation [Target [Used [Trace Output]]]]]]]].
exact (@ClightCorrect.permute_call_correct d ge initial
  (data_block arrays) (permutation_block arrays) (target_block arrays)
  (used_block arrays) (trace_block arrays) (output_block arrays)
  source destinations Size Separate Values Data Permutation Target Used Trace Output).
Qed.

Theorem clight_decides_reachability d (source : 'I_d.+1 -> nat) (destinations : 'S_d.+1)
    (arrays : buffers) ge initial :
  valid_call source destinations arrays initial ->
  exists final code result,
    clight_returns d arrays ge initial final code /\
    matches_model source destinations arrays final code result /\
    (code = 0%Z <-> values_reachable source destinations) /\
    (code = 1%Z <-> ~ values_reachable source destinations).
Proof.
intros Valid.
destruct (clight_refines_model ge Valid) as [final [code [result [Call Match]]]].
destruct Match as [Model [Arrays [Spec Codes]]].
exists final, code, result. split; [exact Call|].
split; [exact (conj Model (conj Arrays (conj Spec Codes)))|].
exact (result_code_reachable Model Arrays Codes).
Qed.
