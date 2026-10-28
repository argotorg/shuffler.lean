(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot all_fingroup.
Require Import ClightMemory ClightScalar ClightNormalization ModelArrays SolcModel ModelProofs.
Require Import FixedPrefix Fill.
From X86 Require Import X86ModelTypes.

Definition model_normalize {size} (source : 'I_size -> nat) (p : model_permutation size) :=
  SolcModel.normalize source p.

Definition model_fixed_reserved {size} (source : 'I_size -> nat) (p : model_permutation size) :=
  fixed_values source (model_target source p).

Definition model_fixed_assignment {size} (source : 'I_size -> nat) (p : model_permutation size)
    (index : 'I_size) : 'I_size :=
  if index \in model_fixed_reserved source p then index else p index.

Lemma model_normalization_fill size (source : 'I_size -> nat) (p : model_permutation size) :
  exists q result,
    model_normalize source p = Some q /\
    raw_fill source (model_target source p) (enum 'I_size)
      (model_fixed_assignment source p) (model_fixed_reserved source p) = Some result /\
    (forall index, result index = q index).
Proof.
  destruct (raw_normalize_complete source p)
    as [q [result [Normalized [Raw [Result Rest]]]]].
  exists q, result. split; [exact Normalized|]. split; assumption.
Qed.

Lemma model_fixed_fill_arrays d source (p : model_permutation (S d)) bd bp bt bu c :
  FixedPrefix.fixed_prefix_arrays d source p bd bp bt bu c ->
  fill_arrays (S d) source (model_target source p) bd bt bp bu
    (model_fixed_assignment source p) (model_fixed_reserved source p) c.
Proof.
  intros [Data [Target [Permutation Used]]].
  rewrite fixed_initial_words in Permutation. rewrite fixed_flag_words in Used.
  constructor; assumption.
Qed.

Print Assumptions model_normalization_fill.
Print Assumptions model_fixed_fill_arrays.
