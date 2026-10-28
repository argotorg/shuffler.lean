(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot all_fingroup.
Require Import ClightScalar ModelArrays SolcModel.

(* Give the machine proofs fixed model types without importing MathComp's
   arithmetic notation, which conflicts with stdpp notation in ArchSem. *)
Definition model_permutation size := 'S_size.

Definition model_destination {size} (p : model_permutation size) (index : 'I_size) : nat :=
  nat_of_ord (p index).

Definition model_target {size} (source : 'I_size -> nat) (p : model_permutation size)
    : 'I_size -> nat := SolcModel.target_of source p.

Lemma model_target_uint size source (p : model_permutation size) :
  (forall index, uint (Z.of_nat (source index))) ->
  forall index, uint (Z.of_nat (model_target source p index)).
Proof. intros Values index. apply Values. Qed.

Print Assumptions model_target_uint.
