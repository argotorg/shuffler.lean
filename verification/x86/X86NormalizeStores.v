(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory FixedBlocks.
Open Scope Z_scope.

(* The same CompCert stores are supplied to the LLVM and x86 proofs. *)
Definition normalize_stores permutation used index (choice : bool) c final : Prop :=
  exists middle,
    (if choice then
       Mem.store Mint32 c permutation (4 * Z.of_nat index)
         (Vint (Int.repr (Z.of_nat index))) = Some middle
     else middle = c) /\
    Mem.store Mint32 middle used (4 * Z.of_nat index) (Vint (flag_word choice)) = Some final.

Lemma normalize_stores_frame permutation used index choice c final other values :
  normalize_stores permutation used index choice c final ->
  other <> permutation -> other <> used ->
  array_at c other values -> array_at final other values.
Proof.
  intros [middle [Assignment Used]] NotPermutation NotUsed Array.
  eapply array_store_disjoint; [|exact NotUsed|exact Used].
  destruct choice.
  - eapply array_store_disjoint; [exact Array|exact NotPermutation|exact Assignment].
  - subst middle. exact Array.
Qed.

Print Assumptions normalize_stores_frame.
