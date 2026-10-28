(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
Require Import CellRelation.
Open Scope Z_scope.

Definition address_modulus : Z := 2 ^ 64.

(* Bounds are part of the layout. Empty blocks carry no machine addresses. *)
Record finite_layout := {
  cell_layout : allocation_layout;
  mapped_bounds : forall b, (0 < block_words cell_layout b)%nat ->
    0 <= block_address cell_layout b /\
    block_address cell_layout b + 4 * Z.of_nat (block_words cell_layout b)
      <= address_modulus
}.

Lemma cell_range (layout : finite_layout) b k :
  (k < block_words (cell_layout layout) b)%nat ->
  0 <= cell_address (cell_layout layout) b k /\
  cell_address (cell_layout layout) b k + 4 <= address_modulus.
Proof.
  intro K. destruct (mapped_bounds layout b ltac:(lia)) as [Low High].
  unfold cell_address. lia.
Qed.

Lemma cell_byte_range (layout : finite_layout) b k byte :
  (k < block_words (cell_layout layout) b)%nat -> 0 <= byte < 4 ->
  0 <= cell_address (cell_layout layout) b k + byte < address_modulus.
Proof.
  intros K Byte. pose proof (cell_range layout b k K). lia.
Qed.

Lemma cell_byte_mod (layout : finite_layout) b k byte :
  (k < block_words (cell_layout layout) b)%nat -> 0 <= byte < 4 ->
  (cell_address (cell_layout layout) b k + byte) mod address_modulus =
    cell_address (cell_layout layout) b k + byte.
Proof. intros K Byte. apply Z.mod_small, cell_byte_range; assumption. Qed.

Lemma different_cells_mod (layout : finite_layout) b k b' j byte byte' :
  (k < block_words (cell_layout layout) b)%nat ->
  (j < block_words (cell_layout layout) b')%nat ->
  b <> b' \/ k <> j -> 0 <= byte < 4 -> 0 <= byte' < 4 ->
  (cell_address (cell_layout layout) b k + byte) mod address_modulus <>
    (cell_address (cell_layout layout) b' j + byte') mod address_modulus.
Proof.
  intros K J Different Byte Byte'.
  rewrite (cell_byte_mod layout b k byte K Byte).
  rewrite (cell_byte_mod layout b' j byte' J Byte').
  pose proof (@distinct_cells_disjoint (cell_layout layout) b k b' j
    K J Different). lia.
Qed.

Lemma stack_save_slot_range sp k :
  40 <= sp -> sp + 16 <= address_modulus -> (k < 5)%nat ->
  sp - 40 <= sp - 8 * Z.of_nat (S k) /\
  0 <= sp - 8 * Z.of_nat (S k) /\
  sp - 8 * Z.of_nat (S k) + 8 <= sp.
Proof. intros Low High K. lia. Qed.

Lemma stack_argument_byte_range sp byte :
  40 <= sp -> sp + 16 <= address_modulus -> 0 <= byte < 16 ->
  0 <= sp + byte < address_modulus.
Proof. intros Low High Byte. lia. Qed.

Lemma returned_stack_pointer sp :
  40 <= sp -> sp + 16 <= address_modulus ->
  (sp + 8) mod address_modulus = sp + 8.
Proof. intros Low High. apply Z.mod_small. lia. Qed.
