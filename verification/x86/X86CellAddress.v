(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers.
From ASCommon Require Import Common.
From SailStdpp Require Import Operators_mwords.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Address.
Open Scope Z_scope.

Lemma low32_zero_extend (value : bv 32) :
  @subrange_vec_dec 64 (@zero_extend 32 value 64) 31 0 = value.
Proof.
  change (bv_extract 0 32 (bv_zero_extend 64 value) = value).
  apply bv_eq. rewrite bv_extract_0_unsigned,
    bv_zero_extend_unsigned by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma zero_extend_machine_word value :
  @zero_extend 32 (machine_word value) 64 = machine_address (Int.unsigned value).
Proof.
  change (bv_zero_extend 64 (Z_to_bv 32 (Int.unsigned value)) =
    Z_to_bv 64 (Int.unsigned value)).
  apply bv_eq. rewrite bv_zero_extend_unsigned'.
  rewrite (Z_to_bv_small 32 (Int.unsigned value)) by exact (Int.unsigned_range value).
  symmetry. apply Z_to_bv_unsigned.
Qed.

Lemma zero_extend_word_repr index :
  0 <= index < Int.modulus ->
  @zero_extend 32 (machine_word (Int.repr index)) 64 = machine_address index.
Proof.
  intro Bounds. rewrite zero_extend_machine_word, Int.unsigned_repr; [reflexivity|].
  unfold Int.max_unsigned. lia.
Qed.

(* These are the operations used by Sail's decode_sib_byte. The equality
   includes modular arithmetic, so it needs no extra no-overflow premise. *)
Lemma machine_address_shift_two index :
  @shiftl 64 (machine_address index) 2 = machine_address (4 * index).
Proof.
  change (bv_shiftl (machine_address index) (Z_to_bv 64 2) =
    machine_address (4 * index)).
  apply bv_eq. rewrite bv_shiftl_unsigned.
  change (bv_wrap 64 (Z.shiftl (bv_unsigned (machine_address index)) 2) =
    bv_unsigned (machine_address (4 * index))).
  rewrite Z.shiftl_mul_pow2 by lia. unfold machine_address.
  rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_wrap 64 index * 4) = bv_wrap 64 (4 * index)).
  rewrite bv_wrap_mul_idemp_l, Z.mul_comm. reflexivity.
Qed.

Lemma scaled_machine_address base index :
  @add_vec 64 (machine_address base) (@shiftl 64 (machine_address index) 2) =
    machine_address (base + 4 * index).
Proof.
  rewrite machine_address_shift_two.
  apply machine_address_add.
Qed.

Lemma scaled_cell_address layout b k :
  @add_vec 64 (pointer_to_block layout b)
    (@shiftl 64 (machine_address (Z.of_nat k)) 2) =
    machine_address (cell_address (cell_layout layout) b k).
Proof. apply scaled_machine_address. Qed.

Lemma scaled_word_cell_address layout b k value :
  Int.unsigned value = Z.of_nat k ->
  @add_vec 64 (pointer_to_block layout b)
    (@shiftl 64 (@zero_extend 32 (machine_word value) 64) 2) =
    machine_address (cell_address (cell_layout layout) b k).
Proof.
  intro Index. rewrite zero_extend_machine_word, Index.
  apply scaled_cell_address.
Qed.

Lemma scaled_repr_cell_address layout b k :
  Z.of_nat k < Int.modulus ->
  @add_vec 64 (pointer_to_block layout b)
    (@shiftl 64 (@zero_extend 32 (machine_word (Int.repr (Z.of_nat k))) 64) 2) =
    machine_address (cell_address (cell_layout layout) b k).
Proof.
  intro Bound. rewrite zero_extend_word_repr by lia.
  apply scaled_cell_address.
Qed.

Print Assumptions low32_zero_extend.
Print Assumptions zero_extend_machine_word.
Print Assumptions scaled_repr_cell_address.
