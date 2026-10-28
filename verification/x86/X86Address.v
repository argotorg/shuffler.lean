(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ASCommon Require Import Common.
From SailStdpp Require Import Operators_mwords.
From X86 Require Import X86Flags X86Memory.
Open Scope Z_scope.

Lemma machine_address_add left right :
  bv_add (machine_address left) (machine_address right) =
    machine_address (left + right).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned,
    bv_wrap_add_idemp. reflexivity.
Qed.

Lemma machine_address_next address count :
  @add_vec_int 64 (machine_address address) count =
    machine_address (address + count).
Proof. apply machine_address_add. Qed.

Lemma address_add_zero (address : bv 64) :
  @add_vec 64 address (Z_to_bv 64 0) = address.
Proof.
  change (bv_add address (Z_to_bv 64 0) = address).
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_unsigned address + 0) = bv_unsigned address).
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma address_subtract (address : Z) count :
  @sub_vec_int 64 (machine_address address) count =
    machine_address (address - count).
Proof.
  change (bv_sub (machine_address address) (Z_to_bv 64 count) =
    machine_address (address - count)).
  apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned,
    bv_wrap_sub_idemp. reflexivity.
Qed.

Print Assumptions machine_address_next.
