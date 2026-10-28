(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ASCommon Require Import Common.
From SailTinyX86 Require Import Tiny_x86.
Open Scope Z_scope.

Lemma instruction_fetch_address base offset fetched :
  @SailStdpp.Operators_mwords.vector_truncate 64
    (@SailStdpp.Operators_mwords.add_vec_int 64
      (Z_to_bv 64 (base + offset)) (fetched - offset)) 64 =
    Z_to_bv 64 (base + fetched).
Proof.
  change (bv_extract 0 64 (bv_add (Z_to_bv 64 (base + offset))
    (Z_to_bv 64 (fetched - offset))) = Z_to_bv 64 (base + fetched)).
  apply bv_eq.
  rewrite bv_extract_0_unsigned, bv_wrap_bv_unsigned,
    bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp.
  f_equal. lia.
Qed.

Print Assumptions instruction_fetch_address.
