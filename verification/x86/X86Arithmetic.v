(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ASCommon Require Import Common.
From SailStdpp Require Import MachineWord Operators_mwords.
Open Scope Z_scope.

Lemma unsigned32_negative z :
  -2147483648 <= z < 0 ->
  bv_unsigned (Z_to_bv 32 z) = z + 4294967296.
Proof.
  intro Range. change (z mod 4294967296 = z + 4294967296).
  rewrite <- (Z.mod_add z 1 4294967296) by lia.
  apply Z.mod_small. lia.
Qed.

(* This is the exact bit read by Sail's update_sign_flag for a 32-bit result. *)
Lemma sign_bit32 z :
  -2147483648 <= z < 2147483648 ->
  @access_vec_dec 32 (Z_to_bv 32 z) 31 =
    Z_to_bv 1 (if z <? 0 then 1 else 0).
Proof.
  intro Range. change (bv_extract 31 1 (Z_to_bv 32 z) =
    Z_to_bv 1 (if z <? 0 then 1 else 0)).
  apply bv_eq. rewrite bv_extract_unsigned.
  destruct (z <? 0) eqn:Negative.
  - apply Z.ltb_lt in Negative.
    rewrite unsigned32_negative by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    change ((z + 4294967296) / 2147483648 mod 2 = 1).
    assert (Quotient : (z + 4294967296) / 2147483648 = 1).
    { symmetry. apply Z.div_unique with (r := z + 2147483648); lia. }
    now rewrite Quotient.
  - apply Z.ltb_ge in Negative.
    rewrite Z_to_bv_small by (change (0 <= z < 4294967296); lia).
    rewrite Z.shiftr_div_pow2 by lia.
    change (z / 2147483648 mod 2 = 0).
    rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma subtract32 a b :
  0 <= a < 4294967296 -> 0 <= b < 4294967296 ->
  @sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 (a - b).
Proof.
  intros A B. unfold sub_vec, word_binop, MachineWord.sub.
  apply bv_eq. rewrite bv_sub_unsigned.
  change (bv_wrap 32 (bv_unsigned (Z_to_bv 32 a) - bv_unsigned (Z_to_bv 32 b)) =
    bv_unsigned (Z_to_bv 32 (a - b))).
  rewrite (Z_to_bv_small 32 a) by exact A.
  rewrite (Z_to_bv_small 32 b) by exact B.
  symmetry. apply Z_to_bv_unsigned.
Qed.

(* JNS tests only SF. These operand bounds exclude signed overflow. *)
Lemma compare32_sign a b :
  0 <= a < 2147483648 -> 0 <= b < 2147483648 ->
  @access_vec_dec 32 (@sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b)) 31 =
    Z_to_bv 1 (if a <? b then 1 else 0).
Proof.
  intros A B. rewrite subtract32 by lia. rewrite sign_bit32 by lia.
  f_equal. destruct (a - b <? 0) eqn:Difference;
    destruct (a <? b) eqn:Less; try reflexivity;
    apply Z.ltb_lt in Difference || apply Z.ltb_ge in Difference;
    apply Z.ltb_lt in Less || apply Z.ltb_ge in Less; lia.
Qed.

Print Assumptions compare32_sign.

Lemma sign_bit32_unsigned z :
  0 <= z < 4294967296 ->
  @access_vec_dec 32 (Z_to_bv 32 z) 31 =
    Z_to_bv 1 (if z <? 2147483648 then 0 else 1).
Proof.
  intro Range. change (bv_extract 31 1 (Z_to_bv 32 z) =
    Z_to_bv 1 (if z <? 2147483648 then 0 else 1)).
  apply bv_eq. rewrite bv_extract_unsigned.
  rewrite Z_to_bv_small by exact Range.
  rewrite Z.shiftr_div_pow2 by lia.
  destruct (z <? 2147483648) eqn:Small.
  - apply Z.ltb_lt in Small. change (z / 2147483648 mod 2 = 0).
    rewrite Z.div_small by lia. reflexivity.
  - apply Z.ltb_ge in Small. change (z / 2147483648 mod 2 = 1).
    assert (Quotient : z / 2147483648 = 1).
    { symmetry. apply Z.div_unique with (r := z - 2147483648); lia. }
    now rewrite Quotient.
Qed.

Lemma word32_equal a b :
  0 <= a < 4294967296 -> 0 <= b < 4294967296 ->
  Z_to_bv 32 a = Z_to_bv 32 b <-> a = b.
Proof.
  intros A B. split; [|intro Equal; now subst b].
  intro Equal. apply (f_equal (@bv_unsigned 32)) in Equal.
  rewrite (Z_to_bv_small 32 a A), (Z_to_bv_small 32 b B) in Equal.
  exact Equal.
Qed.

Lemma compare32_zero a b :
  0 <= a < 4294967296 -> 0 <= b < 4294967296 ->
  @eq_vec 32 (@sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b)) (Z_to_bv 32 0) =
    Z.eqb a b.
Proof.
  intros A B. unfold eq_vec, MachineWord.eqb.
  destruct (Z.eqb a b) eqn:Equal.
  - apply Z.eqb_eq in Equal. subst b. apply bool_decide_eq_true_2.
    rewrite subtract32 by assumption. rewrite Z.sub_diag. reflexivity.
  - apply Z.eqb_neq in Equal. apply bool_decide_eq_false_2.
    intro Zero.
    change (bv_sub (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 0) in Zero.
    apply bv_eq in Zero. rewrite bv_sub_unsigned in Zero.
    rewrite (Z_to_bv_small 32 a A), (Z_to_bv_small 32 b B) in Zero.
    change ((a - b) mod 4294967296 = 0) in Zero.
    pose proof (Z.mod_eq (a - b) 4294967296 ltac:(lia)).
    pose proof (Z.mod_pos_bound (a - b) 4294967296 ltac:(lia)).
    assert (Range : -4294967296 < a - b < 4294967296) by lia.
    assert (a - b = 0).
    { destruct (Z_lt_ge_dec (a - b) 0) as [Negative|Positive].
      - assert (Modulo : (a - b) mod 4294967296 = a - b + 4294967296).
        { rewrite <- (Z.mod_add (a - b) 1 4294967296) by lia.
          apply Z.mod_small. lia. }
        lia.
      - rewrite Z.mod_small in Zero by lia. exact Zero. }
    lia.
Qed.

Print Assumptions sign_bit32_unsigned.
Print Assumptions compare32_zero.
