(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues Operations EOU.
Require Import WordMemory Instructions Entry Index.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.

Lemma word_repr x : word_value (Int.repr x) = DVALUE_Base (DVALUE_I 32 (LLVMInt.repr x)).
Proof.
  unfold word_value. f_equal; f_equal. apply LLVMInt.eqm_samerepr, LLVMInt.eqm_sym.
  rewrite Int.unsigned_repr_eq.
  change (LLVMInt.eqmod 4294967296 x (x mod 4294967296)). apply LLVMInt.eqmod_mod.
Qed.

Lemma integer_add_representatives {width : positive} x y :
  @LLVMInt.add width (LLVMInt.repr x) (LLVMInt.repr y) = LLVMInt.repr (x + y).
Proof.
  unfold LLVMInt.add. apply LLVMInt.eqm_samerepr, LLVMInt.eqm_add;
    apply LLVMInt.eqm_sym, LLVMInt.eqm_unsigned_repr.
Qed.

Lemma integer_sub_representatives {width : positive} x y :
  @LLVMInt.sub width (LLVMInt.repr x) (LLVMInt.repr y) = LLVMInt.repr (x - y).
Proof.
  unfold LLVMInt.sub. apply LLVMInt.eqm_samerepr, LLVMInt.eqm_sub;
    apply LLVMInt.eqm_sym, LLVMInt.eqm_unsigned_repr.
Qed.

Lemma word_add x y :
  eval_iop (Add false false) (word_value (Int.repr x)) (word_value (Int.repr y)) =
    raise_ret (word_value (Int.repr (x + y))).
Proof.
  rewrite !word_repr.
  change (raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.add (LLVMInt.repr x) (LLVMInt.repr y)))) =
    raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (x + y))))).
  rewrite integer_add_representatives. reflexivity.
Qed.

Lemma word_sub x y :
  eval_iop (Sub false false) (word_value (Int.repr x)) (word_value (Int.repr y)) =
    raise_ret (word_value (Int.repr (x - y))).
Proof.
  rewrite !word_repr.
  change (raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.sub (LLVMInt.repr x) (LLVMInt.repr y)))) =
    raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (x - y))))).
  rewrite integer_sub_representatives. reflexivity.
Qed.

Lemma word_double x : 0 <= x <= 1024 ->
  eval_iop (Shl false false) (word_value (Int.repr x)) (word_value Int.one) =
    raise_ret (word_value (Int.repr (2 * x))).
Proof.
  intro Bound. change Int.one with (Int.repr 1). rewrite !word_repr.
  change (raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.shl (LLVMInt.repr x) (LLVMInt.repr 1)))) =
    raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (2 * x))))).
  unfold LLVMInt.shl.
  rewrite LLVMInt.unsigned_repr by (change (0 <= x <= 4294967295); lia).
  change (raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (Z.shiftl x 1)))) =
    raise_ret (DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (2 * x))))).
  rewrite Z.shiftl_mul_pow2 by lia. replace (x * 2 ^ 1) with (2 * x) by ring. reflexivity.
Qed.

Lemma word_gt x y :
  eval_icmp false Ugt (word_value x) (word_value y) =
    raise_ret (boolean_value (Int.unsigned y <? Int.unsigned x)).
Proof.
  change (eval_icmp false Ugt (word_value x) (word_value y)) with
    (eval_icmp false Ult (word_value y) (word_value x)). apply word_lt.
Qed.

Lemma index_decrement x :
  eval_iop (Add false false) (index_value x) (index_value (-1)) =
    raise_ret (index_value (x - 1)).
Proof.
  change (raise_ret (DVALUE_Base (DVALUE_I 64 (LLVMInt.add (LLVMInt.repr x) (LLVMInt.repr (-1))))) =
    raise_ret (index_value (x - 1))).
  rewrite integer_add_representatives. reflexivity.
Qed.

Lemma boolean_and x y :
  eval_iop And (boolean_value x) (boolean_value y) = raise_ret (boolean_value (andb x y)).
Proof. destruct x, y; reflexivity. Qed.

Lemma index_ne x y : 0 <= x <= 1024 -> 0 <= y <= 1024 ->
  eval_icmp false Ne (index_value x) (index_value y) =
    raise_ret (boolean_value (negb (x =? y))).
Proof.
  intros X Y.
  change (raise_ret (DVALUE_Base
    (if negb (@LLVMInt.eq 64 (LLVMInt.repr x) (LLVMInt.repr y))
      then DVALUE_I 1 LLVMInt.one else DVALUE_I 1 LLVMInt.zero)) =
    raise_ret (boolean_value (negb (x =? y)))).
  unfold LLVMInt.eq.
  rewrite !LLVMInt.unsigned_repr by
    (change (@LLVMInt.max_unsigned 64) with 18446744073709551615; lia).
  unfold Vellvm.Numeric.Rocqlib.zeq.
  destruct (Z.eq_dec x y); destruct (Z.eqb_spec x y); try congruence; reflexivity.
Qed.
