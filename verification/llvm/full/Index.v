(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  Operations EOU.
Require Import WordMemory Instructions Entry.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.

Definition index_value (x : Z) : dvalue :=
  DVALUE_Base (DVALUE_I 64 (LLVMInt.repr x)).

Lemma index_add x : 0 <= x <= 1024 ->
  eval_iop (Add false false) (index_value x) (index_value 1) =
    raise_ret (index_value (x + 1)).
Proof.
  intro Bound.
  change (raise_ret (DVALUE_Base (DVALUE_I 64
    (LLVMInt.add (LLVMInt.repr x) (LLVMInt.repr 1)))) =
    raise_ret (index_value (x + 1))).
  rewrite LLVMInt.add_unsigned.
  rewrite !LLVMInt.unsigned_repr by
    (change (@LLVMInt.max_unsigned 64) with 18446744073709551615; lia).
  reflexivity.
Qed.

Lemma index_eq x y : 0 <= x <= 1024 -> 0 <= y <= 1024 ->
  eval_icmp false Eq (index_value x) (index_value y) =
    raise_ret (boolean_value (x =? y)).
Proof.
  intros X Y.
  change (raise_ret (DVALUE_Base
    (if @LLVMInt.eq 64 (LLVMInt.repr x) (LLVMInt.repr y)
      then DVALUE_I 1 LLVMInt.one else DVALUE_I 1 LLVMInt.zero)) =
    raise_ret (boolean_value (x =? y))).
  unfold LLVMInt.eq.
  rewrite !LLVMInt.unsigned_repr by
    (change (@LLVMInt.max_unsigned 64) with 18446744073709551615; lia).
  unfold Vellvm.Numeric.Rocqlib.zeq.
  destruct (Z.eq_dec x y); destruct (Z.eqb_spec x y); try congruence; reflexivity.
Qed.

Lemma index_gep address provenance x : 0 <= x <= 1024 ->
  eval_gep (DTYPE_I 32) (pointer_value address provenance) (index_value x :: nil) =
    raise_ret (pointer_value (address + 4 * x) provenance).
Proof.
  intro Bound.
  change (raise_ret (pointer_value
    (address + 4 * @LLVMInt.signed 64 (LLVMInt.repr x)) provenance) =
    raise_ret (pointer_value (address + 4 * x) provenance)).
  rewrite LLVMInt.signed_repr by
    (change (-9223372036854775808 <= x <= 9223372036854775807); lia).
  reflexivity.
Qed.

Lemma extend_word n :
  convert_pure (Zext false) (DTYPE_I 32) (word_value n) (DTYPE_I 64) =
    raise_ret (index_value (Int.unsigned n)).
Proof.
  change (raise_ret (index_value
    (@LLVMInt.unsigned 32 (LLVMInt.repr (Int.unsigned n)))) =
    raise_ret (index_value (Int.unsigned n))).
  rewrite LLVMInt.unsigned_repr by
    (pose proof (Int.unsigned_range n) as Range;
     change (0 <= Int.unsigned n < 4294967296) in Range;
     change (0 <= Int.unsigned n <= 4294967295); lia).
  reflexivity.
Qed.

Lemma word_eq x y :
  eval_icmp false Eq (word_value x) (word_value y) =
    raise_ret (boolean_value (Int.unsigned x =? Int.unsigned y)).
Proof.
  change (raise_ret (DVALUE_Base
    (if @LLVMInt.eq 32 (LLVMInt.repr (Int.unsigned x)) (LLVMInt.repr (Int.unsigned y))
      then DVALUE_I 1 LLVMInt.one else DVALUE_I 1 LLVMInt.zero)) =
    raise_ret (boolean_value (Int.unsigned x =? Int.unsigned y))).
  unfold LLVMInt.eq.
  rewrite !LLVMInt.unsigned_repr by
    (pose proof (Int.unsigned_range x) as X;
     pose proof (Int.unsigned_range y) as Y;
     change (0 <= Int.unsigned x < 4294967296) in X;
     change (0 <= Int.unsigned y < 4294967296) in Y;
     change (@LLVMInt.max_unsigned 32) with 4294967295; lia).
  unfold Vellvm.Numeric.Rocqlib.zeq.
  destruct (Z.eq_dec (Int.unsigned x) (Int.unsigned y));
    destruct (Z.eqb_spec (Int.unsigned x) (Int.unsigned y));
    try congruence; reflexivity.
Qed.

Lemma word_lt x y :
  eval_icmp false Ult (word_value x) (word_value y) =
    raise_ret (boolean_value (Int.unsigned x <? Int.unsigned y)).
Proof.
  change (raise_ret (DVALUE_Base
    (if @LLVMInt.ltu 32 (LLVMInt.repr (Int.unsigned x)) (LLVMInt.repr (Int.unsigned y))
      then DVALUE_I 1 LLVMInt.one else DVALUE_I 1 LLVMInt.zero)) =
    raise_ret (boolean_value (Int.unsigned x <? Int.unsigned y))).
  unfold LLVMInt.ltu.
  rewrite !LLVMInt.unsigned_repr by
    (pose proof (Int.unsigned_range x) as X;
     pose proof (Int.unsigned_range y) as Y;
     change (0 <= Int.unsigned x < 4294967296) in X;
     change (0 <= Int.unsigned y < 4294967296) in Y;
     change (@LLVMInt.max_unsigned 32) with 4294967295; lia).
  unfold Vellvm.Numeric.Rocqlib.zlt.
  destruct (Z_lt_dec (Int.unsigned x) (Int.unsigned y));
    destruct (Z.ltb_spec (Int.unsigned x) (Int.unsigned y)); try lia; reflexivity.
Qed.

Lemma small_unsigned x : 0 <= x <= 1024 -> Int.unsigned (Int.repr x) = x.
Proof.
  intro Bound. apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia.
Qed.

Lemma truncate_index x : 0 <= x <= 1024 ->
  convert_pure (Trunc false false) (DTYPE_I 64) (index_value x) (DTYPE_I 32) =
    raise_ret (word_value (Int.repr x)).
Proof.
  intro Bound.
  change (raise_ret (DVALUE_Base (DVALUE_I 32
    (LLVMInt.repr (@LLVMInt.unsigned 64 (LLVMInt.repr x))))) =
    raise_ret (word_value (Int.repr x))).
  rewrite LLVMInt.unsigned_repr by
    (change (@LLVMInt.max_unsigned 64) with 18446744073709551615; lia).
  unfold word_value. rewrite small_unsigned by exact Bound. reflexivity.
Qed.
