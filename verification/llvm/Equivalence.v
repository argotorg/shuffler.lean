(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith String.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers Values Memory Ctypes Clight ClightBigstep Events.
From Vellvm Require Import Syntax DynamicValues TopLevel Params ParamsV IPtrInfinite.
Require Import ClightDepth Program PureResult.
Import ListNotations.
Open Scope string_scope.
Module LLVMInt := Vellvm.Numeric.Integers.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.

Definition word (x : Z) : dvalue :=
  DVALUE_Base (DVALUE_I 32 (LLVMInt.repr x)).

Definition run (p : ll_toplevel_entities) (x y : Z) :=
  ITree.map snd (interpreter_gen (DTYPE_I 32) (Name "shuffler_depth")
    (Ret [word x; word y]) p).

Lemma subtract_representatives x y :
  @LLVMInt.sub 32 (LLVMInt.repr x) (LLVMInt.repr y) =
  LLVMInt.repr (x - y).
Proof.
  unfold LLVMInt.sub.
  apply LLVMInt.eqm_samerepr, LLVMInt.eqm_sub;
    apply LLVMInt.eqm_sym, LLVMInt.eqm_unsigned_repr.
Qed.

Theorem llvm_call x y :
  eutt eq (run program x y) (Ret (word (x - y))).
Proof.
  apply (pure_result_sound 1000).
  cbv -[LLVMInt.repr LLVMInt.unsigned LLVMInt.sub Z.sub].
  now rewrite subtract_representatives.
Qed.

Lemma word_clight_sub x y :
  word (Int.unsigned x - Int.unsigned y) = word (Int.unsigned (Int.sub x y)).
Proof.
  unfold word, Int.sub.
  rewrite Int.unsigned_repr_eq.
  f_equal; f_equal.
  apply LLVMInt.eqm_samerepr.
  unfold LLVMInt.eqm.
  change (LLVMInt.eqmod 4294967296
    (Int.unsigned x - Int.unsigned y)
    ((Int.unsigned x - Int.unsigned y) mod 4294967296))%Z.
  apply LLVMInt.eqmod_mod.
Qed.

(* The comparison is a complete call with two defined uint32 arguments.
   Clight memory is unchanged. Vellvm starts with its default initial state;
   its private final interpreter state is hidden by [run]. *)
Definition equivalent (p : ll_toplevel_entities) : Prop :=
  forall ge m x y,
    eval_funcall function_entry2 ge m (Internal depth_function)
      [Vint x; Vint y] E0 m (Vint (Int.sub x y)) /\
    eutt eq (run p (Int.unsigned x) (Int.unsigned y))
      (Ret (word (Int.unsigned (Int.sub x y)))).

Theorem depth_equivalence : equivalent program.
Proof.
  intros ge m x y; split.
  - apply depth_clight_call.
  - rewrite <- word_clight_sub. apply llvm_call.
Qed.

Definition certified_module : {p : ll_toplevel_entities | equivalent p} :=
  exist _ program depth_equivalence.
