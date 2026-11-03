(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Cop Clight.
Require Import Permute ClightEval.
Open Scope Z_scope.

Definition uint (x : Z) := 0 <= x <= Int.max_unsigned.

Definition zcompare (c : comparison) (x y : Z) : bool :=
  match c with
  | Ceq => if zeq x y then true else false
  | Cne => if zeq x y then false else true
  | Clt => if zlt x y then true else false
  | Cle => if zlt y x then false else true
  | Cgt => if zlt y x then true else false
  | Cge => if zlt x y then false else true
  end.

Lemma unsigned_compare m c x y :
  uint x -> uint y ->
  sem_cmp c (Vint (Int.repr x)) u32 (Vint (Int.repr y)) u32 m =
    Some (Val.of_bool (zcompare c x y)).
Proof.
  intros X Y.
  change (Some (Val.of_bool (Int.cmpu c (Int.repr x) (Int.repr y))) =
    Some (Val.of_bool (zcompare c x y))).
  unfold Int.cmpu, Int.eq, Int.ltu.
  rewrite !Int.unsigned_repr by assumption.
  destruct c; cbn [zcompare]; try reflexivity;
    destruct (zeq x y); destruct (zlt x y); destruct (zlt y x); reflexivity.
Qed.

Lemma expression_add ge le m a b x y :
  typeof a = u32 -> typeof b = u32 -> uint x -> uint y ->
  expression ge le m a = Some (Vint (Int.repr x)) ->
  expression ge le m b = Some (Vint (Int.repr y)) ->
  expression ge le m (add a b) = Some (Vint (Int.repr (x + y))).
Proof.
  intros A B X Y Ex Ey. cbn [add expression]. rewrite Ex, Ey, A, B.
  change (Some (Vint (Int.add (Int.repr x) (Int.repr y))) =
    Some (Vint (Int.repr (x + y)))).
  unfold Int.add. rewrite !Int.unsigned_repr by assumption. reflexivity.
Qed.

Lemma expression_sub ge le m a b x y :
  typeof a = u32 -> typeof b = u32 -> uint x -> uint y ->
  expression ge le m a = Some (Vint (Int.repr x)) ->
  expression ge le m b = Some (Vint (Int.repr y)) ->
  expression ge le m (sub a b) = Some (Vint (Int.repr (x - y))).
Proof.
  intros A B X Y Ex Ey. cbn [sub expression]. rewrite Ex, Ey, A, B.
  change (Some (Vint (Int.sub (Int.repr x) (Int.repr y))) =
    Some (Vint (Int.repr (x - y)))).
  unfold Int.sub. rewrite !Int.unsigned_repr by assumption. reflexivity.
Qed.

Definition compare_op (c : comparison) :=
  match c with
  | Ceq => Oeq | Cne => One | Clt => Olt
  | Cle => Ole | Cgt => Ogt | Cge => Oge
  end.

Lemma expression_compare ge le m c a b x y :
  typeof a = u32 -> typeof b = u32 -> uint x -> uint y ->
  expression ge le m a = Some (Vint (Int.repr x)) ->
  expression ge le m b = Some (Vint (Int.repr y)) ->
  expression ge le m (Ebinop (compare_op c) a b i32) =
    Some (Val.of_bool (zcompare c x y)).
Proof.
  intros A B X Y Ex Ey. cbn [expression]. rewrite Ex, Ey, A, B.
  destruct c; apply unsigned_compare; assumption.
Qed.

Lemma bool_comparison m b : bool_val (Val.of_bool b) i32 m = Some b.
Proof. destruct b; reflexivity. Qed.

(* Addition/subtraction above describes unsigned modular arithmetic. A caller
   must separately establish uint(x+y) or uint(x-y) to rule out wrapping. *)
Print Assumptions expression_compare.
