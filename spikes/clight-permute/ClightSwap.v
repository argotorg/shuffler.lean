(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs.
Require Import ClightMemory.

(* This is the three-statement AST used for both swaps in exchange. The
   memory theorem below supplies the load and store facts for typed arrays. *)
Lemma swap_cells_execute ge le m a x m1 m2 :
  expression ge le m (cell a (reg pos)) = Some x ->
  store ge (PTree.set tmp x le) m
    (cell a (reg pos)) (cell a (reg top)) = Some m1 ->
  store ge (PTree.set tmp x le) m1
    (cell a (reg top)) (reg tmp) = Some m2 ->
  execute 8 ge le m (swap_cells a) =
    Some (PTree.set tmp x le, m2, Out_normal).
Proof.
  intros R W1 W2.
  cbn [execute swap_cells seq fold_right Permute.set put].
  rewrite R, W1, W2. reflexivity.
Qed.

(* No load/store-success premise is needed here. Writable array ownership
   and in-range indices establish the complete execution and its result. *)
Theorem swap_cells_array_full ge e le m a b xs p t xp xt :
  a <> tmp ->
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat p))) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  (length xs <= 1024)%nat ->
  nth_error xs p = Some xp -> nth_error xs t = Some xt ->
  array_at m b xs ->
  exists m',
    exec_stmt function_entry2 ge e le m (swap_cells a) E0
      (PTree.set tmp (Vint (Int.repr xp)) le) m' Out_normal /\
    array_at m' b (replace_nth t xp (replace_nth p xt xs)) /\
    (forall other ys, other <> b -> array_at m other ys -> array_at m' other ys) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros Different Base Position Top Size P T A.
  assert (PB : (p < length xs)%nat).
  { apply nth_error_Some. rewrite P. discriminate. }
  assert (TB : (t < length xs)%nat).
  { apply nth_error_Some. rewrite T. discriminate. }
  assert (PK : (0 <= Z.of_nat p <= 2048)%Z) by lia.
  assert (TK : (0 <= Z.of_nat t <= 2048)%Z) by lia.
  destruct (array_store_exists m b xs p xt A PB) as [m1 W1].
  pose proof (array_store_same m m1 b xs p xt A W1) as A1.
  assert (TB1 : (t < length (replace_nth p xt xs))%nat).
  { rewrite length_replace_nth. exact TB. }
  destruct (array_store_exists m1 b (replace_nth p xt xs) t xp A1 TB1)
    as [m2 W2].
  set (le1 := PTree.set tmp (Vint (Int.repr xp)) le).
  assert (Base1 : PTree.get a le1 = Some (Vptr b Ptrofs.zero)).
  { unfold le1. rewrite PTree.gso by exact Different. exact Base. }
  assert (Position1 : PTree.get pos le1 = Some (Vint (Int.repr (Z.of_nat p)))).
  { unfold le1. rewrite PTree.gso by discriminate. exact Position. }
  assert (Top1 : PTree.get top le1 = Some (Vint (Int.repr (Z.of_nat t)))).
  { unfold le1. rewrite PTree.gso by discriminate. exact Top. }
  assert (R : expression ge le m (cell a (reg pos)) = Some (Vint (Int.repr xp))).
  { eapply cell_expression; eauto. exact (proj1 (A p xp P)). }
  assert (Rtop : expression ge le1 m (cell a (reg top)) = Some (Vint (Int.repr xt))).
  { eapply cell_expression; eauto. exact (proj1 (A t xt T)). }
  assert (S1 : store ge le1 m (cell a (reg pos)) (cell a (reg top)) = Some m1).
  { eapply cell_store; eauto. }
  assert (S2 : store ge le1 m1 (cell a (reg top)) (reg tmp) = Some m2).
  { eapply cell_store; eauto.
    change (PTree.get tmp le1 = Some (Vint (Int.repr xp))).
    unfold le1. apply PTree.gss. }
  exists m2. split.
  - eapply execute_sound. eapply swap_cells_execute; eauto.
  - split.
    + eapply array_store_same; eauto.
    + split.
      * intros other ys Disjoint Other.
        eapply array_store_disjoint; [|exact Disjoint|exact W2].
        eapply array_store_disjoint; eauto.
      * intros other count Other.
        eapply writable_array_store; [|exact W2].
        eapply writable_array_store; eauto.
Qed.

Theorem swap_cells_array ge e le m a b xs p t xp xt :
  a <> tmp ->
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat p))) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  (length xs <= 1024)%nat ->
  nth_error xs p = Some xp -> nth_error xs t = Some xt ->
  array_at m b xs ->
  exists m',
    exec_stmt function_entry2 ge e le m (swap_cells a) E0
      (PTree.set tmp (Vint (Int.repr xp)) le) m' Out_normal /\
    array_at m' b (replace_nth t xp (replace_nth p xt xs)) /\
    (forall other ys, other <> b -> array_at m other ys -> array_at m' other ys).
Proof.
  intros D B P T N XP XT A.
  destruct (swap_cells_array_full ge e le m a b xs p t xp xt D B P T N XP XT A)
    as [m' [Run [Result [Frame _]]]].
  exists m'. auto.
Qed.

Print Assumptions swap_cells_array_full.

Theorem swap_cells_execution ge e le m a x m1 m2 :
  expression ge le m (cell a (reg pos)) = Some x ->
  store ge (PTree.set tmp x le) m
    (cell a (reg pos)) (cell a (reg top)) = Some m1 ->
  store ge (PTree.set tmp x le) m1
    (cell a (reg top)) (reg tmp) = Some m2 ->
  exec_stmt function_entry2 ge e le m (swap_cells a) E0
    (PTree.set tmp x le) m2 Out_normal.
Proof.
  intros R W1 W2. eapply execute_sound.
  eapply swap_cells_execute; eauto.
Qed.
