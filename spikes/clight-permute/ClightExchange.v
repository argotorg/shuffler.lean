(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightSwap
  ClightScalar ClightEntry.
Import ListNotations.

(* Equal values only exchange their destinations. In particular, this branch
   does not inspect the depth limit or read or write the trace buffer. *)
Theorem equal_values_exchange ge e le m bd bp xs destinations p t x pp pt :
  bd <> bp ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat p))) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  (length xs <= 1024)%nat -> (length destinations <= 1024)%nat ->
  nth_error xs p = Some x -> nth_error xs t = Some x ->
  nth_error destinations p = Some pp -> nth_error destinations t = Some pt ->
  array_at m bd xs -> array_at m bp destinations ->
  exists m',
    exec_stmt function_entry2 ge e le m exchange E0
      (PTree.set tmp (Vint (Int.repr pp)) le) m' Out_normal /\
    array_at m' bd xs /\
    array_at m' bp (replace_nth t pp (replace_nth p pt destinations)) /\
    (forall other ys, other <> bp -> array_at m other ys -> array_at m' other ys) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros Separate Data Perm Position Top XS PS XP XT PP PT AD AP.
  assert (PK : (0 <= Z.of_nat p <= 2048)%Z).
  { assert (p < length xs)%nat by (apply nth_error_Some; rewrite XP; discriminate).
    lia. }
  assert (TK : (0 <= Z.of_nat t <= 2048)%Z).
  { assert (t < length xs)%nat by (apply nth_error_Some; rewrite XT; discriminate).
    lia. }
  assert (RP : expression ge le m (cell data (reg pos)) = Some (Vint (Int.repr x))).
  { eapply cell_expression; eauto. exact (proj1 (AD p x XP)). }
  assert (RT : expression ge le m (cell data (reg top)) = Some (Vint (Int.repr x))).
  { eapply cell_expression; eauto. exact (proj1 (AD t x XT)). }
  assert (C : expression ge le m (ne (cell data (reg pos)) (cell data (reg top))) =
    Some Vfalse).
  { cbn [ne expression]. rewrite RP, RT.
    change (Some (Val.of_bool (negb (Int.eq (Int.repr x) (Int.repr x)))) = Some Vfalse).
    rewrite Int.eq_true. reflexivity. }
  destruct (swap_cells_array_full ge e le m permutation bp destinations p t pp pt
    ltac:(discriminate) Perm Position Top PS PP PT AP)
    as [m' [Swap [Result [Frame Writable]]]].
  exists m'. split.
  - unfold exchange, seq. cbn [fold_right].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    + unfold when. eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      * eapply expression_sound. exact C.
      * reflexivity.
      * constructor.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * exact Swap.
      * constructor.
  - split; [apply Frame; assumption|]. split; [exact Result|]. split; assumption.
Qed.

Print Assumptions equal_values_exchange.

Theorem blocked_exchange ge e le m bd bo xs p t x y count old_pos old_excess :
  bd <> bo ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get out le = Some (Vptr bo Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat p))) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  (length xs <= 1024)%nat ->
  nth_error xs p = Some x -> nth_error xs t = Some y ->
  uint x -> uint y -> x <> y -> (p + 16 < t)%nat ->
  array_at m bd xs -> array_at m bo [count; old_pos; old_excess] ->
  exists m',
    exec_stmt function_entry2 ge e le m exchange E0
      (PTree.set depth (Vint (Int.repr (Z.of_nat t - Z.of_nat p))) le) m'
      (Out_return (Some (Vint (Int.repr 1), u32))) /\
    array_at m' bd xs /\
    array_at m' bo [count; Z.of_nat p; Z.of_nat t - Z.of_nat p - 16] /\
    (forall other ys, other <> bo -> array_at m other ys -> array_at m' other ys).
Proof.
  intros Separate Data Out Position Top XS XP XT X Y Different Far AD AO.
  assert (PB : (p < length xs)%nat).
  { apply nth_error_Some. rewrite XP. discriminate. }
  assert (TB : (t < length xs)%nat).
  { apply nth_error_Some. rewrite XT. discriminate. }
  assert (PK : (0 <= Z.of_nat p <= 2048)%Z) by lia.
  assert (TK : (0 <= Z.of_nat t <= 2048)%Z) by lia.
  assert (UP : uint (Z.of_nat p)).
  { change (0 <= Z.of_nat p <= 4294967295)%Z. lia. }
  assert (UT : uint (Z.of_nat t)).
  { change (0 <= Z.of_nat t <= 4294967295)%Z. lia. }
  assert (UD : uint (Z.of_nat t - Z.of_nat p)).
  { change (0 <= Z.of_nat t - Z.of_nat p <= 4294967295)%Z. lia. }
  assert (RP : expression ge le m (cell data (reg pos)) = Some (Vint (Int.repr x))).
  { eapply cell_expression; eauto. exact (proj1 (AD p x XP)). }
  assert (RT : expression ge le m (cell data (reg top)) = Some (Vint (Int.repr y))).
  { eapply cell_expression; eauto. exact (proj1 (AD t y XT)). }
  assert (DifferentC : expression ge le m
    (ne (cell data (reg pos)) (cell data (reg top))) = Some Vtrue).
  { pose proof (expression_compare ge le m Cne (cell data (reg pos))
      (cell data (reg top)) x y eq_refl eq_refl X Y RP RT) as C.
    unfold zcompare in C. destruct (Coqlib.zeq x y); [contradiction|exact C]. }
  assert (Distance : expression ge le m (sub (reg top) (reg pos)) =
      Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))).
  { eapply expression_sub; eauto. }
  set (le1 := PTree.set depth (Vint (Int.repr (Z.of_nat t - Z.of_nat p))) le).
  assert (Out1 : PTree.get out le1 = Some (Vptr bo Ptrofs.zero)).
  { unfold le1. rewrite PTree.gso by discriminate. exact Out. }
  assert (Position1 : PTree.get pos le1 = Some (Vint (Int.repr (Z.of_nat p)))).
  { unfold le1. rewrite PTree.gso by discriminate. exact Position. }
  assert (Depth1 : forall memory, expression ge le1 memory (reg depth) =
      Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))).
  { intro memory. change (PTree.get depth le1 =
      Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))) .
    unfold le1. apply PTree.gss. }
  assert (U16 : uint 16) by (change (0 <= 16 <= 4294967295)%Z; lia).
  assert (Blocked : expression ge le1 m (gt (reg depth) (lit 16)) = Some Vtrue).
  { pose proof (expression_compare ge le1 m Cgt (reg depth) (lit 16) _ 16 eq_refl eq_refl
      UD U16 (Depth1 m) eq_refl) as C.
    unfold zcompare in C. destruct (Coqlib.zlt 16 (Z.of_nat t - Z.of_nat p));
      [exact C|lia]. }
  destruct (array_store_exists m bo [count; old_pos; old_excess] 1 (Z.of_nat p) AO
    ltac:(simpl; lia)) as [m1 W1].
  pose proof (array_store_same m m1 bo _ 1 (Z.of_nat p) AO W1) as A1.
  destruct (array_store_exists m1 bo _ 2 (Z.of_nat t - Z.of_nat p - 16) A1
    ltac:(simpl; lia)) as [m2 W2].
  assert (S1 : store ge le1 m (cell out (lit 1)) (reg pos) = Some m1).
  { eapply cell_store with (b := bo) (k := 1%Z) (value := Z.of_nat p);
      eauto; reflexivity || lia. }
  assert (S2 : store ge le1 m1 (cell out (lit 2)) (sub (reg depth) (lit 16)) = Some m2).
  { eapply cell_store with (b := bo) (k := 2%Z)
      (value := (Z.of_nat t - Z.of_nat p - 16)%Z); eauto; try reflexivity; try lia.
    eapply expression_sub; eauto. }
  exists m2. split.
  - unfold exchange, seq. cbn [fold_right].
    eapply exec_Sseq_2; [|discriminate].
    unfold when at 1. eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
    + eapply expression_sound. exact DifferentC.
    + reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_Sset. eapply expression_sound. exact Distance.
      * eapply exec_Sseq_2; [|discriminate].
        unfold when at 1. eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
        -- eapply expression_sound. exact Blocked.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
           ++ now apply exec_store.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m2).
              ** now apply exec_store.
              ** eapply exec_Sseq_2; [|discriminate].
                 apply exec_Sreturn_some. constructor.
  - assert (Frame : forall other ys, other <> bo -> array_at m other ys ->
        array_at m2 other ys).
    { intros other ys Disjoint Other.
      eapply array_store_disjoint; [|exact Disjoint|exact W2].
      eapply array_store_disjoint; eauto. }
    split; [apply Frame; assumption|]. split; [|exact Frame].
    exact (array_store_same m1 m2 bo _ 2 _ A1 W2).
Qed.

Print Assumptions blocked_exchange.
