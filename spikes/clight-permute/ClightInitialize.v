(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar.
Import ListNotations.
Open Scope Z_scope.

Definition zero_prefix (m : mem) (b : block) (count : nat) : Prop :=
  forall k, (k < count)%nat ->
    Mem.load Mint32 m b (4 * Z.of_nat k) = Some (Vint (Int.repr 0)).

Lemma zero_prefix_extend m m' b k :
  zero_prefix m b k ->
  Mem.store Mint32 m b (4 * Z.of_nat k) (Vint (Int.repr 0)) = Some m' ->
  zero_prefix m' b (S k).
Proof.
  intros P W j J. destruct (Nat.eq_dec j k) as [->|D].
  - exact (Mem.load_store_same Mint32 m b (4 * Z.of_nat k)
      (Vint (Int.repr 0)) m' W).
  - rewrite (Mem.load_store_other Mint32 m b (4 * Z.of_nat k)
      (Vint (Int.repr 0)) m' W).
    + apply P. lia.
    + right. left. change (4 * Z.of_nat j + 4 <= 4 * Z.of_nat k). lia.
Qed.

Lemma loop_test ge le m size index :
  0 <= index <= 1024 -> 0 <= size <= 1024 ->
  PTree.get i le = Some (Vint (Int.repr index)) ->
  PTree.get n le = Some (Vint (Int.repr size)) ->
  expression ge le m (lt (reg i) (reg n)) =
    Some (Val.of_bool (if zlt index size then true else false)).
Proof.
  intros I N Ix Nx.
  change (expression ge le m (Ebinop (compare_op Clt) (reg i) (reg n) i32) =
    Some (Val.of_bool (zcompare Clt index size))).
  apply expression_compare; try reflexivity; try assumption;
    unfold uint; change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma initialize_one ge e le m b index m' :
  PTree.get used le = Some (Vptr b Ptrofs.zero) ->
  PTree.get i le = Some (Vint (Int.repr index)) -> 0 <= index <= 1024 ->
  Mem.store Mint32 m b (4 * index) (Vint (Int.repr 0)) = Some m' ->
  exec_stmt function_entry2 ge e le m (put used (reg i) (lit 0)) E0 le m' Out_normal.
Proof.
  intros B I Bound W.
  eapply execute_sound with (fuel := 1%nat).
  cbn [execute put].
  assert (S : store ge le m (cell used (reg i)) (lit 0) = Some m').
  { eapply cell_store with (b := b) (k := index) (value := 0);
      try reflexivity; try assumption; lia. }
  rewrite S. reflexivity.
Qed.

Lemma increase_index ge e le m index :
  PTree.get i le = Some (Vint (Int.repr index)) -> 0 <= index <= 1024 ->
  exec_stmt function_entry2 ge e le m (inc i) E0
    (PTree.set i (Vint (Int.repr (index + 1))) le) m Out_normal.
Proof.
  intros I Bound. apply exec_Sset. apply expression_sound.
  eapply expression_add; try reflexivity; try exact I;
    unfold uint; change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma initialize_loop ge e size : (size <= 1024)%nat ->
  forall remaining start le m b,
  (start + remaining = size)%nat ->
  PTree.get used le = Some (Vptr b Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat start))) ->
  writable_array m b size -> zero_prefix m b start ->
  exists le' m',
    exec_stmt function_entry2 ge e le m
      (loop (lt (reg i) (reg n)) (seq [put used (reg i) (lit 0); inc i]))
      E0 le' m' Out_normal /\
    zero_prefix m' b size /\ writable_array m' b size /\
    (forall id, id <> i -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m' other xs) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros Size remaining. induction remaining as [|remaining IH];
    intros start le m b Sum Base N I Writable Prefix.
  - assert (Start : start = size) by lia. subst start.
    exists le, m. split.
    + unfold loop. eapply exec_Sloop_stop1 with (out' := Out_break).
      * eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false).
        -- apply expression_sound. rewrite (loop_test ge le m (Z.of_nat size)
          (Z.of_nat size)) by (try assumption; lia).
        destruct (zlt (Z.of_nat size) (Z.of_nat size)); [lia|reflexivity].
        -- apply bool_comparison.
        -- apply exec_Sbreak.
      * constructor.
    + split; [exact Prefix|]. split; [exact Writable|]. split; [auto|]. split; auto.
  - assert (Start : (start < size)%nat) by lia.
    destruct (Mem.valid_access_store m Mint32 b (4 * Z.of_nat start)
      (Vint (Int.repr 0)) (Writable start Start)) as [m1 Store].
    pose (le1 := PTree.set i (Vint (Int.repr (Z.of_nat (S start)))) le).
    assert (Base1 : PTree.get used le1 = Some (Vptr b Ptrofs.zero)).
    { unfold le1. rewrite PTree.gso by discriminate. exact Base. }
    assert (N1 : PTree.get n le1 = Some (Vint (Int.repr (Z.of_nat size)))).
    { unfold le1. rewrite PTree.gso by discriminate. exact N. }
    assert (I1 : PTree.get i le1 = Some (Vint (Int.repr (Z.of_nat (S start))))).
    { unfold le1. apply PTree.gss. }
    assert (Writable1 : writable_array m1 b size).
    { eapply writable_array_store; eauto. }
    assert (Prefix1 : zero_prefix m1 b (S start)).
    { eapply zero_prefix_extend; eauto. }
    destruct (IH (S start) le1 m1 b) as [le' [m' [Execution [Zeros [W [Temps [Frame WritableFrame]]]]]]];
      try assumption; try lia.
    exists le', m'. split.
    + unfold loop in *. eapply exec_Sloop_loop with (le1 := le1) (m1 := m1)
        (le2 := le1) (m2 := m1) (out1 := Out_normal)
        (t1 := E0) (t2 := E0) (t3 := E0).
      * eapply exec_Sseq_1 with (le1 := le) (m1 := m) (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true).
           ++ apply expression_sound. rewrite (loop_test ge le m (Z.of_nat size)
                (Z.of_nat start)) by (try assumption; lia).
              destruct (zlt (Z.of_nat start) (Z.of_nat size)); [reflexivity|lia].
           ++ apply bool_comparison.
           ++ constructor.
        -- cbn [seq fold_right].
           eapply exec_Sseq_1 with (le1 := le) (m1 := m1) (t1 := E0) (t2 := E0).
           ++ eapply initialize_one; eauto. lia.
           ++ eapply exec_Sseq_1 with (le1 := le1) (m1 := m1) (t1 := E0) (t2 := E0).
              ** unfold le1. rewrite Nat2Z.inj_succ.
                 replace (Z.succ (Z.of_nat start)) with (Z.of_nat start + 1) by lia.
                 apply increase_index; [exact I|lia].
              ** constructor.
      * constructor.
      * constructor.
      * exact Execution.
    + split; [exact Zeros|]. split; [exact W|]. split.
      * intros id Different. rewrite Temps by exact Different.
        unfold le1. rewrite PTree.gso by exact Different. reflexivity.
      * split.
        -- intros other xs Different A. apply Frame; [exact Different|].
           eapply array_store_disjoint; eauto.
        -- intros other count Valid. apply WritableFrame.
           eapply writable_array_store; eauto.
Qed.

Lemma zero_prefix_array m b count :
  zero_prefix m b count -> writable_array m b count ->
  array_at m b (repeat 0 count).
Proof.
  intros Prefix Writable k value N.
  assert (Bound : (k < count)%nat).
  { assert (H : (k < length (repeat 0%Z count))%nat).
    { apply nth_error_Some. rewrite N. discriminate. }
    rewrite repeat_length in H. exact H. }
  assert (Value : value = 0).
  { apply nth_error_In in N. apply repeat_spec in N. exact N. }
  subst value. split; [apply Prefix|apply Writable]; exact Bound.
Qed.

(* This is the first loop in check_input. It does not read used before
   writing it. The caller need only supply writable, possibly uninitialized
   storage. Other array objects and all other temporaries are preserved. *)
Theorem initialize_used_array_full ge e le m b size :
  (size <= 1024)%nat ->
  PTree.get used le = Some (Vptr b Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  writable_array m b size ->
  exists le' m',
    exec_stmt function_entry2 ge e le m
      (each i (put used (reg i) (lit 0))) E0 le' m' Out_normal /\
    array_at m' b (repeat 0 size) /\
    (forall id, id <> i -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m' other xs) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros Size Base N Writable.
  pose (le0 := PTree.set i (Vint (Int.repr 0)) le).
  assert (Base0 : PTree.get used le0 = Some (Vptr b Ptrofs.zero)).
  { unfold le0. rewrite PTree.gso by discriminate. exact Base. }
  assert (N0 : PTree.get n le0 = Some (Vint (Int.repr (Z.of_nat size)))).
  { unfold le0. rewrite PTree.gso by discriminate. exact N. }
  assert (I0 : PTree.get i le0 = Some (Vint (Int.repr (Z.of_nat 0)))).
  { unfold le0. apply PTree.gss. }
  assert (Prefix0 : zero_prefix m b 0).
  { intros k K. lia. }
  destruct (initialize_loop ge e size Size size 0 le0 m b eq_refl
    Base0 N0 I0 Writable Prefix0) as [le' [m' [Execution [Prefix [W [Temps [Frame WritableFrame]]]]]]].
  exists le', m'. split.
  - cbn [each seq fold_right].
    eapply exec_Sseq_1 with (le1 := le0) (m1 := m) (t1 := E0) (t2 := E0).
    + apply exec_Sset. constructor.
    + eapply exec_Sseq_1 with (le1 := le') (m1 := m') (t1 := E0) (t2 := E0).
      * exact Execution.
      * constructor.
  - split.
    + now apply zero_prefix_array.
    + split; [|split; [exact Frame|exact WritableFrame]]. intros id Different.
      rewrite Temps by exact Different. unfold le0.
      rewrite PTree.gso by exact Different. reflexivity.
Qed.

Print Assumptions initialize_used_array_full.

Corollary initialize_used_array ge e le m b size :
  (size <= 1024)%nat ->
  PTree.get used le = Some (Vptr b Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  writable_array m b size ->
  exists le' m',
    exec_stmt function_entry2 ge e le m
      (each i (put used (reg i) (lit 0))) E0 le' m' Out_normal /\
    array_at m' b (repeat 0 size) /\
    (forall id, id <> i -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m' other xs).
Proof.
  intros Size Base N Writable.
  destruct (initialize_used_array_full ge e le m b size Size Base N Writable)
    as [le' [m' [Execution [A [Temps [Frame Permissions]]]]]].
  exists le', m'. split; [exact Execution|]. split; [exact A|]. now split.
Qed.
