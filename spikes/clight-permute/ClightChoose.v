(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar.
Import ListNotations.
Open Scope Z_scope.

Fixpoint descending_position (xs : list Z) (k : nat) : nat :=
  match k with
  | O => O
  | S k' =>
      if Z.eq_dec (nth k' xs 0) (Z.of_nat k')
      then descending_position xs k' else k'
  end.

Definition choose_scan :=
  loop (gt (reg pos) (lit 0))
    (seq [set pos (sub (reg pos) (lit 1));
          when (ne (cell permutation (reg pos)) (reg pos)) Sbreak]).

Lemma descending_position_bound xs k : (descending_position xs k <= k)%nat.
Proof.
  induction k; simpl; [lia|]. destruct (Z.eq_dec (nth k xs 0) (Z.of_nat k)); lia.
Qed.

Lemma exec_if_test ge e le m a yes no b le' out :
  expression ge le m a = Some (Val.of_bool b) -> typeof a = i32 ->
  exec_stmt function_entry2 ge e le m (if b then yes else no) E0 le' m out ->
  exec_stmt function_entry2 ge e le m (Sifthenelse a yes no) E0 le' m out.
Proof.
  intros E T S. eapply exec_Sifthenelse.
  - eapply expression_sound. exact E.
  - rewrite T. apply bool_comparison.
  - exact S.
Qed.

Lemma nth_array_load m b xs k :
  array_at m b xs -> (k < length xs)%nat ->
  Mem.load Mint32 m b (4 * Z.of_nat k) = Some (Vint (Int.repr (nth k xs 0))).
Proof.
  intros A K. assert (N : nth_error xs k = Some (nth k xs 0)).
  { apply nth_error_nth'. exact K. }
  exact (proj1 (A k (nth k xs 0) N)).
Qed.

Lemma scan_expression ge le m b xs k :
  PTree.get permutation le = Some (Vptr b Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat k))) ->
  array_at m b xs -> (k < length xs <= 1024)%nat ->
  expression ge le m (cell permutation (reg pos)) =
    Some (Vint (Int.repr (nth k xs 0))).
Proof.
  intros B P A K. eapply cell_expression; eauto; try reflexivity.
  - lia.
  - apply nth_array_load; tauto.
Qed.

(* This proves the actual descending loop. The array hypothesis supplies all
   loads; there is no assumption that a selected expression executes. *)
Theorem choose_scan_array ge e m b xs :
  array_at m b xs -> (length xs <= 1024)%nat ->
  Forall uint xs ->
  forall k le,
  (k < length xs)%nat ->
  PTree.get permutation le = Some (Vptr b Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat k))) ->
  exec_stmt function_entry2 ge e le m choose_scan E0
    (PTree.set pos (Vint (Int.repr (Z.of_nat (descending_position xs k)))) le)
    m Out_normal.
Proof.
  intros A Size Values k. induction k as [|k IH]; intros le K B P.
  - simpl descending_position. rewrite (PTree.gsident pos le P).
    unfold choose_scan, loop. eapply exec_Sloop_stop1 with (out' := Out_break).
    + eapply exec_Sseq_2; [|discriminate].
      eapply exec_if_test with (b := false); [|reflexivity|constructor].
      unfold gt. exact (expression_compare ge le m Cgt (reg pos) (lit 0)
        0 0 eq_refl eq_refl ltac:(unfold uint; cbn; lia)
        ltac:(unfold uint; cbn; lia) P eq_refl).
    + constructor.
  - set (le1 := PTree.set pos (Vint (Int.repr (Z.of_nat k))) le).
    assert (KU : uint (Z.of_nat k)).
    { unfold uint; change (0 <= Z.of_nat k <= 4294967295); lia. }
    assert (SU : uint (Z.of_nat (S k))).
    { unfold uint; change (0 <= Z.of_nat (S k) <= 4294967295); lia. }
    assert (B1 : PTree.get permutation le1 = Some (Vptr b Ptrofs.zero)).
    { unfold le1. rewrite PTree.gso by discriminate. exact B. }
    assert (P1 : PTree.get pos le1 = Some (Vint (Int.repr (Z.of_nat k)))).
    { unfold le1. apply PTree.gss. }
    assert (Read : expression ge le1 m (cell permutation (reg pos)) =
        Some (Vint (Int.repr (nth k xs 0)))).
    { eapply scan_expression; eauto; lia. }
    assert (Value : uint (nth k xs 0)).
    { apply Forall_forall with (x := nth k xs 0) in Values; [exact Values|].
      apply nth_In. lia. }
    assert (Guard : expression ge le m (gt (reg pos) (lit 0)) = Some (Val.of_bool true)).
    { unfold gt. pose proof (expression_compare ge le m Cgt (reg pos) (lit 0)
        (Z.of_nat (S k)) 0 eq_refl eq_refl SU ltac:(unfold uint; cbn; lia) P eq_refl) as G.
      unfold zcompare in G. destruct (zlt 0 (Z.of_nat (S k))); [exact G|lia]. }
    assert (Decrement : expression ge le m (sub (reg pos) (lit 1)) =
        Some (Vint (Int.repr (Z.of_nat k)))).
    { replace (Z.of_nat k) with (Z.of_nat (S k) - 1) by lia.
      eapply expression_sub; eauto; try reflexivity.
      unfold uint; change (0 <= 1 <= 4294967295); lia. }
    assert (Different : expression ge le1 m (ne (cell permutation (reg pos)) (reg pos)) =
        Some (Val.of_bool (zcompare Cne (nth k xs 0) (Z.of_nat k)))).
    { unfold ne. eapply (expression_compare ge le1 m Cne); eauto; reflexivity. }
    destruct (Z.eq_dec (nth k xs 0) (Z.of_nat k)) as [Equal|Unequal] eqn:Choice.
    + assert (Test : zcompare Cne (nth k xs 0) (Z.of_nat k) = false).
      { unfold zcompare. destruct (zeq (nth k xs 0) (Z.of_nat k)); congruence. }
      rewrite Test in Different.
      assert (Body : exec_stmt function_entry2 ge e le m
          (Ssequence (Sifthenelse (gt (reg pos) (lit 0)) Sskip Sbreak)
            (seq [set pos (sub (reg pos) (lit 1));
                  when (ne (cell permutation (reg pos)) (reg pos)) Sbreak]))
          E0 le1 m Out_normal).
      { change E0 with (E0 ** E0). eapply exec_Sseq_1.
        - eapply exec_if_test; [exact Guard|reflexivity|constructor].
        - cbn [seq fold_right]. change E0 with (E0 ** E0). eapply exec_Sseq_1.
          + unfold set, le1. constructor. apply expression_sound. exact Decrement.
          + change E0 with (E0 ** E0). eapply exec_Sseq_1.
            * unfold when. eapply exec_if_test; [exact Different|reflexivity|constructor].
            * constructor. }
      specialize (IH le1 ltac:(lia) B1 P1).
      unfold le1 in IH. rewrite PTree.set2 in IH.
      simpl descending_position. rewrite Choice.
      unfold choose_scan, loop in *. change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop; [exact Body|constructor|constructor|exact IH].
    + assert (Test : zcompare Cne (nth k xs 0) (Z.of_nat k) = true).
      { unfold zcompare. destruct (zeq (nth k xs 0) (Z.of_nat k)); congruence. }
      rewrite Test in Different.
      simpl descending_position. rewrite Choice.
      unfold choose_scan, loop. eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
      change E0 with (E0 ** E0). eapply exec_Sseq_1.
      * eapply exec_if_test; [exact Guard|reflexivity|constructor].
      * cbn [seq fold_right]. change E0 with (E0 ** E0). eapply exec_Sseq_1.
        -- unfold set, le1. constructor. apply expression_sound. exact Decrement.
        -- eapply exec_Sseq_2; [|discriminate].
           unfold when. eapply exec_if_test; [exact Different|reflexivity|constructor].
Qed.

Print Assumptions choose_scan_array.

Definition selection_outcome xs k :=
  if zeq (nth k xs 0) (Z.of_nat k)
  then Out_return (Some (Vint Int.zero, u32)) else Out_normal.

Definition choose_result xs k :=
  if zeq (nth k xs 0) (Z.of_nat k)
  then let selected := descending_position xs k in
       (Z.of_nat selected, selection_outcome xs selected)
  else (nth k xs 0, Out_normal).

Lemma exec_seq_single ge e le m s le' out :
  exec_stmt function_entry2 ge e le m s E0 le' m out ->
  exec_stmt function_entry2 ge e le m (seq [s]) E0 le' m out.
Proof.
  intro S. cbn [seq fold_right]. destruct out;
    try (eapply exec_Sseq_2; [exact S|discriminate]).
  change E0 with (E0 ** E0). eapply exec_Sseq_1; [exact S|constructor].
Qed.

Lemma choose_tail_array ge e le m b xs k :
  array_at m b xs -> (k < length xs <= 1024)%nat -> Forall uint xs ->
  PTree.get permutation le = Some (Vptr b Ptrofs.zero) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat k))) ->
  exec_stmt function_entry2 ge e le m
    (when (eq (cell permutation (reg pos)) (reg pos)) (ret 0))
    E0 le m (selection_outcome xs k).
Proof.
  intros A K Values B P.
  assert (KU : uint (Z.of_nat k)).
  { unfold uint; change (0 <= Z.of_nat k <= 4294967295); lia. }
  assert (Value : uint (nth k xs 0)).
  { apply Forall_forall with (x := nth k xs 0) in Values; [exact Values|].
    apply nth_In. lia. }
  assert (Read : expression ge le m (cell permutation (reg pos)) =
      Some (Vint (Int.repr (nth k xs 0)))).
  { eapply scan_expression; eauto. }
  pose proof (expression_compare ge le m Ceq (cell permutation (reg pos)) (reg pos)
    (nth k xs 0) (Z.of_nat k) eq_refl eq_refl Value KU Read P) as Test.
  unfold selection_outcome, zcompare in *. destruct (zeq (nth k xs 0) (Z.of_nat k)).
  - unfold when. eapply exec_if_test; [exact Test|reflexivity|].
    unfold ret. constructor. constructor.
  - unfold when. eapply exec_if_test; [exact Test|reflexivity|constructor].
Qed.

(* The complete choose_position AST is read-only. Its only changed register
   is pos. The result below describes both the return-zero path and the
   selected-position path for every initialized array in the size bound. *)
Theorem choose_position_array ge e le m b xs t :
  array_at m b xs -> (t < length xs <= 1024)%nat -> Forall uint xs ->
  PTree.get permutation le = Some (Vptr b Ptrofs.zero) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  exec_stmt function_entry2 ge e le m choose_position E0
    (PTree.set pos (Vint (Int.repr (fst (choose_result xs t)))) le)
    m (snd (choose_result xs t)).
Proof.
  intros A K Values B T.
  assert (TU : uint (Z.of_nat t)).
  { unfold uint; change (0 <= Z.of_nat t <= 4294967295); lia. }
  assert (Value : uint (nth t xs 0)).
  { apply Forall_forall with (x := nth t xs 0) in Values; [exact Values|].
    apply nth_In. lia. }
  assert (Read : expression ge le m (cell permutation (reg top)) =
      Some (Vint (Int.repr (nth t xs 0)))).
  { eapply cell_expression; eauto; try reflexivity; [lia|].
    apply nth_array_load; tauto. }
  set (le1 := PTree.set pos (Vint (Int.repr (nth t xs 0))) le).
  assert (P1 : PTree.get pos le1 = Some (Vint (Int.repr (nth t xs 0)))).
  { unfold le1. apply PTree.gss. }
  assert (T1 : PTree.get top le1 = Some (Vint (Int.repr (Z.of_nat t)))).
  { unfold le1. rewrite PTree.gso by discriminate. exact T. }
  assert (B1 : PTree.get permutation le1 = Some (Vptr b Ptrofs.zero)).
  { unfold le1. rewrite PTree.gso by discriminate. exact B. }
  pose proof (expression_compare ge le1 m Ceq (reg pos) (reg top)
    (nth t xs 0) (Z.of_nat t) eq_refl eq_refl Value TU P1 T1) as Test.
  unfold choose_result, zcompare in *. destruct (zeq (nth t xs 0) (Z.of_nat t)) as [Equal|Unequal].
  - cbn [fst snd].
    set (selected := descending_position xs t).
    set (le2 := PTree.set pos (Vint (Int.repr (Z.of_nat selected))) le).
    assert (Selected : (selected < length xs <= 1024)%nat).
    { unfold selected. pose proof (descending_position_bound xs t). lia. }
    assert (Scan : exec_stmt function_entry2 ge e le1 m choose_scan E0 le2 m Out_normal).
    { pose proof (choose_scan_array ge e m b xs A (proj2 K) Values t le1
        (proj1 K) B1 ltac:(rewrite <- Equal; exact P1)) as S.
      unfold le1 in S. rewrite PTree.set2 in S. exact S. }
    assert (B2 : PTree.get permutation le2 = Some (Vptr b Ptrofs.zero)).
    { unfold le2. rewrite PTree.gso by discriminate. exact B. }
    assert (P2 : PTree.get pos le2 = Some (Vint (Int.repr (Z.of_nat selected)))).
    { unfold le2. apply PTree.gss. }
    pose proof (choose_tail_array ge e le2 m b xs selected A Selected Values B2 P2) as Tail.
    unfold choose_position. cbn [seq fold_right].
    change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le1) (m1 := m).
    + unfold set, le1. constructor. apply expression_sound. exact Read.
    + apply exec_seq_single. unfold when at 1.
      eapply exec_if_test; [exact Test|reflexivity|].
      change E0 with (E0 ** E0). eapply exec_Sseq_1; [exact Scan|].
      exact (exec_seq_single ge e le2 m _ le2 _ Tail).
  - cbn [fst snd]. unfold choose_position. cbn [seq fold_right].
    change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le1) (m1 := m).
    + unfold set, le1. constructor. apply expression_sound. exact Read.
    + apply exec_seq_single. unfold when at 1.
      eapply exec_if_test; [exact Test|reflexivity|constructor].
Qed.

Print Assumptions choose_position_array.
