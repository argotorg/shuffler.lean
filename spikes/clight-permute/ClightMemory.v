(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Coq Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Ctypes Cop Clight.
Require Import Permute ClightEval.
Import ListNotations.
Open Scope Z_scope.

Definition writable_array (m : mem) (b : block) (count : nat) : Prop :=
  forall k, (k < count)%nat ->
    Mem.valid_access m Mint32 b (4 * Z.of_nat k) Writable.

Lemma writable_array_store m m' b count block' offset value :
  writable_array m b count ->
  Mem.store Mint32 m block' offset value = Some m' ->
  writable_array m' b count.
Proof.
  intros W S k K. eapply Mem.store_valid_access_1; [exact S|]. apply W. exact K.
Qed.

Definition array_at (m : mem) (b : block) (xs : list Z) : Prop :=
  forall k v, nth_error xs k = Some v ->
    Mem.load Mint32 m b (4 * Z.of_nat k) = Some (Vint (Int.repr v)) /\
    Mem.valid_access m Mint32 b (4 * Z.of_nat k) Writable.

Fixpoint replace_nth (k : nat) (v : Z) (xs : list Z) : list Z :=
  match k, xs with
  | O, _ :: rest => v :: rest
  | S k', x :: rest => x :: replace_nth k' v rest
  | _, [] => []
  end.

Lemma length_replace_nth k v xs : length (replace_nth k v xs) = length xs.
Proof. revert k. induction xs; intros [|k]; simpl; auto. Qed.

Lemma nth_error_replace_same k v xs :
  (k < length xs)%nat -> nth_error (replace_nth k v xs) k = Some v.
Proof.
  revert k. induction xs; intros [|k] H; simpl in *; try lia; auto.
  apply IHxs. lia.
Qed.

Lemma nth_error_replace_other k j v xs :
  k <> j -> nth_error (replace_nth k v xs) j = nth_error xs j.
Proof.
  revert k j. induction xs; intros [|k] [|j] H; simpl; auto; try congruence.
Qed.

Lemma array_store_exists m b xs k v :
  array_at m b xs -> (k < length xs)%nat ->
  exists m', Mem.store Mint32 m b (4 * Z.of_nat k) (Vint (Int.repr v)) = Some m'.
Proof.
  intros A K.
  destruct (nth_error xs k) as [old|] eqn:N.
  - destruct (A k old N) as [_ W].
    destruct (Mem.valid_access_store m Mint32 b (4 * Z.of_nat k)
      (Vint (Int.repr v)) W) as [m' S]. eauto.
  - apply nth_error_None in N. lia.
Qed.

Lemma array_store_same m m' b xs k v :
  array_at m b xs ->
  Mem.store Mint32 m b (4 * Z.of_nat k) (Vint (Int.repr v)) = Some m' ->
  array_at m' b (replace_nth k v xs).
Proof.
  intros A S j x N. destruct (Nat.eq_dec k j) as [E|E].
  - subst j.
    assert (K : (k < length xs)%nat).
    { rewrite <- (length_replace_nth k v xs).
      apply nth_error_Some. rewrite N. discriminate. }
    rewrite nth_error_replace_same in N by exact K. inversion N; subst x.
    split.
    + exact (Mem.load_store_same Mint32 m b (4 * Z.of_nat k)
        (Vint (Int.repr v)) m' S).
    + eapply Mem.store_valid_access_1; [exact S|].
      eapply Mem.store_valid_access_3. exact S.
  - rewrite nth_error_replace_other in N by exact E.
    destruct (A j x N) as [L W]. split.
    + rewrite (Mem.load_store_other Mint32 m b (4 * Z.of_nat k)
        (Vint (Int.repr v)) m' S); [exact L|].
      change (b <> b \/ 4 * Z.of_nat j + 4 <= 4 * Z.of_nat k \/
        4 * Z.of_nat k + 4 <= 4 * Z.of_nat j).
      right. destruct (Nat.lt_trichotomy k j) as [H|[H|H]]; try contradiction.
      * right. lia.
      * left. lia.
    + eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma array_store_disjoint m m' b b' offset value xs :
  array_at m b' xs -> b' <> b ->
  Mem.store Mint32 m b offset value = Some m' -> array_at m' b' xs.
Proof.
  intros A B S k v N. destruct (A k v N) as [L W]. split.
  - rewrite (Mem.load_store_other Mint32 m b offset value m' S); [exact L|]. now left.
  - eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma pointer_index ge m b k :
  0 <= k <= 2048 ->
  sem_binary_operation ge Oadd (Vptr b Ptrofs.zero) ptr
    (Vint (Int.repr k)) u32 m = Some (Vptr b (Ptrofs.repr (4 * k))).
Proof.
  intro K.
  change (Some (Vptr b (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_intu (Int.repr k))))) =
    Some (Vptr b (Ptrofs.repr (4 * k)))).
  rewrite Ptrofs.add_zero_l.
  unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by (change (0 <= k <= 4294967295); lia).
  unfold Ptrofs.mul.
  rewrite Ptrofs.unsigned_repr by (change (0 <= 4 <= 18446744073709551615); lia).
  rewrite Ptrofs.unsigned_repr by (change (0 <= k <= 18446744073709551615); lia).
  reflexivity.
Qed.

Lemma cell_address ge le m a index b k :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  typeof index = u32 -> expression ge le m index = Some (Vint (Int.repr k)) ->
  0 <= k <= 2048 ->
  expression ge le m (Ebinop Oadd (Etempvar a ptr) index ptr) =
    Some (Vptr b (Ptrofs.repr (4 * k))).
Proof.
  intros A T I K. cbn [expression]. rewrite A, I, T.
  exact (pointer_index ge m b k K).
Qed.

Lemma cell_expression ge le m a index b k value :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  typeof index = u32 -> expression ge le m index = Some (Vint (Int.repr k)) ->
  0 <= k <= 2048 ->
  Mem.load Mint32 m b (4 * k) = Some value ->
  expression ge le m (cell a index) = Some value.
Proof.
  intros A T I K L. unfold cell. cbn [expression]. rewrite A, I, T.
  cbn [typeof]. rewrite (pointer_index ge m b k K).
  cbn [u32 access_mode Mem.loadv].
  rewrite Ptrofs.unsigned_repr by
    (change (0 <= 4 * k <= 18446744073709551615); lia).
  exact L.
Qed.

Lemma cell_store ge le m a index rhs b k value m' :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  typeof index = u32 -> expression ge le m index = Some (Vint (Int.repr k)) ->
  0 <= k <= 2048 ->
  typeof rhs = u32 -> expression ge le m rhs = Some (Vint (Int.repr value)) ->
  Mem.store Mint32 m b (4 * k) (Vint (Int.repr value)) = Some m' ->
  store ge le m (cell a index) rhs = Some m'.
Proof.
  intros A T I K R V S. unfold store, cell. cbn [expression]. rewrite A, I, T.
  cbn [typeof]. rewrite (pointer_index ge m b k K). rewrite V, R.
  cbn [u32 access_mode sem_cast classify_cast cast_int_int Mem.storev].
  rewrite Ptrofs.unsigned_repr by
    (change (0 <= 4 * k <= 18446744073709551615); lia).
  exact S.
Qed.
