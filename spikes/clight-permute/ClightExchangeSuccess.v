(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightSwap
  ClightScalar ClightEntry.
Import ListNotations.
Open Scope Z_scope.

Lemma array_append_store m m' b xs v :
  array_at m b xs ->
  Mem.store Mint32 m b (4 * Z.of_nat (length xs)) (Vint (Int.repr v)) = Some m' ->
  array_at m' b (xs ++ [v]).
Proof.
  intros A S k x N.
  destruct (Nat.lt_ge_cases k (length xs)) as [Before|After].
  - rewrite nth_error_app1 in N by exact Before.
    destruct (A k x N) as [L W]. split.
    + rewrite (Mem.load_store_other Mint32 m b (4 * Z.of_nat (length xs))
        (Vint (Int.repr v)) m' S); [exact L|].
      right; left. change (4 * Z.of_nat k + 4 <= 4 * Z.of_nat (length xs)). lia.
    + eapply Mem.store_valid_access_1; eauto.
  - rewrite nth_error_app2 in N by exact After.
    assert (E : k = length xs).
    { destruct (k - length xs)%nat eqn:D; [lia|]. destruct n; discriminate. }
    subst k. rewrite Nat.sub_diag in N. inversion N; subst x. split.
    + exact (Mem.load_store_same Mint32 m b _ _ m' S).
    + eapply Mem.store_valid_access_1; [exact S|].
      eapply Mem.store_valid_access_3. exact S.
Qed.

(* The trace can be uninitialized after its written prefix. The capacity
   assumption gives permissions for the next element without a load. *)
Theorem successful_exchange ge e le m bd bp bt bo xs destinations depths p t x y pp pt :
  bd <> bp -> bd <> bt -> bd <> bo -> bp <> bt -> bp <> bo -> bt <> bo ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get trace le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get out le = Some (Vptr bo Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat (length xs)))) ->
  PTree.get pos le = Some (Vint (Int.repr (Z.of_nat p))) ->
  PTree.get top le = Some (Vint (Int.repr (Z.of_nat t))) ->
  (length xs <= 1024)%nat -> (length destinations <= 1024)%nat ->
  nth_error xs p = Some x -> nth_error xs t = Some y ->
  nth_error destinations p = Some pp -> nth_error destinations t = Some pt ->
  uint x -> uint y -> x <> y -> (p < t <= p + 16)%nat ->
  (length depths < 2 * length xs)%nat ->
  array_at m bd xs -> array_at m bp destinations ->
  array_at m bo [Z.of_nat (length depths); 0; 0] ->
  array_at m bt depths -> writable_array m bt (2 * length xs) ->
  exists le' m',
    exec_stmt function_entry2 ge e le m exchange E0 le' m' Out_normal /\
    array_at m' bd (replace_nth t x (replace_nth p y xs)) /\
    array_at m' bp (replace_nth t pp (replace_nth p pt destinations)) /\
    array_at m' bo [Z.of_nat (length depths) + 1; 0; 0] /\
    array_at m' bt (depths ++ [Z.of_nat t - Z.of_nat p]) /\
    writable_array m' bt (2 * length xs) /\
    (forall id, id <> tmp -> id <> depth -> PTree.get id le' = PTree.get id le) /\
    (forall other ys, other <> bd -> other <> bp -> other <> bt -> other <> bo ->
      array_at m other ys -> array_at m' other ys).
Proof.
  intros DP DT DO PT PO TO Data Perm Trace Out Size Position Top XS PS XP XT PP TP
    X Y Different Near Capacity AD AP AO AT WT.
  assert (PB : (p < length xs)%nat) by (apply nth_error_Some; rewrite XP; discriminate).
  assert (TB : (t < length xs)%nat) by (apply nth_error_Some; rewrite XT; discriminate).
  assert (PK : 0 <= Z.of_nat p <= 2048) by lia.
  assert (TK : 0 <= Z.of_nat t <= 2048) by lia.
  assert (CK : 0 <= Z.of_nat (length depths) <= 2048) by lia.
  assert (UP : uint (Z.of_nat p)) by (change (0 <= Z.of_nat p <= 4294967295); lia).
  assert (UT : uint (Z.of_nat t)) by (change (0 <= Z.of_nat t <= 4294967295); lia).
  assert (UN : uint (Z.of_nat (length xs)))
    by (change (0 <= Z.of_nat (length xs) <= 4294967295); lia).
  assert (UC : uint (Z.of_nat (length depths)))
    by (change (0 <= Z.of_nat (length depths) <= 4294967295); lia).
  assert (UD : uint (Z.of_nat t - Z.of_nat p))
    by (change (0 <= Z.of_nat t - Z.of_nat p <= 4294967295); lia).
  assert (U16 : uint 16) by (change (0 <= 16 <= 4294967295); lia).
  assert (U1 : uint 1) by (change (0 <= 1 <= 4294967295); lia).
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
  assert (Binding1 : forall a, a <> depth -> PTree.get a le1 = PTree.get a le).
  { intros a A. unfold le1. now rewrite PTree.gso. }
  assert (Depth1 : forall memory, expression ge le1 memory (reg depth) =
    Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))).
  { intro memory. change (PTree.get depth le1 =
      Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))).
    unfold le1. apply PTree.gss. }
  assert (Reachable : expression ge le1 m (gt (reg depth) (lit 16)) = Some Vfalse).
  { pose proof (expression_compare ge le1 m Cgt (reg depth) (lit 16) _ 16 eq_refl eq_refl
      UD U16 (Depth1 m) eq_refl) as C.
    unfold zcompare in C. destruct (Coqlib.zlt 16 (Z.of_nat t - Z.of_nat p)); [lia|exact C]. }
  assert (Count1 : expression ge le1 m (cell out (lit 0)) =
    Some (Vint (Int.repr (Z.of_nat (length depths))))).
  { eapply cell_expression with (b := bo) (k := 0); try reflexivity; try lia.
    - rewrite Binding1 by discriminate. exact Out.
    - exact (proj1 (AO 0%nat _ eq_refl)). }
  assert (TwiceN : expression ge le1 m (add (reg n) (reg n)) =
    Some (Vint (Int.repr (Z.of_nat (length xs) + Z.of_nat (length xs))))).
  { eapply expression_add; eauto; try reflexivity;
      change (PTree.get n le1 = Some (Vint (Int.repr (Z.of_nat (length xs)))));
      rewrite Binding1 by discriminate; exact Size. }
  assert (U2N : uint (Z.of_nat (length xs) + Z.of_nat (length xs)))
    by (change (0 <= Z.of_nat (length xs) + Z.of_nat (length xs) <= 4294967295); lia).
  assert (HasSpace : expression ge le1 m
    (Permute.ge (cell out (lit 0)) (add (reg n) (reg n))) = Some Vfalse).
  { pose proof (expression_compare ge le1 m Cge (cell out (lit 0))
      (add (reg n) (reg n)) _ _ eq_refl eq_refl UC U2N Count1 TwiceN) as C.
    unfold zcompare in C.
    destruct (Coqlib.zlt (Z.of_nat (length depths))
      (Z.of_nat (length xs) + Z.of_nat (length xs))); [exact C|lia]. }
  destruct (swap_cells_array_full ge e le1 m data bd xs p t x y ltac:(discriminate)
    ltac:(rewrite Binding1 by discriminate; exact Data)
    ltac:(rewrite Binding1 by discriminate; exact Position)
    ltac:(rewrite Binding1 by discriminate; exact Top) XS XP XT AD)
    as [m1 [SwapData [AD1 [Frame1 Writable1]]]].
  set (le2 := PTree.set tmp (Vint (Int.repr x)) le1).
  assert (Binding2 : forall a, a <> tmp -> PTree.get a le2 = PTree.get a le1).
  { intros a A. unfold le2. now rewrite PTree.gso. }
  assert (AO1 : array_at m1 bo [Z.of_nat (length depths); 0; 0])
    by (apply Frame1; [congruence|exact AO]).
  assert (AT1 : array_at m1 bt depths) by (apply Frame1; [congruence|exact AT]).
  assert (AP1 : array_at m1 bp destinations) by (apply Frame1; [congruence|exact AP]).
  assert (WT1 : writable_array m1 bt (2 * length xs)).
  { apply Writable1. exact WT. }
  destruct (Mem.valid_access_store m1 Mint32 bt (4 * Z.of_nat (length depths))
    (Vint (Int.repr (Z.of_nat t - Z.of_nat p))) (WT1 _ Capacity)) as [m2 WTrace].
  pose proof (array_append_store m1 m2 bt depths _ AT1 WTrace) as AT2.
  assert (AO2 : array_at m2 bo [Z.of_nat (length depths); 0; 0])
    by (eapply array_store_disjoint with (b := bt); [exact AO1|congruence|exact WTrace]).
  destruct (array_store_exists m2 bo _ 0 (Z.of_nat (length depths) + 1) AO2
    ltac:(simpl; lia)) as [m3 WCount].
  pose proof (array_store_same m2 m3 bo _ 0 _ AO2 WCount) as AO3.
  assert (Count2 : expression ge le2 m1 (cell out (lit 0)) =
    Some (Vint (Int.repr (Z.of_nat (length depths))))).
  { eapply cell_expression with (b := bo) (k := 0); try reflexivity; try lia.
    - rewrite Binding2, Binding1 by discriminate. exact Out.
    - exact (proj1 (AO1 0%nat _ eq_refl)). }
  assert (STrace : store ge le2 m1 (cell trace (cell out (lit 0))) (reg depth) = Some m2).
  { eapply cell_store with (b := bt) (k := Z.of_nat (length depths)); eauto; try reflexivity.
    - rewrite Binding2, Binding1 by discriminate. exact Trace.
    - change (PTree.get depth le2 = Some (Vint (Int.repr (Z.of_nat t - Z.of_nat p)))).
      rewrite Binding2 by discriminate. apply PTree.gss. }
  assert (SCount : store ge le2 m2 (cell out (lit 0))
    (add (cell out (lit 0)) (lit 1)) = Some m3).
  { eapply cell_store with (b := bo) (k := 0) (value := Z.of_nat (length depths) + 1);
      eauto; try reflexivity; try lia.
    - rewrite Binding2, Binding1 by discriminate. exact Out.
    - eapply expression_add; eauto; try reflexivity.
      eapply cell_expression with (b := bo) (k := 0); try reflexivity; try lia.
      + rewrite Binding2, Binding1 by discriminate. exact Out.
      + exact (proj1 (AO2 0%nat _ eq_refl)). }
  assert (AP3 : array_at m3 bp destinations).
  { eapply array_store_disjoint; [|exact PO|exact WCount].
    eapply array_store_disjoint; [exact AP1|exact PT|exact WTrace]. }
  destruct (swap_cells_array_full ge e le2 m3 permutation bp destinations p t pp pt
    ltac:(discriminate)
    ltac:(rewrite Binding2, Binding1 by discriminate; exact Perm)
    ltac:(rewrite Binding2, Binding1 by discriminate; exact Position)
    ltac:(rewrite Binding2, Binding1 by discriminate; exact Top) PS PP TP AP3)
    as [m4 [SwapPerm [AP4 [Frame4 Writable4]]]].
  exists (PTree.set tmp (Vint (Int.repr pp)) le2), m4.
  split.
  - unfold exchange, seq. cbn [fold_right].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
    + unfold when at 1. eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      * eapply expression_sound. exact DifferentC.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        -- apply exec_Sset. eapply expression_sound. exact Distance.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
           ++ unfold when at 1. eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
              ** eapply expression_sound. exact Reachable.
              ** reflexivity.
              ** constructor.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
              ** unfold when at 1. eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
                 --- eapply expression_sound. exact HasSpace.
                 --- reflexivity.
                 --- constructor.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
                 --- exact SwapData.
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
                     +++ now apply exec_store.
                     +++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
                         *** now apply exec_store.
                         *** constructor.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact SwapPerm|constructor].
  - split.
    + apply Frame4; [exact DP|].
      eapply array_store_disjoint; [|exact DO|exact WCount].
      eapply array_store_disjoint; [exact AD1|exact DT|exact WTrace].
    + split; [exact AP4|]. split.
      * apply Frame4; [congruence|exact AO3].
      * split.
        -- apply Frame4; [congruence|].
           eapply array_store_disjoint; [exact AT2|exact TO|exact WCount].
        -- split.
           ++ apply Writable4.
              eapply writable_array_store; [|exact WCount].
              eapply writable_array_store; [exact WT1|exact WTrace].
           ++ split.
              ** intros id T D. unfold le2, le1. rewrite !PTree.gso by assumption.
                 reflexivity.
              ** intros other ys BData BPerm BTrace BOut Other.
                 apply Frame4; [exact BPerm|].
                 eapply array_store_disjoint; [|exact BOut|exact WCount].
                 eapply array_store_disjoint; [|exact BTrace|exact WTrace].
                 apply Frame1; assumption.
Qed.

Print Assumptions successful_exchange.
