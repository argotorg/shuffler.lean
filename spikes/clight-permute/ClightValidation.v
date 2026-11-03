(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar
  ClightLoop ClightInitialize ClightEntry.
Import ListNotations.
Open Scope Z_scope.

(* A proof abbreviation for the exact second loop body in check_input. *)
Definition validation_body := seq [
  set j (cell permutation (reg i));
  when (Permute.ge (reg j) (reg n)) (ret 2);
  when (ne (cell used (reg j)) (lit 0)) (ret 2);
  put used (reg j) (lit 1);
  put target (reg j) (cell data (reg i))
].

Lemma different_cells (a b : nat) : a <> b ->
  4 * Z.of_nat a + 4 <= 4 * Z.of_nat b \/
  4 * Z.of_nat b + 4 <= 4 * Z.of_nat a.
Proof. intros D. destruct (Nat.lt_trichotomy a b) as [L|[E|L]]; auto; lia. Qed.

Section Validation.
Variables (size : nat) (xs destinations : list Z) (destination : nat -> nat).
Variables (bd bp bt bu : block).
Hypothesis Size : (size <= 1024)%nat.
Hypothesis Length : length xs = size.
Hypothesis Destinations : forall k, (k < size)%nat ->
  nth_error destinations k = Some (Z.of_nat (destination k)).
Hypothesis Bounded : forall k, (k < size)%nat -> (destination k < size)%nat.
Hypothesis Injective : forall k q, (k < size)%nat -> (q < size)%nat ->
  destination k = destination q -> k = q.
Hypotheses DU : bd <> bu.
Hypotheses DT : bd <> bt.
Hypotheses PU : bp <> bu.
Hypotheses PT : bp <> bt.
Hypotheses TU : bt <> bu.

Record validation_memory (count : nat) (m : mem) : Prop := {
  validation_data : array_at m bd xs;
  validation_permutation : array_at m bp destinations;
  validation_target_writable : writable_array m bt size;
  validation_used_writable : writable_array m bu size;
  validation_target : forall q value, (q < count)%nat ->
    nth_error xs q = Some value ->
    Mem.load Mint32 m bt (4 * Z.of_nat (destination q)) = Some (Vint (Int.repr value));
  validation_unused : forall q, (q < size)%nat ->
    (forall r, (r < count)%nat -> destination r <> q) ->
    Mem.load Mint32 m bu (4 * Z.of_nat q) = Some (Vint (Int.repr 0))
}.

Lemma validation_memory_step m m1 m2 k value :
  (k < size)%nat -> nth_error xs k = Some value -> validation_memory k m ->
  Mem.store Mint32 m bu (4 * Z.of_nat (destination k)) (Vint (Int.repr 1)) = Some m1 ->
  Mem.store Mint32 m1 bt (4 * Z.of_nat (destination k)) (Vint (Int.repr value)) = Some m2 ->
  validation_memory (S k) m2.
Proof.
  intros K Source [AD AP WT WU Target Unused] SU ST. constructor.
  - eapply array_store_disjoint; [|exact DT|exact ST].
    eapply array_store_disjoint; [exact AD|exact DU|exact SU].
  - eapply array_store_disjoint; [|exact PT|exact ST].
    eapply array_store_disjoint; [exact AP|exact PU|exact SU].
  - eapply writable_array_store; [|exact ST]. eapply writable_array_store; [exact WT|exact SU].
  - eapply writable_array_store; [|exact ST]. eapply writable_array_store; [exact WU|exact SU].
  - intros q x Q SourceQ. destruct (Nat.eq_dec q k) as [->|Different].
    + rewrite Source in SourceQ. inversion SourceQ; subst x.
      exact (Mem.load_store_same Mint32 m1 bt _ _ m2 ST).
    + rewrite (Mem.load_store_other Mint32 m1 bt _ _ m2 ST).
      * rewrite (Mem.load_store_other Mint32 m bu _ _ m1 SU) by (left; exact TU).
        apply Target; [lia|exact SourceQ].
      * right. change (4 * Z.of_nat (destination q) + 4 <= 4 * Z.of_nat (destination k) \/
          4 * Z.of_nat (destination k) + 4 <= 4 * Z.of_nat (destination q)).
        apply different_cells. intro E. apply Different. apply Injective; auto; lia.
  - intros q Q Fresh.
    rewrite (Mem.load_store_other Mint32 m1 bt _ _ m2 ST) by (left; congruence).
    rewrite (Mem.load_store_other Mint32 m bu _ _ m1 SU).
    + apply Unused; [exact Q|]. intros r R. apply Fresh. lia.
    + right. change (4 * Z.of_nat q + 4 <= 4 * Z.of_nat (destination k) \/
        4 * Z.of_nat (destination k) + 4 <= 4 * Z.of_nat q).
      apply different_cells. intro E. apply (Fresh k); [lia|symmetry; exact E].
Qed.

Lemma validation_iteration ge e le m k :
  (k < size)%nat -> validation_memory k m ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat k))) ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  exists m',
    exec_stmt function_entry2 ge e le m validation_body E0
      (PTree.set j (Vint (Int.repr (Z.of_nat (destination k)))) le) m' Out_normal /\
    validation_memory (S k) m' /\
    (forall other values, other <> bu -> other <> bt ->
      array_at m other values -> array_at m' other values) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros K V N I Data Perm Target Used.
  destruct V as [AD AP WT WU T U].
  assert (DK : (destination k < size)%nat) by (apply Bounded; exact K).
  assert (KB : 0 <= Z.of_nat k <= 2048) by lia.
  assert (DB : 0 <= Z.of_nat (destination k) <= 2048) by lia.
  assert (UN : uint (Z.of_nat size)) by (unfold uint; change Int.max_unsigned with 4294967295; lia).
  assert (UD : uint (Z.of_nat (destination k)))
    by (unfold uint; change Int.max_unsigned with 4294967295; lia).
  assert (U0 : uint 0) by (unfold uint; change Int.max_unsigned with 4294967295; lia).
  assert (P : nth_error destinations k = Some (Z.of_nat (destination k))) by auto.
  assert (RPerm : expression ge le m (cell permutation (reg i)) =
      Some (Vint (Int.repr (Z.of_nat (destination k))))).
  { eapply cell_expression; eauto. exact (proj1 (AP _ _ P)). }
  pose (le1 := PTree.set j (Vint (Int.repr (Z.of_nat (destination k)))) le).
  assert (J1 : PTree.get j le1 = Some (Vint (Int.repr (Z.of_nat (destination k)))))
    by (unfold le1; apply PTree.gss).
  assert (Bindings : forall id, id <> j -> PTree.get id le1 = PTree.get id le).
  { intros id D. unfold le1. rewrite PTree.gso by exact D. reflexivity. }
  assert (N1 : PTree.get n le1 = Some (Vint (Int.repr (Z.of_nat size)))).
  { rewrite Bindings by discriminate. exact N. }
  assert (InRange : expression ge le1 m (Permute.ge (reg j) (reg n)) = Some Vfalse).
  { pose proof (expression_compare ge le1 m Cge (reg j) (reg n)
      _ _ eq_refl eq_refl UD UN J1 N1) as C.
    unfold zcompare in C. destruct (Coqlib.zlt (Z.of_nat (destination k)) (Z.of_nat size));
      [exact C|lia]. }
  assert (Fresh : forall r, (r < k)%nat -> destination r <> destination k).
  { intros r R Same. assert (r = k) by (apply Injective; auto; lia). lia. }
  assert (RUsed : expression ge le1 m (cell used (reg j)) = Some (Vint (Int.repr 0))).
  { eapply cell_expression with (b := bu) (k := Z.of_nat (destination k));
      try reflexivity; try assumption.
    - rewrite Bindings by discriminate. exact Used.
    - apply U; assumption. }
  assert (Unused : expression ge le1 m (ne (cell used (reg j)) (lit 0)) = Some Vfalse).
  { pose proof (expression_compare ge le1 m Cne (cell used (reg j)) (lit 0)
      0 0 eq_refl eq_refl U0 U0 RUsed eq_refl) as C.
    unfold zcompare in C. destruct (Coqlib.zeq 0 0); [exact C|contradiction]. }
  destruct (nth_error xs k) as [value|] eqn:Source.
  2: { apply nth_error_None in Source. lia. }
  destruct (Mem.valid_access_store m Mint32 bu (4 * Z.of_nat (destination k))
    (Vint (Int.repr 1)) (WU _ DK)) as [m1 SU].
  assert (WT1 : writable_array m1 bt size) by (eapply writable_array_store; eauto).
  destruct (Mem.valid_access_store m1 Mint32 bt (4 * Z.of_nat (destination k))
    (Vint (Int.repr value)) (WT1 _ DK)) as [m2 ST].
  assert (SUsed : store ge le1 m (cell used (reg j)) (lit 1) = Some m1).
  { eapply cell_store with (b := bu) (k := Z.of_nat (destination k)) (value := 1);
      try reflexivity; try assumption.
    rewrite Bindings by discriminate. exact Used. }
  assert (AD1 : array_at m1 bd xs).
  { eapply array_store_disjoint; [exact AD|exact DU|exact SU]. }
  assert (RData : expression ge le1 m1 (cell data (reg i)) = Some (Vint (Int.repr value))).
  { eapply cell_expression with (b := bd) (k := Z.of_nat k); try reflexivity; try assumption.
    - rewrite Bindings by discriminate. exact Data.
    - change (PTree.get i le1 = Some (Vint (Int.repr (Z.of_nat k)))).
      rewrite Bindings by discriminate. exact I.
    - exact (proj1 (AD1 _ _ Source)). }
  assert (STarget : store ge le1 m1 (cell target (reg j)) (cell data (reg i)) = Some m2).
  { eapply cell_store with (b := bt) (k := Z.of_nat (destination k)) (value := value);
      try reflexivity; try assumption.
    rewrite Bindings by discriminate. exact Target. }
  exists m2. split.
  - cbn [validation_body seq fold_right].
    eapply exec_Sseq_1 with (le1 := le1) (m1 := m) (t1 := E0) (t2 := E0).
    + apply exec_Sset. apply expression_sound. exact RPerm.
    + eapply exec_Sseq_1 with (le1 := le1) (m1 := m) (t1 := E0) (t2 := E0).
      * eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
        -- apply expression_sound. exact InRange.
        -- exact (bool_comparison m false).
        -- constructor.
      * eapply exec_Sseq_1 with (le1 := le1) (m1 := m) (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
           ++ apply expression_sound. exact Unused.
           ++ exact (bool_comparison m false).
           ++ constructor.
        -- eapply exec_Sseq_1 with (le1 := le1) (m1 := m1) (t1 := E0) (t2 := E0).
           ++ apply exec_store. exact SUsed.
           ++ eapply exec_Sseq_1 with (le1 := le1) (m1 := m2) (t1 := E0) (t2 := E0).
              ** apply exec_store. exact STarget.
              ** constructor.
  - split.
    + eapply validation_memory_step; eauto. constructor; assumption.
    + split.
      * intros other values DifferentU DifferentT A.
        eapply array_store_disjoint; [|exact DifferentT|exact ST].
        eapply array_store_disjoint; [exact A|exact DifferentU|exact SU].
      * intros other count W. eapply writable_array_store; [|exact ST].
        eapply writable_array_store; [exact W|exact SU].
Qed.

Record validation_registers (index : nat) (le : temp_env) : Prop := {
  validation_size_register : PTree.get n le = Some (Vint (Int.repr (Z.of_nat size)));
  validation_index_register : PTree.get i le = Some (Vint (Int.repr (Z.of_nat index)));
  validation_data_register : PTree.get data le = Some (Vptr bd Ptrofs.zero);
  validation_permutation_register : PTree.get permutation le = Some (Vptr bp Ptrofs.zero);
  validation_target_register : PTree.get target le = Some (Vptr bt Ptrofs.zero);
  validation_used_register : PTree.get used le = Some (Vptr bu Ptrofs.zero)
}.

Lemma validation_registers_next k le value :
  validation_registers k le ->
  validation_registers (S k)
    (PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) (PTree.set j value le)).
Proof.
  intros [N I D P T U]. constructor;
    try (rewrite PTree.gss; reflexivity);
    rewrite PTree.gso by discriminate;
    rewrite PTree.gso by discriminate; assumption.
Qed.

Theorem validation_pass ge e le m :
  validation_memory 0 m ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  exists le' m',
    exec_stmt function_entry2 ge e le m (each i validation_body) E0 le' m' Out_normal /\
    validation_memory size m' /\
    (forall id, id <> i -> id <> j -> PTree.get id le' = PTree.get id le) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at m other values -> array_at m' other values) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros V N Data Perm Target Used.
  pose (Inv := fun k le' m' =>
    validation_registers k le' /\ validation_memory k m' /\
    (forall id, id <> i -> id <> j -> PTree.get id le' = PTree.get id le) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at m other values -> array_at m' other values) /\
    (forall other count, writable_array m other count -> writable_array m' other count)).
  assert (Registers : forall k le' m', Inv k le' m' ->
    PTree.get i le' = Some (Vint (Int.repr (Z.of_nat k))) /\
    PTree.get n le' = Some (Vint (Int.repr (Z.of_nat size)))).
  { intros k le' m' [[RN RI RD RP RT RU] Rest]. now split. }
  assert (Step : forall k le0 m0, (k < size)%nat -> Inv k le0 m0 ->
    exists le' m', exec_stmt function_entry2 ge e le0 m0
      (seq [validation_body; inc i]) E0 le' m' Out_normal /\ Inv (S k) le' m').
  { intros k le0 m0 K [R [V0 [Temp0 [Frame0 Writable0]]]].
    destruct R as [RN RI RD RP RT RU].
    destruct (validation_iteration ge e le0 m0 k K V0 RN RI RD RP RT RU)
      as [m1 [Body [V1 [Frame1 Writable1]]]].
    pose (le1 := PTree.set j (Vint (Int.repr (Z.of_nat (destination k)))) le0).
    pose (le2 := PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) le1).
    assert (RI1 : PTree.get i le1 = Some (Vint (Int.repr (Z.of_nat k)))).
    { unfold le1. rewrite PTree.gso by discriminate. exact RI. }
    exists le2, m1. split.
    - cbn [seq fold_right].
      eapply exec_Sseq_1 with (le1 := le1) (m1 := m1) (t1 := E0) (t2 := E0).
      + exact Body.
      + eapply exec_Sseq_1 with (le1 := le2) (m1 := m1) (t1 := E0) (t2 := E0).
        * unfold le2. rewrite Nat2Z.inj_succ.
          replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
          apply increase_index; [exact RI1|lia].
        * constructor.
    - unfold Inv. split.
      + unfold le2, le1. apply validation_registers_next. constructor; assumption.
      + split; [exact V1|]. split.
        * intros id DI DJ. unfold le2, le1.
          rewrite !PTree.gso by assumption. apply Temp0; assumption.
        * split.
          -- intros other values DU' DT' A. apply Frame1; try assumption.
             apply Frame0; assumption.
          -- intros other count W. apply Writable1. apply Writable0. exact W.
  }
  assert (Initial : Inv 0%nat (PTree.set i (Vint (Int.repr 0)) le) m).
  { unfold Inv. split.
    - constructor; try (rewrite PTree.gss; reflexivity);
        rewrite PTree.gso by discriminate; assumption.
    - split; [exact V|]. split.
      + intros id DI DJ. rewrite PTree.gso by exact DI. reflexivity.
      + split; auto.
  }
  destruct (each_invariant ge e i size validation_body Inv Size Registers Step le m Initial)
    as [le' [m' [Execution [R [V' [Temps [Frame Writable]]]]]]].
  exists le', m'. split; [exact Execution|]. split; [exact V'|].
  split; [exact Temps|]. now split.
Qed.

Lemma zero_used_initialized m : array_at m bu (repeat 0 size) ->
  forall q, (q < size)%nat ->
    Mem.load Mint32 m bu (4 * Z.of_nat q) = Some (Vint (Int.repr 0)).
Proof.
  intros A q Q.
  assert (R : forall s q : nat, (q < s)%nat -> nth_error (repeat 0%Z s) q = Some 0%Z).
  { intros s. induction s as [|s IH]; intros [|q'] Q'; simpl; try lia; auto.
    apply IH. lia. }
  pose proof (R size q Q) as N.
  exact (proj1 (A q 0 N)).
Qed.

(* Range and injectivity assumptions express a valid input permutation.
   The target and used arrays need no initial contents. *)
Theorem check_input_valid ge e le m :
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat size))) ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  array_at m bd xs -> array_at m bp destinations ->
  writable_array m bt size -> writable_array m bu size ->
  exists le' m',
    exec_stmt function_entry2 ge e le m check_input E0 le' m' Out_normal /\
    validation_memory size m' /\
    (forall id, id <> i -> id <> j -> PTree.get id le' = PTree.get id le) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at m other values -> array_at m' other values) /\
    (forall other count, writable_array m other count -> writable_array m' other count).
Proof.
  intros N Data Perm Target Used AD AP WT WU.
  destruct (initialize_used_array_full ge e le m bu size Size Used N WU)
    as [le1 [m1 [Init [Zeros [Temps1 [Frame1 Writable1]]]]]].
  assert (InitialMemory : validation_memory 0 m1).
  { constructor.
    - apply Frame1; assumption.
    - apply Frame1; assumption.
    - apply Writable1. exact WT.
    - apply Writable1. exact WU.
    - intros q value Q. lia.
    - intros q Q Fresh. apply zero_used_initialized; assumption.
  }
  assert (N1 : PTree.get n le1 = Some (Vint (Int.repr (Z.of_nat size)))).
  { rewrite Temps1 by discriminate. exact N. }
  assert (D1 : PTree.get data le1 = Some (Vptr bd Ptrofs.zero)).
  { rewrite Temps1 by discriminate. exact Data. }
  assert (P1 : PTree.get permutation le1 = Some (Vptr bp Ptrofs.zero)).
  { rewrite Temps1 by discriminate. exact Perm. }
  assert (T1 : PTree.get target le1 = Some (Vptr bt Ptrofs.zero)).
  { rewrite Temps1 by discriminate. exact Target. }
  assert (U1 : PTree.get used le1 = Some (Vptr bu Ptrofs.zero)).
  { rewrite Temps1 by discriminate. exact Used. }
  destruct (validation_pass ge e le1 m1 InitialMemory N1 D1 P1 T1 U1)
    as [le2 [m2 [Pass [V [Temps2 [Frame2 Writable2]]]]]].
  exists le2, m2. split.
  - change (exec_stmt function_entry2 ge e le m
      (seq [each i (put used (reg i) (lit 0)); each i validation_body]) E0 le2 m2 Out_normal).
    cbn [seq fold_right].
    eapply exec_Sseq_1 with (le1 := le1) (m1 := m1) (t1 := E0) (t2 := E0).
    + exact Init.
    + eapply exec_Sseq_1 with (le1 := le2) (m1 := m2) (t1 := E0) (t2 := E0).
      * exact Pass.
      * constructor.
  - split; [exact V|]. split.
    + intros id DI DJ. rewrite Temps2 by assumption. apply Temps1. exact DI.
    + split.
      * intros other values OU OT A. apply Frame2; try assumption.
        apply Frame1; assumption.
      * intros other count W. apply Writable2. apply Writable1. exact W.
Qed.
End Validation.

Print Assumptions check_input_valid.
