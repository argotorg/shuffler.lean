(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightValidation.
From Vellvm Require Import Utils Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index ValidationBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Loop.
Context (layout : allocation_layout) (size : nat) (xs destinations : list Z)
    (destination : nat -> nat) (bd bp bt bu : Values.block).
Hypothesis Size : (size <= 1024)%nat.
Hypothesis Length : List.length xs = size.
Hypothesis Destinations : forall k, (k < size)%nat ->
  nth_error destinations k = Some (Z.of_nat (destination k)).
Hypothesis Bounded : forall k, (k < size)%nat -> (destination k < size)%nat.
Hypothesis Injective : forall k q, (k < size)%nat -> (q < size)%nat ->
  destination k = destination q -> k = q.
Hypotheses (DU : bd <> bu) (DT : bd <> bt) (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu).
Hypotheses (CD : (size <= block_words layout bd)%nat)
    (CP : (size <= block_words layout bp)%nat)
    (CT : (size <= block_words layout bt)%nat)
    (CU : (size <= block_words layout bu)%nat).

Let invariant := ClightValidation.validation_memory size xs destinations destination bd bp bt bu.

Record validation_locals (s : FusedS) : Prop := {
  local_size : Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size)));
  local_count : Maps.lookup (Name "wide.trip.count299") (locals s) = Some (index_value (Z.of_nat size));
  local_data : Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd));
  local_permutation : Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp));
  local_target : Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt));
  local_used : Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu))
}.

Theorem validation_iteration from varargs c s k : (k < size)%nat ->
  cells_related layout c (fst s) -> invariant k c -> validation_locals s ->
  validation_input from s (Z.of_nat k) ->
  exists c' s', cells_related layout c' (fst s') /\ invariant (S k) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17") s
      (Name "if.end29")
      (if Z.of_nat k + 1 =? Z.of_nat size then Name "if.end43.preheader" else Name "if.end17") s' /\
    validation_locals s' /\ validation_input (Name "if.end29") s' (Z.of_nat (S k)) /\
    (forall id, ~ In id validation_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intros K Relation Inv Registers Input.
  destruct Registers as [N Count Data Perm Target Used].
  destruct Inv as [AD AP WT WU T U].
  assert (DK : (destination k < size)%nat) by (apply Bounded, K).
  assert (Fresh : forall r, (r < k)%nat -> destination r <> destination k).
  { intros r R Same. assert (r = k) by (apply Injective; auto; lia). lia. }
  destruct (nth_error xs k) as [value|] eqn:Source.
  2: { apply nth_error_None in Source. lia. }
  assert (ReadPerm : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bp k, block_provenance layout bp)) (fst s) =
      Ret (fst s, word_value (Int.repr (Z.of_nat (destination k))))).
  { eapply related_load; [exact Relation|lia|].
    exact (proj1 (AP k _ (@Destinations k K))). }
  pose (s1 := range_state s (Z.of_nat k) (Z.of_nat (destination k))
    (block_address layout bp) (block_provenance layout bp)).
  assert (Range : runs (denote_block (proj1_sig FullCFG.validation_range) from varargs)
      s s1 (inl (Name "if.end23"))).
  { apply validation_range_runs with (n := Z.of_nat size); try assumption; lia. }
  assert (Memory1 : fst s1 = fst s).
  { unfold s1, range_state. rewrite !memory_set_local. reflexivity. }
  assert (ReadUsed : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bu (destination k), block_provenance layout bu)) (fst s1) =
      Ret (fst s1, word_value Int.zero)).
  { rewrite Memory1. eapply related_load; [exact Relation|lia|apply U; assumption]. }
  pose (s2 := unused_state s1 (Z.of_nat (destination k))
    (block_address layout bu) (block_provenance layout bu)).
  assert (Unused : runs (denote_block (proj1_sig FullCFG.validation_unused)
      (Name "if.end17") varargs) s1 s2 (inl (Name "if.end29"))).
  { apply validation_unused_runs; [lia| | |exact ReadUsed].
    - unfold s1, range_state. rewrite lookup_local_other by discriminate.
      apply lookup_local_same.
    - unfold s1, range_state. rewrite !lookup_local_other by discriminate. exact Used. }
  assert (Memory2 : fst s2 = fst s).
  { unfold s2, unused_state. rewrite !memory_set_local. exact Memory1. }
  destruct (@related_store layout c (fst s) bu (destination k) Int.one Relation ltac:(lia))
    as [c1 [m1 [StoreUsed [WriteUsed [Related1 _]]]]].
  destruct (@related_store layout c1 m1 bt (destination k) (Int.repr value) Related1 ltac:(lia))
    as [c2 [m2 [StoreTarget [WriteTarget [Related2 _]]]]].
  assert (ReadData : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bd k, block_provenance layout bd)) m1 =
      Ret (m1, word_value (Int.repr value))).
  { eapply related_load; [exact Related1|lia|].
    rewrite (Mem.load_store_other Mint32 c bu _ _ c1 StoreUsed) by (left; exact DU).
    exact (proj1 (AD k value Source)). }
  pose (s3 := iteration_state layout bd bp bt bu s (Z.of_nat k) (Z.of_nat size)
    (Z.of_nat (destination k)) m1 m2 (Int.repr value)).
  assert (Store : runs (denote_block (proj1_sig FullCFG.validation_store)
      (Name "if.end23") varargs) s2 s3
      (inl (if Z.of_nat k + 1 =? Z.of_nat size then Name "if.end43.preheader" else Name "if.end17"))).
  { apply validation_store_runs with
      (used_address := cell_address layout bu (destination k))
      (used_prov := block_provenance layout bu); try lia.
    - unfold s2, s1, unused_state, range_state.
      rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, s1, unused_state, range_state.
      rewrite !lookup_local_other by discriminate. exact Count.
    - unfold s2, unused_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, unused_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, s1, unused_state, range_state. rewrite !lookup_local_other by discriminate. exact Data.
    - unfold s2, s1, unused_state, range_state. rewrite !lookup_local_other by discriminate. exact Target.
    - unfold s2, s1, unused_state, range_state.
      rewrite !memory_set_local. exact WriteUsed.
    - exact ReadData.
    - exact WriteTarget. }
  assert (Other : forall id, ~ In id validation_modified ->
      Maps.lookup id (locals s3) = Maps.lookup id (locals s)).
  { intros id Different. apply iteration_other, Different. }
  exists c2, s3. split.
  - unfold s3. rewrite iteration_memory. exact Related2.
  - split.
    + eapply ClightValidation.validation_memory_step; try eassumption.
      constructor; assumption.
    + split.
      * eapply steps_next; [exact (proj2_sig FullCFG.validation_range)|exact Range|].
        eapply steps_next; [exact (proj2_sig FullCFG.validation_unused)|exact Unused|].
        eapply steps_next; [exact (proj2_sig FullCFG.validation_store)|exact Store|constructor].
      * split.
        -- constructor; rewrite Other by (unfold validation_modified; simpl; intuition discriminate); assumption.
        -- split.
           ++ rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
              apply iteration_next.
           ++ split; [exact Other|].
              intros other values NotUsed NotTarget A.
              eapply array_store_disjoint; [|exact NotTarget|exact StoreTarget].
              eapply array_store_disjoint; [exact A|exact NotUsed|exact StoreUsed].
Qed.

Theorem validation_loop varargs : forall remaining start from c s,
  (0 < remaining)%nat -> (start + remaining = size)%nat ->
  cells_related layout c (fst s) -> invariant start c -> validation_locals s ->
  validation_input from s (Z.of_nat start) ->
  exists c' s', cells_related layout c' (fst s') /\ invariant size c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17") s
      (Name "if.end29") (Name "if.end43.preheader") s' /\
    (forall id, ~ In id validation_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from c s Positive Sum Relation Inv Registers Input; [lia|].
  destruct (@validation_iteration from varargs c s start ltac:(lia) Relation Inv Registers Input)
    as [c1 [s1 [Related1 [Inv1 [Step [Locals1 [Next [Other Frame]]]]]]]].
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat start + 1 =? Z.of_nat size) = true)
      by (apply Z.eqb_eq; lia).
    rewrite Last in Step. exists c1, s1. split; [exact Related1|].
    split; [replace size with (S start) by lia; exact Inv1|].
    split; [exact Step|]. split; assumption.
  - assert (More : (Z.of_nat start + 1 =? Z.of_nat size) = false)
      by (apply Z.eqb_neq; lia).
    rewrite More in Step.
    destruct (IH (S start) (Name "if.end29") c1 s1 ltac:(lia) ltac:(lia)
      Related1 Inv1 Locals1 Next) as [c' [s' [Related [Final [Steps [Locals Frame']]]]]].
    exists c', s'. split; [exact Related|]. split; [exact Final|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * intros id Outside. rewrite Locals by exact Outside. apply Other, Outside.
      * intros other values NotUsed NotTarget A. apply Frame'; try assumption.
        apply Frame; assumption.
Qed.

Lemma validation_preheader_runs from varargs (s : FusedS) :
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
  runs (denote_block (proj1_sig FullCFG.validation_preheader) from varargs) s
    (set_local s (Name "wide.trip.count299") (index_value (Z.of_nat size)))
    (inl (Name "if.end17")).
Proof.
  intro N. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (Z.of_nat size)).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by lia. reflexivity.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Theorem validation_pass from varargs c s : (0 < size)%nat ->
  cells_related layout c (fst s) -> invariant 0 c ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  exists c' s', cells_related layout c' (fst s') /\ invariant size c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17.preheader") s
      (Name "if.end29") (Name "if.end43.preheader") s' /\
    (forall id, id <> Name "wide.trip.count299" -> ~ In id validation_modified ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Positive Relation Inv N Data Perm Target Used.
  pose (s1 := set_local s (Name "wide.trip.count299") (index_value (Z.of_nat size))).
  assert (Related1 : cells_related layout c (fst s1)).
  { unfold s1. rewrite memory_set_local. exact Relation. }
  assert (Registers : validation_locals s1).
  { constructor; unfold s1;
      first [apply lookup_local_same | rewrite lookup_local_other by discriminate; assumption]. }
  destruct (@validation_loop varargs size 0 (Name "if.end17.preheader") c s1
    Positive eq_refl Related1 Inv Registers (or_introl (conj eq_refl eq_refl)))
    as [c' [s' [Related [Final [Steps [Locals Frame]]]]]].
  exists c', s'. split; [exact Related|]. split; [exact Final|]. split.
  - eapply steps_next; [exact (proj2_sig FullCFG.validation_preheader)| |exact Steps].
    apply validation_preheader_runs, N.
  - split; [|exact Frame]. intros id Different Outside.
    rewrite Locals by exact Outside. unfold s1.
    rewrite lookup_local_other by exact Different. reflexivity.
Qed.
End Loop.
