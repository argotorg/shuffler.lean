(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index
  FixedBlocks Choose ExchangeBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma exchange_blocked_fields layout output from varargs c s k depth count old_pos old_excess :
  (3 <= block_words layout output)%nat ->
  cells_related layout c (fst s) ->
  array_at c output [count; old_pos; old_excess] ->
  output_registers layout output s ->
  Maps.lookup (Name "v11.2") (locals s) = Some (word_value (Int.repr k)) ->
  Maps.lookup (Name "sub140") (locals s) = Some (word_value (Int.repr depth)) ->
  exists c' s', cells_related layout c' (fst s') /\
    array_at c' output [count; k; depth - 16] /\
    runs (denote_block (proj1_sig exchange_blocked) from varargs) s s' (inl (Name "cleanup")) /\
    (forall other values, other <> output -> array_at c other values -> array_at c' other values) /\
    (forall id, ~ In id exchange_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Capacity Related Output [Field1 Field2] Position Depth.
  destruct (@related_store layout c (fst s) output 1 (Int.repr k) Related ltac:(lia))
    as [c1 [m1 [Store1 [Write1 [Related1 _]]]]].
  destruct (@related_store layout c1 m1 output 2 (Int.repr (depth - 16)) Related1 ltac:(lia))
    as [c2 [m2 [Store2 [Write2 [Related2 _]]]]].
  pose (s2 := exchange_blocked_state s depth m1 m2).
  exists c2, s2. split; [exact Related2|]. split.
  - change (array_at c2 output (replace_nth 2 (depth - 16)
      (replace_nth 1 k [count; old_pos; old_excess]))).
    eapply array_store_same; [|exact Store2].
    eapply array_store_same; eassumption.
  - split.
    + apply exchange_blocked_runs with (oa := block_address layout output)
        (op := block_provenance layout output) (k := k); try assumption.
    + split.
      * intros other values Separate Array.
        eapply array_store_disjoint; [|exact Separate|exact Store2].
        eapply array_store_disjoint; eassumption.
      * apply exchange_blocked_other.
Qed.

(* The comparison and depth test are the actual LLVM blocks. The two stores
   follow from the related writable cells; store success is not a premise. *)
Theorem exchange_blocked_choice layout bd output xs k d count old_pos old_excess x y
    from varargs c s :
  (List.length xs <= 1024)%nat ->
  (List.length xs <= block_words layout bd)%nat ->
  (3 <= block_words layout output)%nat ->
  nth_error xs k = Some x -> nth_error xs d = Some y ->
  uint x -> uint y -> x <> y -> (k + 16 < d)%nat ->
  cells_related layout c (fst s) ->
  array_at c bd xs -> array_at c output [count; old_pos; old_excess] ->
  choose_binding from s (Some k) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "arrayidx137") (locals s) = Some
    (pointer_value (block_address layout bd + 4 * Z.of_nat d) (block_provenance layout bd)) ->
  Maps.lookup (Name "sub") (locals s) = Some (word_value (Int.repr (Z.of_nat d))) ->
  output_registers layout output s ->
  exists c' s', cells_related layout c' (fst s') /\
    array_at c' output [count; Z.of_nat k; Z.of_nat d - Z.of_nat k - 16] /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.then142") (Name "cleanup") s' /\
    (forall other values, other <> output -> array_at c other values -> array_at c' other values) /\
    (forall id, ~ In id exchange_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Size DataCapacity OutCapacity AtSelected AtTop X Y Different Far Related
    DataArray OutputArray Binding Data TopData Top Fields.
  assert (K : (k < List.length xs)%nat).
  { apply nth_error_Some. rewrite AtSelected. discriminate. }
  assert (D : (d < List.length xs)%nat).
  { apply nth_error_Some. rewrite AtTop. discriminate. }
  pose (s1 := exchange_compare_state s (Z.of_nat k)
    (block_address layout bd) (block_provenance layout bd) (Int.repr x) (Int.repr y)).
  assert (Equal : word_equal (Int.repr x) (Int.repr y) = false).
  { unfold word_equal. rewrite !Int.unsigned_repr by assumption. apply Z.eqb_neq, Different. }
  assert (Compare : runs (denote_block (proj1_sig exchange_compare) from varargs) s s1
      (inl (if word_equal (Int.repr x) (Int.repr y) then Name "if.end169" else Name "if.then139"))).
  { apply exchange_compare_runs with (top_address := block_address layout bd + 4 * Z.of_nat d);
      try assumption; try lia.
    - eapply related_load; [exact Related|lia|exact (proj1 (DataArray _ _ AtSelected))].
    - eapply related_load; [exact Related|lia|exact (proj1 (DataArray _ _ AtTop))]. }
  rewrite Equal in Compare.
  assert (Memory1 : fst s1 = fst s) by apply exchange_compare_memory.
  assert (Position1 : Maps.lookup (Name "v11.2") (locals s1) =
      Some (word_value (Int.repr (Z.of_nat k)))).
  { exact (proj1 (exchange_compare_bindings s (Z.of_nat k)
      (block_address layout bd) (block_provenance layout bd) (Int.repr x) (Int.repr y))). }
  assert (Other1 : forall id, ~ In id exchange_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { apply exchange_compare_other. }
  pose (s2 := exchange_depth_state s1 (Z.of_nat d) (Z.of_nat k)).
  assert (FarTest : (16 <? Z.of_nat d - Z.of_nat k) = true) by (apply Z.ltb_lt; lia).
  assert (Depth : runs (denote_block (proj1_sig exchange_depth) (Name "if.end133") varargs)
      s1 s2 (inl (if 16 <? Z.of_nat d - Z.of_nat k then Name "if.then142" else Name "if.end147"))).
  { apply exchange_depth_runs; try lia; [|exact Position1].
    rewrite Other1 by (unfold exchange_modified; simpl; intuition discriminate). exact Top. }
  rewrite FarTest in Depth.
  assert (Memory2 : fst s2 = fst s) by (unfold s2; rewrite exchange_depth_memory, Memory1; reflexivity).
  assert (Related2 : cells_related layout c (fst s2)) by (rewrite Memory2; exact Related).
  assert (Position2 : Maps.lookup (Name "v11.2") (locals s2) =
      Some (word_value (Int.repr (Z.of_nat k)))).
  { unfold s2, exchange_depth_state. rewrite !lookup_local_other by discriminate. exact Position1. }
  assert (Other2 : forall id, ~ In id exchange_modified ->
      Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
  { intros id Outside. unfold s2. rewrite exchange_depth_other by exact Outside. apply Other1, Outside. }
  assert (Fields2 : output_registers layout output s2).
  { destruct Fields. constructor; rewrite Other2 by
      (unfold exchange_modified; simpl; intuition discriminate); assumption. }
  destruct (@exchange_blocked_fields layout output (Name "if.then139") varargs c s2
    (Z.of_nat k) (Z.of_nat d - Z.of_nat k) count old_pos old_excess OutCapacity
    Related2 OutputArray Fields2 Position2 (exchange_depth_binding _ _ _))
    as [c3 [s3 [Related3 [Output3 [Blocked [Frame Other3]]]]]].
  exists c3, s3. split; [exact Related3|]. split; [exact Output3|]. split.
  - eapply steps_next; [exact (proj2_sig exchange_compare)|exact Compare|].
    eapply steps_next; [exact (proj2_sig exchange_depth)|exact Depth|].
    eapply steps_next; [exact (proj2_sig exchange_blocked)|exact Blocked|constructor].
  - split; [exact Frame|]. intros id Outside. rewrite Other3 by exact Outside. apply Other2, Outside.
Qed.
