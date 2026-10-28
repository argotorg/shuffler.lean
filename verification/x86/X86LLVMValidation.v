(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index ValidationBlocks Validation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* The two stores are shared with the machine proof. Their addresses and values
   come from the actual load and store order of the validation blocks. *)
Theorem llvm_validation_step layout size bd bp bt bu from varargs
    index destination value c c1 c2 s :
  (index < size <= 1024)%nat -> (destination < size)%nat ->
  (size <= block_words layout bd)%nat ->
  (size <= block_words layout bp)%nat ->
  (size <= block_words layout bt)%nat ->
  (size <= block_words layout bu)%nat ->
  cells_related layout c (fst s) ->
  validation_locals layout size bd bp bt bu s ->
  validation_input from s (Z.of_nat index) ->
  Mem.load Mint32 c bp (4 * Z.of_nat index) = Some (Vint (Int.repr (Z.of_nat destination))) ->
  Mem.load Mint32 c bu (4 * Z.of_nat destination) = Some (Vint Int.zero) ->
  Mem.store Mint32 c bu (4 * Z.of_nat destination) (Vint Int.one) = Some c1 ->
  Mem.load Mint32 c1 bd (4 * Z.of_nat index) = Some (Vint value) ->
  Mem.store Mint32 c1 bt (4 * Z.of_nat destination) (Vint value) = Some c2 ->
  exists s', cells_related layout c2 (fst s') /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17") s
      (Name "if.end29")
      (if Z.of_nat (S index) =? Z.of_nat size
       then Name "if.end43.preheader" else Name "if.end17") s' /\
    validation_locals layout size bd bp bt bu s' /\
    validation_input (Name "if.end29") s' (Z.of_nat (S index)) /\
    (forall id, ~ In id validation_modified ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Range Destination CD CP CT CU Relation Registers Input
    LoadPerm LoadUsed StoreUsed LoadData StoreTarget.
  destruct Registers as [N Count Data Perm Target Used].
  assert (ReadPerm : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bp index, block_provenance layout bp)) (fst s) =
      Ret (fst s, word_value (Int.repr (Z.of_nat destination)))).
  { eapply related_load; [exact Relation|lia|exact LoadPerm]. }
  pose (s1 := range_state s (Z.of_nat index) (Z.of_nat destination)
    (block_address layout bp) (block_provenance layout bp)).
  assert (CheckRange : runs (denote_block (proj1_sig FullCFG.validation_range) from varargs)
      s s1 (inl (Name "if.end23"))).
  { apply validation_range_runs with (n := Z.of_nat size); try assumption; lia. }
  assert (Memory1 : fst s1 = fst s).
  { unfold s1, range_state. rewrite !memory_set_local. reflexivity. }
  assert (ReadUsed : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bu destination, block_provenance layout bu)) (fst s1) =
      Ret (fst s1, word_value Int.zero)).
  { rewrite Memory1. eapply related_load; [exact Relation|lia|exact LoadUsed]. }
  pose (s2 := unused_state s1 (Z.of_nat destination)
    (block_address layout bu) (block_provenance layout bu)).
  assert (Unused : runs (denote_block (proj1_sig FullCFG.validation_unused)
      (Name "if.end17") varargs) s1 s2 (inl (Name "if.end29"))).
  { apply validation_unused_runs; [lia| | |exact ReadUsed].
    - unfold s1, range_state. rewrite lookup_local_other by discriminate.
      apply lookup_local_same.
    - unfold s1, range_state. rewrite !lookup_local_other by discriminate. exact Used. }
  destruct (@related_store layout c (fst s) bu destination Int.one Relation ltac:(lia))
    as [c1' [m1 [StoreUsed' [WriteUsed [Related1 _]]]]].
  assert (Same1 : c1' = c1) by congruence. subst c1'.
  destruct (@related_store layout c1 m1 bt destination value Related1 ltac:(lia))
    as [c2' [m2 [StoreTarget' [WriteTarget [Related2 _]]]]].
  assert (Same2 : c2' = c2) by congruence. subst c2'.
  assert (ReadData : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (cell_address layout bd index, block_provenance layout bd)) m1 =
      Ret (m1, word_value value)).
  { eapply related_load; [exact Related1|lia|exact LoadData]. }
  pose (s3 := iteration_state layout bd bp bt bu s (Z.of_nat index) (Z.of_nat size)
    (Z.of_nat destination) m1 m2 value).
  assert (Store : runs (denote_block (proj1_sig FullCFG.validation_store)
      (Name "if.end23") varargs) s2 s3
      (inl (if Z.of_nat index + 1 =? Z.of_nat size
            then Name "if.end43.preheader" else Name "if.end17"))).
  { apply validation_store_runs with
      (used_address := cell_address layout bu destination)
      (used_prov := block_provenance layout bu); try lia.
    - unfold s2, s1, unused_state, range_state.
      rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, s1, unused_state, range_state.
      rewrite !lookup_local_other by discriminate. exact Count.
    - unfold s2, unused_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, unused_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
    - unfold s2, s1, unused_state, range_state. rewrite !lookup_local_other by discriminate. exact Data.
    - unfold s2, s1, unused_state, range_state. rewrite !lookup_local_other by discriminate. exact Target.
    - unfold s2, s1, unused_state, range_state. rewrite !memory_set_local. exact WriteUsed.
    - exact ReadData.
    - exact WriteTarget. }
  assert (Other : forall id, ~ In id validation_modified ->
      Maps.lookup id (locals s3) = Maps.lookup id (locals s)).
  { intros id Different. apply iteration_other, Different. }
  exists s3. split.
  - unfold s3. rewrite iteration_memory. exact Related2.
  - split.
    + replace (Z.of_nat (S index)) with (Z.of_nat index + 1) by lia.
      eapply steps_next; [exact (proj2_sig FullCFG.validation_range)|exact CheckRange|].
      eapply steps_next; [exact (proj2_sig FullCFG.validation_unused)|exact Unused|].
      eapply steps_next; [exact (proj2_sig FullCFG.validation_store)|exact Store|constructor].
    + split.
      * constructor; rewrite Other by
          (unfold validation_modified; simpl; intuition discriminate); assumption.
      * split.
        -- replace (Z.of_nat (S index)) with (Z.of_nat index + 1) by lia.
           apply iteration_next.
        -- exact Other.
Qed.

Print Assumptions llvm_validation_step.
