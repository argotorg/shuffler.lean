(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory.
From Legacy Require Import Permute.
Require Import ClightMemory ModelArrays ChooseModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  ChooseBlocks Choose.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem choose_permutation layout d (p : 'S_(S d)) (bp : Values.block) c s from varargs :
  (S d <= 1024)%coq_nat -> (S d <= block_words layout bp)%coq_nat ->
  cells_related layout c (fst s) ->
  array_at c bp (words (fun x => nat_of_ord (p x))) ->
  Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "sub") (locals s) = Some (word_value (Int.repr (Z.of_nat d))) ->
  Maps.lookup (Name "arrayidx109") (locals s) =
    Some (pointer_value (block_address layout bp + 4 * Z.of_nat d) (block_provenance layout bp)) ->
  exists previous s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs from (Name "while.cond106") s previous
      (choose_target (option_map (fun x : 'I_(S d) => nat_of_ord x) (Legacy.Permute.choose p ord_max))) s' /\
    choose_binding previous s' (option_map (fun x : 'I_(S d) => nat_of_ord x) (Legacy.Permute.choose p ord_max)) /\
    (forall id, ~ List.In id choose_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Bound Capacity Related Array Perm Top TopPointer.
  assert (Values : List.Forall (fun x => 0 <= x <= 1024) (words (fun x => nat_of_ord (p x)))).
  { unfold words. apply List.Forall_map, List.Forall_forall. intros x In.
    pose proof (elimT ltP (ltn_ord (p x))) as Range. lia. }
  assert (Model : ChooseModel.choose_observation d (words (fun x => nat_of_ord (p x))) =
    option_map (fun x : 'I_(S d) => nat_of_ord x) (Legacy.Permute.choose p ord_max)).
  { exact (@choose_matches_model d p (words (fun x => nat_of_ord (p x)))
      (fun x => words_nth (fun y => nat_of_ord (p y)) x)). }
  rewrite <- Model.
  apply (@choose_array layout bp (words (fun x => nat_of_ord (p x))) c
    ltac:(rewrite -> words_length; exact Bound)
    ltac:(rewrite -> words_length; exact Capacity) Values Array from varargs d s
    ltac:(rewrite -> words_length; lia) Related Perm Top TopPointer).
Qed.
