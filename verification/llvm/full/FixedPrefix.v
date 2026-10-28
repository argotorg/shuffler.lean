(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightValidation ClightNormalize
  ModelArrays SolcModel ClightCorrect.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks Validation CheckedPrefix FixedBlocks Fixed.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition fixed_prefix_unmodified id := check_unmodified id /\ fixed_unmodified id.

Section Check.
Context (layout : allocation_layout) (d : nat) (source : 'I_(S d) -> nat) (p : 'S_(S d))
    (bd bp bt bu output : Values.block).
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypothesis Values : forall x, uint (Z.of_nat (source x)).
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (DT : bd <> bt)
    (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu) (DO : bd <> output) (PO : bp <> output).
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (S d <= block_words layout bt)%coq_nat)
    (CU : (S d <= block_words layout bu)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Definition fixed_prefix_arrays c :=
  array_at c bd (words source) /\
  array_at c bt (words (SolcModel.target_of source p)) /\
  array_at c bp (words (fun x => if Nat.eqb (source x) (SolcModel.target_of source p x)
    then nat_of_ord x else nat_of_ord (p x))) /\
  array_at c bu (words (fixed_flags source (SolcModel.target_of source p))).

Theorem fixed_prefix varargs c s :
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun x => nat_of_ord (p x))) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat (S d)))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  exists c' s', cells_related layout c' (fst s') /\ fixed_prefix_arrays c' /\
    block_steps (blks FullCFG.body) varargs (Name "entry") (Name "entry") s
      (Name "if.end57") (Name "if.end65.preheader") s' /\
    (forall id, fixed_prefix_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values) /\
    output_registers layout output s' /\
    (output <> bu -> output <> bt -> output <> bp -> array_at c' output [0; 0; 0]).
Proof.
  intros Relation AD AP N Data Perm Target Used Output.
  destruct (@checked_prefix layout (S d) (words source) (words (fun x => nat_of_ord (p x)))
    (destination_at p) bd bp bt bu output ltac:(lia) (words_length source)
    (@destination_at_words d p) (fun k _ => @destination_at_bound d p k)
    (@destination_at_injective d p) DU DT PU PT TU DO PO CD CP CT CU CO
    varargs c s Relation AD AP N Data Perm Target Used Output)
    as [c1 [s1 [Related1 [Inv [Steps1 [Locals1 [Frame1 [Output1 Zeros1]]]]]]]].
  destruct Inv as [D1 P1 WT WU Loads Unused].
  assert (T1 : array_at c1 bt (words (SolcModel.target_of source p))).
  { exact (@target_array_from_destinations d source p c1 bt WT Loads). }
  assert (Registers : forall id value, check_unmodified id ->
      Maps.lookup id (locals s) = Some value -> Maps.lookup id (locals s1) = Some value).
  { intros id value Outside At. rewrite -> Locals1 by exact Outside. exact At. }
  destruct (@fixed_pass layout (S d) source (SolcModel.target_of source p) bd bt bp bu
    Size DP DU (not_eq_sym PT) TU PU CD CT CP CU Values
    (fun x => Values (p^-1 x)) (Name "if.end29") varargs c1 s1
    (fun x => nat_of_ord (p x)) ltac:(lia) Related1 D1 T1 P1
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact N])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Data])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Target])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Perm])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Used]))
    as [c' [s' [Related [Arrays [Steps [Locals Frame]]]]]].
  exists c', s'. split; [exact Related|]. split.
  - destruct Arrays as [D T P U]. exact (conj D (conj T (conj P U))).
  - split.
    + eapply block_steps_append; eassumption.
    + split.
      * intros id [Checked Fixed]. rewrite -> Locals by exact Fixed. apply Locals1, Checked.
      * split.
        -- intros other values NotOutput NotUsed NotTarget NotPerm A.
           apply Frame; try assumption. apply Frame1; assumption.
        -- split.
           ++ destruct Output1. constructor; rewrite -> Locals by
                (unfold fixed_unmodified, fixed_modified; simpl; intuition discriminate); assumption.
           ++ intros NotUsed NotTarget NotPerm. apply Frame; try assumption. apply Zeros1; assumption.
Qed.

Corollary fixed_prefix_semantics varargs c s :
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun x => nat_of_ord (p x))) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat (S d)))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  exists c' s', cells_related layout c' (fst s') /\ fixed_prefix_arrays c' /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (Name "entry", Name "entry")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end57", Name "if.end65.preheader")) s')).
Proof.
  intros Relation AD AP N Data Perm Target Used Output.
  destruct (@fixed_prefix varargs c s Relation AD AP N Data Perm Target Used Output)
    as [c' [s' [Related [Arrays [Steps Rest]]]]].
  exists c', s'. split; [exact Related|]. split; [exact Arrays|].
  apply block_steps_sound, Steps.
Qed.
End Check.
