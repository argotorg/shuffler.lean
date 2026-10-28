(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightNormalize ClightNormalization
  ModelArrays SolcModel ModelProofs.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks Validation CheckedPrefix FixedBlocks Fixed FixedPrefix
  SearchBlocks FillBlocks Fill FillLoop.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition normalized_prefix_unmodified id := fixed_prefix_unmodified id /\ fill_unmodified id.

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

Theorem normalized_prefix varargs c s :
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
  exists q c' s', SolcModel.normalize source p = Some q /\ cells_related layout c' (fst s') /\
    array_at c' bd (words source) /\ array_at c' bp (words (fun x => nat_of_ord (q x))) /\
    block_steps (blks FullCFG.body) varargs (Name "entry") (Name "entry") s
      (Name "if.end103") (Name "while.end105") s' /\
    (forall id, normalized_prefix_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values) /\
    output_registers layout output s' /\
    (output <> bu -> output <> bt -> output <> bp -> array_at c' output [0; 0; 0]).
Proof.
  intros Related AD AP N Data Perm Target Used Output.
  destruct (raw_normalize_complete source p)
    as [q [result [Normalized [Raw [Result [Compatible Fixed]]]]]].
  pose (desired := SolcModel.target_of source p).
  pose (good := fixed_values source desired).
  pose (initial := fun x : 'I_(S d) => if x \in good then x else p x).
  change (raw_fill source desired (enum 'I_(S d)) initial good = Some result) in Raw.
  destruct (@fixed_prefix layout d source p bd bp bt bu output Size Values
    DP DU DT PU PT TU DO PO CD CP CT CU CO varargs c s Related AD AP N Data Perm Target Used Output)
    as [c1 [s1 [Related1 [[D1 [T1 [P1 U1]]] [Steps1 [Other1 [Frame1 [Output1 Zeros1]]]]]]]].
  rewrite -> fixed_initial_words in P1. rewrite -> fixed_flag_words in U1.
  assert (Arrays1 : fill_arrays (S d) source desired bd bt bp bu initial good c1).
  { constructor; assumption. }
  assert (Registers : forall id value, fixed_prefix_unmodified id ->
      Maps.lookup id (locals s) = Some value -> Maps.lookup id (locals s1) = Some value).
  { intros id value Outside At. rewrite -> Other1 by exact Outside. exact At. }
  destruct (@fill_pass layout (S d) source desired bd bt bp bu Size DP DU (not_eq_sym PT) TU PU
    CD CT CP CU Values (fun x => Values (p^-1 x)) (Name "if.end57") varargs c1 s1 initial good result
    ltac:(lia) Related1 Arrays1 Raw
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact N])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Data])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Target])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Perm])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Used]))
    as [reserved [c2 [s2 [Related2 [[D2 T2 P2 U2] [Steps2 [Other2 Frame2]]]]]]].
  exists q, c2, s2. split; [exact Normalized|]. split; [exact Related2|].
  split; [exact D2|]. split.
  - assert (Same : words (fun x => nat_of_ord (result x)) = words (fun x => nat_of_ord (q x))).
    { apply words_ext. intro x. rewrite -> Result. reflexivity. }
    rewrite <- Same. exact P2.
  - split.
    + eapply block_steps_append; eassumption.
    + split.
      * intros id [Before Fill]. rewrite -> Other2 by exact Fill. apply Other1, Before.
      * split.
        -- intros other values NotOutput NotUsed NotTarget NotPerm A.
           apply Frame2; try assumption. apply Frame1; assumption.
        -- split.
           ++ destruct Output1. constructor; rewrite -> Other2 by
                (unfold fill_unmodified, fill_body_unmodified, fill_modified, search_modified;
                 simpl; intuition discriminate); assumption.
           ++ intros NotUsed NotTarget NotPerm. apply Frame2; try assumption. apply Zeros1; assumption.
Qed.

Corollary normalized_prefix_semantics varargs c s :
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
  exists q c' s', SolcModel.normalize source p = Some q /\ cells_related layout c' (fst s') /\
    array_at c' bd (words source) /\ array_at c' bp (words (fun x => nat_of_ord (q x))) /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (Name "entry", Name "entry")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end103", Name "while.end105")) s')).
Proof.
  intros Related AD AP N Data Perm Target Used Output.
  destruct (@normalized_prefix varargs c s Related AD AP N Data Perm Target Used Output)
    as [q [c' [s' [Normalized [Related' [D [P [Steps Rest]]]]]]]].
  exists q, c', s'. split; [exact Normalized|]. split; [exact Related'|].
  split; [exact D|]. split; [exact P|]. apply block_steps_sound, Steps.
Qed.
End Check.
