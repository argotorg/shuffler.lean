(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightValidation.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks Validation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma output_stores_array c output final other values :
  output_stores c output final -> other <> output ->
  array_at c other values -> array_at final other values.
Proof.
  intros [c1 [c2 [S0 [S1 S2]]]] Different A.
  eapply array_store_disjoint; [|exact Different|exact S2].
  eapply array_store_disjoint; [|exact Different|exact S1].
  eapply array_store_disjoint; eassumption.
Qed.

Lemma zero_stores_array used start count c final :
  zero_stores used start count c final ->
  forall other values, other <> used -> array_at c other values -> array_at final other values.
Proof.
  intro Stores. induction Stores; intros other values Different A; [exact A|].
  apply IHStores; [exact Different|].
  eapply array_store_disjoint; [exact A|exact Different|exact H].
Qed.

Lemma output_stores_zero c output final :
  output_stores c output final -> array_at final output [0; 0; 0].
Proof.
  intros [c1 [c2 [S0 [S1 S2]]]].
  intros [|[|[|k]]] v H; cbn in H; try discriminate.
  - inversion H; subst v. split.
    + rewrite (Mem.load_store_other Mint32 c2 output 8 _ final S2)
        by (right; left; change (0 + 4 <= 8); lia).
      rewrite (Mem.load_store_other Mint32 c1 output 4 _ c2 S1)
        by (right; left; change (0 + 4 <= 4); lia).
      exact (Mem.load_store_same Mint32 c output 0 _ c1 S0).
    + eapply Mem.store_valid_access_1; [exact S2|].
      eapply Mem.store_valid_access_1; [exact S1|].
      eapply Mem.store_valid_access_1; [exact S0|].
      eapply Mem.store_valid_access_3; exact S0.
  - inversion H; subst v. split.
    + rewrite (Mem.load_store_other Mint32 c2 output 8 _ final S2)
        by (right; left; change (4 + 4 <= 8); lia).
      exact (Mem.load_store_same Mint32 c1 output 4 _ c2 S1).
    + eapply Mem.store_valid_access_1; [exact S2|].
      eapply Mem.store_valid_access_1; [exact S1|].
      eapply Mem.store_valid_access_3; exact S1.
  - inversion H; subst v. split.
    + exact (Mem.load_store_same Mint32 c2 output 8 _ final S2).
    + eapply Mem.store_valid_access_1; [exact S2|].
      eapply Mem.store_valid_access_3; exact S2.
  - destruct k; discriminate.
Qed.

Definition check_unmodified id := prefix_unmodified id /\
  id <> Name "wide.trip.count299" /\ ~ In id validation_modified.

Section Check.
Context (layout : allocation_layout) (size : nat) (xs destinations : list Z)
    (destination : nat -> nat) (bd bp bt bu output : Values.block).
Hypothesis Size : (0 < size <= 1024)%nat.
Hypothesis Length : List.length xs = size.
Hypothesis Destinations : forall k, (k < size)%nat ->
  nth_error destinations k = Some (Z.of_nat (destination k)).
Hypothesis Bounded : forall k, (k < size)%nat -> (destination k < size)%nat.
Hypothesis Injective : forall k q, (k < size)%nat -> (q < size)%nat ->
  destination k = destination q -> k = q.
Hypotheses (DU : bd <> bu) (DT : bd <> bt) (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu)
    (DO : bd <> output) (PO : bp <> output).
Hypotheses (CD : (size <= block_words layout bd)%nat)
    (CP : (size <= block_words layout bp)%nat)
    (CT : (size <= block_words layout bt)%nat)
    (CU : (size <= block_words layout bu)%nat)
    (CO : (3 <= block_words layout output)%nat).

Theorem checked_prefix varargs c s :
  cells_related layout c (fst s) -> array_at c bd xs -> array_at c bp destinations ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
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
  exists c' s', cells_related layout c' (fst s') /\
    ClightValidation.validation_memory size xs destinations destination bd bp bt bu size c' /\
    block_steps (blks FullCFG.body) varargs (Name "entry") (Name "entry") s
      (Name "if.end29") (Name "if.end43.preheader") s' /\
    (forall id, check_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> output -> other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values) /\
    output_registers layout output s' /\
    (output <> bu -> output <> bt -> array_at c' output [0; 0; 0]).
Proof.
  intros Relation AD AP N Data Perm Target Used Output.
  destruct (@initialized_prefix layout output bu size varargs c s Size CO CU Relation N Output Used)
    as [c1 [c2 [s2 [Stores [Zeros [Related2 [Initialization [Locals2 Output2]]]]]]]].
  assert (Initial : ClightValidation.validation_memory size xs destinations destination bd bp bt bu 0 c2).
  { constructor.
    - eapply zero_stores_array; [exact Zeros|exact DU|].
      eapply output_stores_array; eassumption.
    - eapply zero_stores_array; [exact Zeros|exact PU|].
      eapply output_stores_array; eassumption.
    - intros k K. exact (proj1 (Related2 bt k ltac:(lia))).
    - intros k K. exact (proj1 (Related2 bu k ltac:(lia))).
    - intros q value Q. lia.
    - intros q Q Fresh. eapply zero_stores_values; [exact Zeros|lia]. }
  assert (N2 : Maps.lookup (Name "v1") (locals s2) = Some (word_value (Int.repr (Z.of_nat size)))).
  { rewrite Locals2 by (repeat split; discriminate). exact N. }
  assert (Data2 : Maps.lookup (Name "v2") (locals s2) = Some
      (pointer_value (block_address layout bd) (block_provenance layout bd))).
  { rewrite Locals2 by (repeat split; discriminate). exact Data. }
  assert (Perm2 : Maps.lookup (Name "v3") (locals s2) = Some
      (pointer_value (block_address layout bp) (block_provenance layout bp))).
  { rewrite Locals2 by (repeat split; discriminate). exact Perm. }
  assert (Target2 : Maps.lookup (Name "v4") (locals s2) = Some
      (pointer_value (block_address layout bt) (block_provenance layout bt))).
  { rewrite Locals2 by (repeat split; discriminate). exact Target. }
  assert (Used2 : Maps.lookup (Name "v5") (locals s2) = Some
      (pointer_value (block_address layout bu) (block_provenance layout bu))).
  { rewrite Locals2 by (repeat split; discriminate). exact Used. }
  destruct (@Validation.validation_pass layout size xs destinations destination bd bp bt bu
    (proj2 Size) Length Destinations Bounded Injective DU DT PU PT TU CD CP CT CU
    (Name "if.end10") varargs c2 s2 (proj1 Size) Related2 Initial N2 Data2 Perm2 Target2 Used2)
    as [c' [s' [Related [Inv [Steps [Locals Frame]]]]]].
  exists c', s'. split; [exact Related|]. split; [exact Inv|]. split.
  - eapply block_steps_append; eassumption.
  - split.
    + intros id [A [B C]]. rewrite Locals by assumption. apply Locals2, A.
    + split.
      * intros other values NotOutput NotUsed NotTarget A.
        apply Frame; try assumption.
        eapply zero_stores_array; [exact Zeros|exact NotUsed|].
        eapply output_stores_array; eassumption.
      * split.
        -- destruct Output2. constructor; rewrite Locals by
             (unfold validation_modified; simpl; intuition discriminate); assumption.
        -- intros NotUsed NotTarget. apply Frame; try assumption.
           eapply zero_stores_array; [exact Zeros|exact NotUsed|].
           exact (output_stores_zero c output c1 Stores).
Qed.

Corollary checked_prefix_semantics varargs c s :
  cells_related layout c (fst s) -> array_at c bd xs -> array_at c bp destinations ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
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
  exists c' s', cells_related layout c' (fst s') /\
    ClightValidation.validation_memory size xs destinations destination bd bp bt bu size c' /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (Name "entry", Name "entry")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end29", Name "if.end43.preheader")) s')).
Proof.
  intros Relation AD AP N Data Perm Target Used Output.
  destruct (@checked_prefix varargs c s Relation AD AP N Data Perm Target Used Output)
    as [c' [s' [Related [Inv [Steps Rest]]]]].
  exists c', s'. split; [exact Related|]. split; [exact Inv|].
  apply block_steps_sound, Steps.
Qed.
End Check.
