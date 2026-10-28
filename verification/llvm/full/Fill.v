(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ClightFillLoop
  ClightNormalization ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks Fixed SearchBlocks Search SearchModel FillBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Pass.
Context (layout : allocation_layout) (count : nat)
    (source desired : 'I_count -> nat) (bd bt bp bu : Values.block).
Hypothesis Bound : (count <= 1024)%coq_nat.
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (TP : bt <> bp) (TU : bt <> bu) (PU : bp <> bu).
Hypotheses (CD : (count <= block_words layout bd)%coq_nat)
    (CT : (count <= block_words layout bt)%coq_nat)
    (CP : (count <= block_words layout bp)%coq_nat)
    (CU : (count <= block_words layout bu)%coq_nat).
Hypotheses (SourceUInt : forall x, uint (Z.of_nat (source x)))
    (TargetUInt : forall x, uint (Z.of_nat (desired x))).

Record fill_arrays (assignment : 'I_count -> 'I_count) (reserved : {set 'I_count}) (c : Mem.mem) : Prop := {
  fill_data : array_at c bd (words source);
  fill_target : array_at c bt (words desired);
  fill_permutation : array_at c bp (words (fun x => nat_of_ord (assignment x)));
  fill_used : array_at c bu (words (used_flags reserved))
}.

Record fill_registers (s : FusedS) : Prop := {
  fill_size_local : Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count)));
  fill_count_local : Maps.lookup (Name "wide.trip.count314") (locals s) = Some (index_value (Z.of_nat count));
  fill_search_count_local : Maps.lookup (Name "wide.trip.count309") (locals s) = Some (index_value (Z.of_nat count));
  fill_data_local : Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd));
  fill_target_local : Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt));
  fill_permutation_local : Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp));
  fill_used_local : Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu))
}.

Definition fill_frame c final := forall other values, other <> bp -> other <> bu ->
  array_at c other values -> array_at final other values.

Lemma fill_assignment from varargs c s (index chosen : 'I_count) assignment reserved :
  cells_related layout c (fst s) -> fill_arrays assignment reserved c -> fill_registers s ->
  Maps.lookup (Name "indvars.iv311") (locals s) = Some (index_value (Z.of_nat (nat_of_ord index))) ->
  Maps.lookup (Name "v9.0.lcssa") (locals s) = Some (word_value (Int.repr (Z.of_nat (nat_of_ord chosen)))) ->
  exists c' s', cells_related layout c' (fst s') /\
    fill_arrays (write_index assignment index chosen) (chosen |: reserved) c' /\
    runs (denote_block (proj1_sig fill_assign) from varargs) s s' (inl (Name "if.end103")) /\
    Maps.lookup (Name "indvars.iv311") (locals s') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    fill_registers s' /\
    (forall id, ~ In id fill_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fill_frame c c'.
Proof.
  intros Related [AD AT AP AU] [N Count SearchCount Data Target Perm Used] Index Chosen.
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  assert (J : (nat_of_ord chosen < count)%coq_nat) by exact (elimT ltP (ltn_ord chosen)).
  destruct (@related_store layout c (fst s) bp (nat_of_ord index)
    (Int.repr (Z.of_nat (nat_of_ord chosen))) Related ltac:(lia))
    as [c1 [m1 [StorePerm [WritePerm [Related1 _]]]]].
  destruct (@related_store layout c1 m1 bu (nat_of_ord chosen) Int.one Related1 ltac:(lia))
    as [c2 [m2 [StoreUsed [WriteUsed [Related2 _]]]]].
  pose (s2 := fill_assign_state s (Z.of_nat (nat_of_ord index)) (Z.of_nat (nat_of_ord chosen))
    (block_address layout bp) (block_provenance layout bp)
    (block_address layout bu) (block_provenance layout bu) m1 m2).
  assert (Other : forall id, ~ In id fill_modified ->
      Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
  { intros id Outside. apply fill_assign_other, Outside. }
  assert (P1 : array_at c1 bp (words (fun x => nat_of_ord (write_index assignment index chosen x)))).
  { rewrite <- destination_words_update. rewrite <- words_update.
    eapply array_store_same; eassumption. }
  assert (U1 : array_at c1 bu (words (used_flags reserved))).
  { eapply array_store_disjoint; [exact AU|exact (not_eq_sym PU)|exact StorePerm]. }
  exists c2, s2. split; [unfold s2; rewrite -> fill_assign_memory; exact Related2|].
  split.
  - constructor.
    + eapply array_store_disjoint; [|exact DU|exact StoreUsed].
      eapply array_store_disjoint; [exact AD|exact DP|exact StorePerm].
    + eapply array_store_disjoint; [|exact TU|exact StoreUsed].
      eapply array_store_disjoint; [exact AT|exact TP|exact StorePerm].
    + eapply array_store_disjoint; [exact P1|exact PU|exact StoreUsed].
    + rewrite <- used_flags_update. rewrite <- words_update.
      eapply array_store_same; eassumption.
  - split.
    + apply fill_assign_runs; try assumption; lia.
    + split.
      * unfold s2. rewrite -> fill_assign_index. exact Index.
      * split.
        -- constructor; rewrite -> Other by (unfold fill_modified; simpl; intuition discriminate); assumption.
        -- split; [exact Other|]. intros other values NotPerm NotUsed A.
           eapply array_store_disjoint; [|exact NotUsed|exact StoreUsed].
           eapply array_store_disjoint; [exact A|exact NotPerm|exact StorePerm].
Qed.

Definition fill_body_unmodified id := ~ In id fill_modified /\ ~ In id search_modified.

Lemma fill_branch from varargs c s (index : 'I_count) tail assignment reserved final :
  cells_related layout c (fst s) -> fill_arrays assignment reserved c -> fill_registers s ->
  fill_input from s (Z.of_nat (nat_of_ord index)) ->
  raw_fill source desired (index :: tail) assignment reserved = Some final ->
  exists assignment' reserved' c' s' previous,
    raw_fill source desired tail assignment' reserved' = Some final /\
    cells_related layout c' (fst s') /\ fill_arrays assignment' reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") s
      previous (Name "if.end103") s' /\
    Maps.lookup (Name "indvars.iv311") (locals s') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    fill_registers s' /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fill_frame c c'.
Proof.
  intros Related Arrays Registers Input Model.
  destruct Arrays as [AD AT AP AU].
  destruct Registers as [N Count SearchCount Data Target Perm Used].
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  pose (s1 := fill_compare_state s (Z.of_nat (nat_of_ord index))
    (block_address layout bd) (block_provenance layout bd)
    (block_address layout bt) (block_provenance layout bt)
    (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index)))).
  assert (Comparison : runs (denote_block (proj1_sig fill_compare) from varargs) s s1
      (inl (if source index == desired index then Name "if.end103" else Name "if.end77"))).
  { rewrite <- nat_eqb_mathcomp, <- natural_word_equal by auto.
    apply fill_compare_runs; try assumption; try lia.
    - eapply related_load; [exact Related|lia|].
      exact (proj1 (AD _ _ (words_nth_error source index))).
    - eapply related_load; [exact Related|lia|].
      exact (proj1 (AT _ _ (words_nth_error desired index))). }
  assert (Memory1 : fst s1 = fst s) by apply fill_compare_memory.
  assert (Related1 : cells_related layout c (fst s1)) by (rewrite -> Memory1; exact Related).
  assert (Other1 : forall id, ~ In id fill_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply fill_compare_other, Outside. }
  assert (Index1 : Maps.lookup (Name "indvars.iv311") (locals s1) =
      Some (index_value (Z.of_nat (nat_of_ord index)))) by apply fill_compare_index.
  assert (Registers1 : fill_registers s1).
  { constructor; rewrite -> Other1 by (unfold fill_modified; simpl; intuition discriminate); assumption. }
  cbn [raw_fill] in Model. rewrite /fixed_values inE in Model.
  destruct (source index == desired index) eqn:Equal.
  - exists assignment, reserved, c, s1, (Name "if.end65").
    split; [exact Model|]. split; [exact Related1|]. split; [constructor; assumption|].
    split.
    + eapply steps_next; [exact (proj2_sig fill_compare)|exact Comparison|constructor].
    + split; [exact Index1|]. split; [exact Registers1|]. split.
      * intros id [Outside _]. apply Other1, Outside.
      * intros other values NotPerm NotUsed A. exact A.
  - case Choice: (first_free desired (source index) reserved (enum 'I_count))=> [chosen|] in Model;
      last discriminate.
    assert (SearchRegisters : search_registers layout count (source index) bt bu s1).
    { constructor.
      - exact (fill_size_local _ Registers1).
      - exact (fill_search_count_local _ Registers1).
      - exact (fill_target_local _ Registers1).
      - exact (fill_used_local _ Registers1).
      - apply fill_compare_value. }
    destruct (@first_free_search layout count (source index) desired reserved bt bu varargs c s1 chosen
      Bound CT CU (SourceUInt index) TargetUInt Choice Related1 AT AU SearchRegisters)
      as [s2 [Memory2 [Search [Chosen [SearchRegisters2 Other2]]]]].
    assert (Related2 : cells_related layout c (fst s2)) by (rewrite -> Memory2; exact Related1).
    assert (Registers2 : fill_registers s2).
    { destruct Registers1. constructor;
        rewrite -> Other2 by (unfold search_modified; simpl; intuition discriminate); assumption. }
    assert (Index2 : Maps.lookup (Name "indvars.iv311") (locals s2) =
        Some (index_value (Z.of_nat (nat_of_ord index)))).
    { rewrite -> Other2 by (unfold search_modified; simpl; intuition discriminate). exact Index1. }
    destruct (@fill_assignment (Name "while.end93") varargs c s2 index chosen assignment reserved
      Related2 ltac:(constructor; assumption) Registers2 Index2 Chosen)
      as [c3 [s3 [Related3 [Arrays3 [Assign [Index3 [Registers3 [Other3 Frame3]]]]]]]].
    exists (write_index assignment index chosen), (chosen |: reserved), c3, s3, (Name "if.end97").
    split; [exact Model|]. split; [exact Related3|]. split; [exact Arrays3|]. split.
    + eapply steps_next; [exact (proj2_sig fill_compare)|exact Comparison|].
      eapply block_steps_append; [exact Search|].
      eapply steps_next; [exact (proj2_sig fill_assign)|exact Assign|constructor].
    + split; [exact Index3|]. split; [exact Registers3|]. split; [|exact Frame3].
      intros id [OutsideFill OutsideSearch].
      rewrite -> Other3 by exact OutsideFill. rewrite -> Other2 by exact OutsideSearch.
      apply Other1, OutsideFill.
Qed.
End Pass.
