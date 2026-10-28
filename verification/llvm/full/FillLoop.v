(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ClightFillLoop ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  SearchBlocks FillBlocks Fill.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition fill_unmodified id := fill_body_unmodified id /\
  id <> Name "wide.trip.count314" /\ id <> Name "wide.trip.count309".

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
Local Notation arrays := (fill_arrays count source desired bd bt bp bu).
Local Notation registers := (fill_registers layout count bd bt bp bu).

Lemma fill_iteration from varargs c s (index : 'I_count) assignment reserved final :
  cells_related layout c (fst s) -> arrays assignment reserved c -> registers s ->
  fill_input from s (Z.of_nat (nat_of_ord index)) ->
  raw_fill source desired (List.skipn (nat_of_ord index) (enum 'I_count)) assignment reserved = Some final ->
  exists assignment' reserved' c' s',
    raw_fill source desired (List.skipn (S (nat_of_ord index)) (enum 'I_count)) assignment' reserved' = Some final /\
    cells_related layout c' (fst s') /\ arrays assignment' reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") s
      (Name "if.end103") (if Z.of_nat (nat_of_ord index) + 1 =? Z.of_nat count
        then Name "while.end105" else Name "if.end65") s' /\
    registers s' /\ fill_input (Name "if.end103") s' (Z.of_nat (S (nat_of_ord index))) /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fill_frame bp bu c c'.
Proof.
  intros Related Arrays Registers Input Model.
  rewrite (ordinal_enum_step index) in Model.
  destruct (@fill_branch layout count source desired bd bt bp bu Bound DP DU TP TU PU
    CD CT CP CU SourceUInt TargetUInt from varargs c s index
    (List.skipn (S (nat_of_ord index)) (enum 'I_count)) assignment reserved final
    Related Arrays Registers Input Model)
    as [assignment1 [reserved1 [c1 [s1 [previous
      [Model1 [Related1 [Arrays1 [Branch [Index1 [Registers1 [Other1 Frame1]]]]]]]]]]]].
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  pose (s2 := fill_next_state s1 (Z.of_nat (nat_of_ord index)) (Z.of_nat count)).
  assert (Next : runs (denote_block (proj1_sig fill_next) previous varargs) s1 s2
      (inl (if Z.of_nat (nat_of_ord index) + 1 =? Z.of_nat count
        then Name "while.end105" else Name "if.end65"))).
  { apply fill_next_runs; try lia; [exact Index1|exact (fill_count_local _ _ _ _ _ _ _ Registers1)]. }
  exists assignment1, reserved1, c1, s2.
  split; [exact Model1|]. split; [unfold s2; rewrite -> fill_next_memory; exact Related1|].
  split; [exact Arrays1|]. split.
  - eapply block_steps_append; [exact Branch|].
    eapply steps_next; [exact (proj2_sig fill_next)|exact Next|constructor].
  - split.
    + destruct Registers1. constructor; unfold s2; rewrite -> fill_next_other by
        (unfold fill_modified; simpl; intuition discriminate); assumption.
    + split.
      * rewrite -> Nat2Z.inj_succ. replace (Z.succ (Z.of_nat (nat_of_ord index))) with
          (Z.of_nat (nat_of_ord index) + 1) by lia. apply fill_next_input.
      * split; [|exact Frame1]. intros id Outside. unfold s2.
        rewrite -> fill_next_other by exact (proj1 Outside). apply Other1, Outside.
Qed.

Theorem fill_loop varargs final : forall remaining start from assignment reserved c s,
  (0 < remaining)%coq_nat -> (start + remaining = count)%coq_nat ->
  cells_related layout c (fst s) -> arrays assignment reserved c -> registers s ->
  fill_input from s (Z.of_nat start) ->
  raw_fill source desired (List.skipn start (enum 'I_count)) assignment reserved = Some final ->
  exists reserved' c' s', cells_related layout c' (fst s') /\ arrays final reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") s
      (Name "if.end103") (Name "while.end105") s' /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fill_frame bp bu c c'.
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from assignment reserved c s Positive Sum Related Arrays Registers Input Model; [lia|].
  assert (K : (start < count)%coq_nat) by lia.
  pose index : 'I_count := Ordinal (introT ltP K).
  destruct (@fill_iteration from varargs c s index assignment reserved final
    Related Arrays Registers Input Model)
    as [assignment1 [reserved1 [c1 [s1 [Model1 [Related1 [Arrays1 [Step
      [Registers1 [Input1 [Other1 Frame1]]]]]]]]]]].
  change (nat_of_ord index) with start in Model1, Step, Input1.
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat start + 1 =? Z.of_nat count) = true) by (apply Z.eqb_eq; lia).
    rewrite -> Last in Step.
    replace (S start) with count in Model1 by lia.
    rewrite ordinal_enum_end in Model1. cbn [raw_fill] in Model1.
    injection Model1 as E. subst assignment1.
    exists reserved1, c1, s1. split; [exact Related1|]. split; [exact Arrays1|].
    split; [exact Step|]. split; assumption.
  - assert (More : (Z.of_nat start + 1 =? Z.of_nat count) = false) by (apply Z.eqb_neq; lia).
    rewrite -> More in Step.
    destruct (IH (S start) (Name "if.end103") assignment1 reserved1 c1 s1
      ltac:(lia) ltac:(lia) Related1 Arrays1 Registers1 Input1 Model1)
      as [reserved' [c' [s' [Related' [Arrays' [Steps [Other Frame]]]]]]].
    exists reserved', c', s'. split; [exact Related'|]. split; [exact Arrays'|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * intros id Outside. rewrite -> Other by exact Outside. apply Other1, Outside.
      * intros other values NotPerm NotUsed A. apply Frame; try assumption. apply Frame1; assumption.
Qed.

Theorem fill_pass from varargs c s assignment reserved final : (0 < count)%coq_nat ->
  cells_related layout c (fst s) -> arrays assignment reserved c ->
  raw_fill source desired (enum 'I_count) assignment reserved = Some final ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  exists reserved' c' s', cells_related layout c' (fst s') /\ arrays final reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65.preheader") s
      (Name "if.end103") (Name "while.end105") s' /\
    (forall id, fill_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fill_frame bp bu c c'.
Proof.
  intros Positive Related Arrays Model N Data Target Perm Used.
  pose (s1 := fill_preheader_state s (Z.of_nat count)).
  assert (Related1 : cells_related layout c (fst s1)).
  { unfold s1, fill_preheader_state. rewrite -> !memory_set_local. exact Related. }
  assert (Registers1 : registers s1).
  { constructor; unfold s1, fill_preheader_state;
      repeat first [apply lookup_local_same | rewrite -> lookup_local_other by discriminate]; assumption. }
  destruct (@fill_loop varargs final count 0 (Name "if.end65.preheader") assignment reserved c s1
    Positive Logic.eq_refl Related1 Arrays Registers1
    (or_introl (conj Logic.eq_refl Logic.eq_refl)) Model)
    as [reserved' [c' [s' [Related' [Arrays' [Steps [Other Frame]]]]]]].
  exists reserved', c', s'. split; [exact Related'|]. split; [exact Arrays'|]. split.
  - eapply steps_next; [exact (proj2_sig fill_preheader)| |exact Steps].
    apply fill_preheader_runs; [lia|exact N].
  - split; [|exact Frame]. intros id [Outside [Different1 Different2]].
    rewrite -> Other by exact Outside. unfold s1, fill_preheader_state.
    rewrite -> !lookup_local_other by assumption. reflexivity.
Qed.

Corollary fill_pass_semantics from varargs c s assignment reserved final : (0 < count)%coq_nat ->
  cells_related layout c (fst s) -> arrays assignment reserved c ->
  raw_fill source desired (enum 'I_count) assignment reserved = Some final ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat (count)))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  exists reserved' c' s', cells_related layout c' (fst s') /\ arrays final reserved' c' /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (from, Name "if.end65.preheader")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end103", Name "while.end105")) s')).
Proof.
  intros Positive Related Arrays Model N Data Target Perm Used.
  destruct (@fill_pass from varargs c s assignment reserved final Positive Related Arrays Model
    N Data Target Perm Used) as [reserved' [c' [s' [Related' [Arrays' [Steps Rest]]]]]].
  exists reserved', c', s'. split; [exact Related'|]. split; [exact Arrays'|].
  apply block_steps_sound, Steps.
Qed.
End Pass.
