(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import ClightMemory ClightChoose ChooseModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks WordArithmetic ChooseBlocks ChooseScan.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition choose_target (selected : option nat) :=
  match selected with Some _ => Name "if.end133" | None => Name "cleanup" end.

Definition choose_binding previous s (selected : option nat) : Prop :=
  match selected with
  | None => previous = Name "while.end125"
  | Some k =>
      (previous = Name "while.cond106" /\ Maps.lookup (Anon 11) (locals s) =
        Some (word_value (Int.repr (Z.of_nat k)))) \/
      (previous = Name "while.end125" /\ Maps.lookup (Name "v11.1") (locals s) =
        Some (word_value (Int.repr (Z.of_nat k))))
  end.

Lemma choose_observation_eq d xs : ChooseModel.choose_observation d xs =
  if List.nth d xs 0 =? Z.of_nat d then
    let k := ClightChoose.descending_position xs d in
    if List.nth k xs 0 =? Z.of_nat k then None else Some k
  else Some (Z.to_nat (List.nth d xs 0)).
Proof.
  unfold ChooseModel.choose_observation, ClightChoose.choose_result.
  destruct (Coqlib.zeq (List.nth d xs 0) (Z.of_nat d)) as [Same|Different].
  - assert (Equal : (List.nth d xs 0 =? Z.of_nat d) = true) by (apply Z.eqb_eq; exact Same).
    rewrite Equal. cbn [fst snd]. unfold ClightChoose.selection_outcome.
    destruct (Coqlib.zeq (List.nth (ClightChoose.descending_position xs d) xs 0)
      (Z.of_nat (ClightChoose.descending_position xs d))) as [Found|Missing].
    + assert (E : (List.nth (ClightChoose.descending_position xs d) xs 0 =?
        Z.of_nat (ClightChoose.descending_position xs d)) = true) by (apply Z.eqb_eq; exact Found).
      rewrite E. reflexivity.
    + assert (E : (List.nth (ClightChoose.descending_position xs d) xs 0 =?
        Z.of_nat (ClightChoose.descending_position xs d)) = false) by (apply Z.eqb_neq; exact Missing).
      rewrite E. cbn. rewrite Nat2Z.id. reflexivity.
  - assert (Equal : (List.nth d xs 0 =? Z.of_nat d) = false) by (apply Z.eqb_neq; exact Different).
    rewrite Equal. reflexivity.
Qed.

Section Choice.
Context (layout : allocation_layout) (bp : Values.block) (xs : list Z) (c : Mem.mem).
Hypothesis Bound : (List.length xs <= 1024)%nat.
Hypothesis Capacity : (List.length xs <= block_words layout bp)%nat.
Hypothesis Values : Forall (fun x => 0 <= x <= 1024) xs.
Hypothesis Array : array_at c bp xs.

Theorem choose_array from varargs d s :
  (d < List.length xs)%nat -> cells_related layout c (fst s) ->
  Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "sub") (locals s) = Some (word_value (Int.repr (Z.of_nat d))) ->
  Maps.lookup (Name "arrayidx109") (locals s) =
    Some (pointer_value (block_address layout bp + 4 * Z.of_nat d) (block_provenance layout bp)) ->
  exists previous s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs from (Name "while.cond106") s
      previous (choose_target (ChooseModel.choose_observation d xs)) s' /\
    choose_binding previous s' (ChooseModel.choose_observation d xs) /\
    (forall id, ~ In id choose_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros D Related Perm Top TopPointer.
  pose (value := List.nth d xs 0).
  assert (ValueBound : 0 <= value <= 1024).
  { apply Forall_forall with (x := value) in Values; [exact Values|]. apply nth_In, D. }
  assert (ValueAt : nth_error xs d = Some value) by (apply nth_error_nth'; exact D).
  pose (s1 := choose_head_state s (Int.repr value) (Int.repr (Z.of_nat d))).
  assert (Compare : word_equal (Int.repr value) (Int.repr (Z.of_nat d)) = (value =? Z.of_nat d)).
  { unfold word_equal. rewrite !small_unsigned by lia. reflexivity. }
  assert (Head : runs (denote_block (proj1_sig choose_head) from varargs) s s1
      (inl (if value =? Z.of_nat d then Name "while.cond112" else Name "if.end133"))).
  { rewrite <- Compare. eapply choose_head_runs; [exact TopPointer|exact Top|].
    eapply related_load; [exact Related|lia|].
    exact (proj1 (Array _ _ ValueAt)). }
  assert (Memory1 : fst s1 = fst s) by apply choose_head_memory.
  assert (Other1 : forall id, ~ In id choose_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply choose_head_other, Outside. }
  destruct (value =? Z.of_nat d) eqn:Equal.
  - assert (Same : value = Z.of_nat d) by (apply Z.eqb_eq; exact Equal).
    assert (Related1 : cells_related layout c (fst s1)) by (rewrite Memory1; exact Related).
    assert (Perm1 : Maps.lookup (Name "v3") (locals s1) =
        Some (pointer_value (block_address layout bp) (block_provenance layout bp))).
    { rewrite Other1 by (unfold choose_modified; simpl; intuition discriminate). exact Perm. }
    assert (Value1 : Maps.lookup (Anon 11) (locals s1) = Some (word_value (Int.repr (Z.of_nat d)))).
    { rewrite <- Same. apply choose_head_value. }
    destruct (@choose_descending layout bp xs c Bound Capacity Values Array varargs d s1
      D Related1 Perm1 Value1) as [previous [s2 [Memory2 [Scan [Input2 Other2]]]]].
    assert (Related2 : cells_related layout c (fst s2)).
    { exact (eq_ind_r (fun m => cells_related layout c m) Related1 Memory2). }
    pose (selected := ClightChoose.descending_position xs d).
    assert (SelectedBound : (selected < List.length xs)%nat).
    { pose proof (descending_position_bound xs d). unfold selected; lia. }
    pose (selected_value := List.nth selected xs 0).
    assert (SelectedAt : nth_error xs selected = Some selected_value)
      by (apply nth_error_nth'; exact SelectedBound).
    assert (SelectedValueBound : 0 <= selected_value <= 1024).
    { apply Forall_forall with (x := selected_value) in Values; [exact Values|].
      apply nth_In, SelectedBound. }
    pose (s3 := choose_result_state s2 (Z.of_nat selected)
      (block_address layout bp) (block_provenance layout bp) (Int.repr selected_value)).
    assert (ResultCompare : word_equal (Int.repr selected_value) (Int.repr (Z.of_nat selected)) =
        (selected_value =? Z.of_nat selected)).
    { unfold word_equal. rewrite !small_unsigned by lia. reflexivity. }
    assert (Result : runs (denote_block (proj1_sig ChooseBlocks.choose_result) previous varargs) s2 s3
        (inl (if selected_value =? Z.of_nat selected then Name "cleanup" else Name "if.end133"))).
    { rewrite <- ResultCompare. apply choose_result_runs; [lia|exact Input2| |].
      - rewrite Other2 by (unfold choose_modified; simpl; intuition discriminate). exact Perm1.
      - eapply related_load; [exact Related2|lia|].
        exact (proj1 (Array _ _ SelectedAt)). }
    assert (Observe : ChooseModel.choose_observation d xs =
        if selected_value =? Z.of_nat selected then None else Some selected).
    { rewrite choose_observation_eq. change (List.nth d xs 0) with value.
      rewrite Equal. reflexivity. }
    rewrite Observe. exists (Name "while.end125"), s3. split.
    + transitivity (fst s2); [apply choose_result_memory|]. exact (eq_trans Memory2 Memory1).
    + split.
      * eapply steps_next; [exact (proj2_sig choose_head)|exact Head|].
        eapply block_steps_append; [exact Scan|].
        eapply steps_next; [exact (proj2_sig ChooseBlocks.choose_result)| |constructor].
        unfold choose_target. destruct (selected_value =? Z.of_nat selected); exact Result.
      * split.
        -- unfold choose_binding. destruct (selected_value =? Z.of_nat selected); [reflexivity|].
           right; split; [reflexivity|apply choose_result_value].
        -- intros id Outside. unfold s3. rewrite choose_result_other by exact Outside.
           rewrite Other2 by exact Outside. apply Other1, Outside.
  - assert (Observe : ChooseModel.choose_observation d xs = Some (Z.to_nat value)).
    { rewrite choose_observation_eq. change (List.nth d xs 0) with value.
      rewrite Equal. reflexivity. }
    rewrite Observe. exists (Name "while.cond106"), s1. split; [exact Memory1|]. split.
    + eapply steps_next; [exact (proj2_sig choose_head)|exact Head|constructor].
    + split; [|exact Other1]. left; split; [reflexivity|].
      rewrite Z2Nat.id by lia. apply choose_head_value.
Qed.
End Choice.
