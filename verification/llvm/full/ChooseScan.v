(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightChoose.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks WordArithmetic ChooseBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Scan.
Context (layout : allocation_layout) (bp : Values.block) (xs : list Z) (c : Mem.mem).
Hypothesis Bound : (List.length xs <= 1024)%nat.
Hypothesis Capacity : (List.length xs <= block_words layout bp)%nat.
Hypothesis Values : Forall (fun x => 0 <= x <= 1024) xs.
Hypothesis Array : array_at c bp xs.

Theorem choose_scan_loop varargs : forall k from s,
  (0 < k <= List.length xs)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  choose_scan_input from s (Z.of_nat k) ->
  exists s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end117") s
      (Name "while.end125.loopexit") (Name "while.end125") s' /\
    Maps.lookup (Anon 16) (locals s') =
      Some (word_value (Int.repr (Z.of_nat (ClightChoose.descending_position xs k)))) /\
    (forall id, ~ In id choose_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intro k. induction k as [|k IH]; intros from s K Related Perm Input; [lia|].
  pose (value := List.nth k xs 0).
  assert (ValueBound : 0 <= value <= 1024).
  { apply Forall_forall with (x := value) in Values; [exact Values|]. apply nth_In; lia. }
  assert (N : nth_error xs k = Some value) by (apply nth_error_nth'; lia).
  assert (Current : Z.of_nat (S k) - 1 = Z.of_nat k) by lia.
  pose (s1 := choose_scan_state s (Z.of_nat (S k))
    (block_address layout bp) (block_provenance layout bp) value).
  assert (Step : runs (denote_block (proj1_sig ChooseBlocks.choose_scan) from varargs) s s1
      (inl (if choose_continue (Z.of_nat (S k)) value then Name "if.end117"
        else Name "while.end125.loopexit"))).
  { apply choose_scan_runs; try assumption; try lia. rewrite Current.
    eapply related_load; [exact Related|lia|]. exact (proj1 (Array _ _ N)). }
  assert (Memory1 : fst s1 = fst s) by apply choose_scan_memory.
  assert (Other1 : forall id, ~ In id choose_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply choose_scan_other, Outside. }
  assert (ModelStep : ClightChoose.descending_position xs (S k) =
      if Z.eq_dec value (Z.of_nat k) then ClightChoose.descending_position xs k else k)
    by reflexivity.
  assert (Finish : choose_continue (Z.of_nat (S k)) value = false ->
      ClightChoose.descending_position xs (S k) = k ->
      exists s', fst s' = fst s /\
        block_steps (blks FullCFG.body) varargs from (Name "if.end117") s
          (Name "while.end125.loopexit") (Name "while.end125") s' /\
        Maps.lookup (Anon 16) (locals s') =
          Some (word_value (Int.repr (Z.of_nat (ClightChoose.descending_position xs (S k))))) /\
        (forall id, ~ In id choose_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s))).
  { intros Stop Chosen.
    pose (s2 := set_local s1 (Anon 16) (word_value (Int.repr (Z.of_nat k)))).
    assert (Exit : runs (denote_block (proj1_sig choose_exit) (Name "if.end117") varargs) s1 s2
        (inl (Name "while.end125"))).
    { apply choose_exit_runs; [lia|]. rewrite <- Current. apply choose_scan_index. }
    exists s2. split; [unfold s2; rewrite memory_set_local; exact Memory1|]. split.
    - eapply steps_next; [exact (proj2_sig ChooseBlocks.choose_scan)|rewrite Stop in Step; exact Step|].
      eapply steps_next; [exact (proj2_sig choose_exit)|exact Exit|constructor].
    - split; [rewrite Chosen; apply lookup_local_same|]. intros id Outside. unfold s2.
      rewrite lookup_local_other by
        (intro E; subst id; apply Outside; unfold choose_modified; simpl; tauto).
      apply Other1, Outside. }
  destruct (Z.eq_dec value (Z.of_nat k)) as [Same|Different] eqn:Decision.
  - destruct k as [|k].
    + apply Finish.
      * unfold choose_continue. rewrite Current, Same. reflexivity.
      * rewrite ModelStep. reflexivity.
    + assert (More : choose_continue (Z.of_nat (S (S k))) value = true).
      { unfold choose_continue. rewrite Current, Same, Z.eqb_refl.
        assert (Nonzero : (Z.of_nat (S k) =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite Nonzero. reflexivity. }
      assert (Related1 : cells_related layout c (fst s1)) by (rewrite Memory1; exact Related).
      assert (Perm1 : Maps.lookup (Name "v3") (locals s1) =
          Some (pointer_value (block_address layout bp) (block_provenance layout bp))).
      { rewrite Other1 by (unfold choose_modified; simpl; intuition discriminate). exact Perm. }
      assert (Input1 : choose_scan_input (Name "if.end117") s1 (Z.of_nat (S k))).
      { rewrite <- Current. apply choose_scan_next. }
      destruct (IH (Name "if.end117") s1 ltac:(lia) Related1 Perm1 Input1)
        as [s2 [Memory2 [Steps [Chosen Other2]]]].
      exists s2. split; [rewrite Memory2; exact Memory1|]. split.
      * eapply steps_next; [exact (proj2_sig ChooseBlocks.choose_scan)|rewrite More in Step; exact Step|exact Steps].
      * split; [rewrite ModelStep; exact Chosen|]. intros id Outside.
        rewrite Other2 by exact Outside. apply Other1, Outside.
  - apply Finish.
    + unfold choose_continue. rewrite Current.
      assert (Miss : (Z.of_nat k =? value) = false) by (apply Z.eqb_neq; congruence).
      rewrite Miss. reflexivity.
    + rewrite ModelStep. reflexivity.
Qed.

Theorem choose_descending varargs d s :
  (d < List.length xs)%nat -> cells_related layout c (fst s) ->
  Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Anon 11) (locals s) = Some (word_value (Int.repr (Z.of_nat d))) ->
  exists previous s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs (Name "while.cond106") (Name "while.cond112") s
      previous (Name "while.end125") s' /\
    choose_result_input previous s' (Z.of_nat (ClightChoose.descending_position xs d)) /\
    (forall id, ~ In id choose_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros D Related Perm Value.
  pose (s1 := choose_zero_state s (Int.repr (Z.of_nat d))).
  assert (Compare : word_equal (Int.repr (Z.of_nat d)) Int.zero = (Z.of_nat d =? 0)).
  { unfold word_equal. rewrite small_unsigned by lia. reflexivity. }
  assert (Zero : runs (denote_block (proj1_sig choose_zero) (Name "while.cond106") varargs) s s1
      (inl (if Z.of_nat d =? 0 then Name "while.end125" else Name "if.end117.preheader"))).
  { rewrite <- Compare. apply choose_zero_runs, Value. }
  assert (Memory1 : fst s1 = fst s) by apply choose_zero_memory.
  assert (Other1 : forall id, ~ In id choose_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply choose_zero_other, Outside. }
  destruct d as [|d].
  - exists (Name "while.cond112"), s1. split; [exact Memory1|]. split.
    + eapply steps_next; [exact (proj2_sig choose_zero)|exact Zero|constructor].
    + split; [left; split; reflexivity|exact Other1].
  - assert (Positive : (Z.of_nat (S d) =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Positive in Zero.
    pose (s2 := set_local s1 (Anon 12) (index_value (Z.of_nat (S d)))).
    assert (Preheader : runs (denote_block (proj1_sig choose_preheader) (Name "while.cond112") varargs)
        s1 s2 (inl (Name "if.end117"))).
    { apply choose_preheader_runs; [lia|]. unfold s1, choose_zero_state.
      rewrite lookup_local_other by discriminate. exact Value. }
    assert (Memory2 : fst s2 = fst s) by (unfold s2; rewrite memory_set_local; exact Memory1).
    assert (Other2 : forall id, ~ In id choose_modified ->
        Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
    { intros id Outside. unfold s2. rewrite lookup_local_other by
        (intro E; subst id; apply Outside; unfold choose_modified; simpl; tauto).
      apply Other1, Outside. }
    assert (Related2 : cells_related layout c (fst s2)) by (rewrite Memory2; exact Related).
    assert (Perm2 : Maps.lookup (Name "v3") (locals s2) =
        Some (pointer_value (block_address layout bp) (block_provenance layout bp))).
    { rewrite Other2 by (unfold choose_modified; simpl; intuition discriminate). exact Perm. }
    assert (Input2 : choose_scan_input (Name "if.end117.preheader") s2 (Z.of_nat (S d))).
    { left; split; [reflexivity|apply lookup_local_same]. }
    destruct (@choose_scan_loop varargs (S d) (Name "if.end117.preheader") s2
      ltac:(lia) Related2 Perm2 Input2) as [s3 [Memory3 [Scan [Chosen Other3]]]].
    exists (Name "while.end125.loopexit"), s3. split; [rewrite Memory3; exact Memory2|]. split.
    + eapply steps_next; [exact (proj2_sig choose_zero)|exact Zero|].
      eapply steps_next; [exact (proj2_sig choose_preheader)|exact Preheader|exact Scan].
    + split; [right; split; [reflexivity|exact Chosen]|]. intros id Outside.
      rewrite Other3 by exact Outside. apply Other2, Outside.
Qed.
End Scan.
