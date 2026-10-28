(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightChoose ChooseModel ModelArrays CellRelation Choose.
From ASCommon Require Import Common Exec.
From mathcomp Require Import ssrbool eqtype fintype perm.
From ArchSemX86 Require Import X86Inst.
From Legacy Require Import Permute.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Search X86Choice X86ChoiceLoop.
Open Scope Z_scope.
Local Notation nat_of_ord := fintype.nat_of_ord.

Definition choice_machine_target (selected : option nat) : Z :=
  match selected with Some _ => 322 | None => 419 end.

Definition choice_machine_binding state (selected : option nat) : Prop :=
  match selected with
  | Some index => read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index))
  | None => True
  end.

Theorem choose_machine_array nondet layout (frame : call_frame layout program_bytes)
    bp xs c top state :
  (List.length xs <= 1024)%nat ->
  (List.length xs <= block_words (cell_layout layout) bp)%nat ->
  List.Forall (fun value => 0 <= value <= 1024) xs ->
  array_at c bp xs -> (top < List.length xs)%nat ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 275)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + choice_machine_target (ChooseModel.choose_observation top xs))) /\
    choice_machine_binding final (ChooseModel.choose_observation top xs).
Proof.
  intros Bound Capacity Values Array TopBound Related Code Present PC Perm Top.
  pose (value := List.nth top xs 0).
  assert (ValueBound : 0 <= value <= 1024) by (apply choice_value_bound; assumption).
  assert (ValueAt : List.nth_error xs top = Some value) by (apply List.nth_error_nth'; exact TopBound).
  destruct (choice_head nondet layout frame state bp top value c ltac:(lia) ltac:(lia)
    ValueBound Code Present PC Perm Top Related (proj1 (Array _ _ ValueAt)))
    as [headed [Head [HeadFrame [HeadCode [HeadPresent [HeadPC HeadIndex]]]]]].
  destruct (value =? Z.of_nat top) eqn:Equal.
  - assert (Same : value = Z.of_nat top) by (apply Z.eqb_eq; exact Equal).
    rewrite Same in HeadIndex.
    assert (HeadPerm : read_reg_seq_state rdx headed = Some (pointer_to_block layout bp)).
    { rewrite (proj2 HeadFrame rdx) by (unfold search_clobbered; cbn; intuition discriminate). exact Perm. }
    assert (HeadRelated : machine_cells_related layout c (archState.memory (sst headed))).
    { rewrite (proj1 HeadFrame). exact Related. }
    destruct (@choice_descending nondet layout frame bp xs c Bound Capacity Values Array top headed
      TopBound HeadCode HeadPresent HeadPC HeadPerm HeadIndex HeadRelated)
      as [scan_count [scanned [Scan [ScanFrame [ScanCode [ScanPresent [ScanPC ScanIndex]]]]]]].
    pose (selected := ClightChoose.descending_position xs top).
    assert (SelectedBound : (selected < List.length xs)%nat).
    { unfold selected. pose proof (ClightChoose.descending_position_bound xs top). lia. }
    pose (selected_value := List.nth selected xs 0).
    assert (SelectedValueBound : 0 <= selected_value <= 1024) by (apply choice_value_bound; assumption).
    assert (SelectedAt : List.nth_error xs selected = Some selected_value)
      by (apply List.nth_error_nth'; exact SelectedBound).
    assert (ScanPerm : read_reg_seq_state rdx scanned = Some (pointer_to_block layout bp)).
    { rewrite (proj2 ScanFrame rdx) by (unfold search_clobbered; cbn; intuition discriminate). exact HeadPerm. }
    assert (ScanRelated : machine_cells_related layout c (archState.memory (sst scanned))).
    { rewrite (proj1 ScanFrame). exact HeadRelated. }
    destruct (choice_result nondet layout frame scanned bp selected selected_value c ltac:(lia) ltac:(lia)
      SelectedValueBound ScanCode ScanPresent ScanPC ScanPerm ScanIndex ScanRelated (proj1 (Array _ _ SelectedAt)))
      as [result_count [final [Result [ResultFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]]].
    assert (Observe : ChooseModel.choose_observation top xs =
      if selected_value =? Z.of_nat selected then None else Some selected).
    { rewrite choose_observation_eq. change (List.nth top xs 0) with value. rewrite Equal. reflexivity. }
    exists (3 + (scan_count + result_count))%nat, final. split.
    + eapply instruction_steps_append; [exact Head|].
      eapply instruction_steps_append; [exact Scan|exact Result].
    + split.
      * eapply search_frame_trans; [exact HeadFrame|].
        eapply search_frame_trans; [exact ScanFrame|exact ResultFrame].
      * split; [exact FinalCode|]. split; [exact FinalPresent|].
        rewrite Observe. split.
        -- destruct (selected_value =? Z.of_nat selected); exact FinalPC.
        -- unfold choice_machine_binding. destruct (selected_value =? Z.of_nat selected);
             [exact I|exact FinalIndex].
  - assert (Observe : ChooseModel.choose_observation top xs = Some (Z.to_nat value)).
    { rewrite choose_observation_eq. change (List.nth top xs 0) with value. rewrite Equal. reflexivity. }
    exists 3%nat, headed. split; [exact Head|]. split; [exact HeadFrame|].
    split; [exact HeadCode|]. split; [exact HeadPresent|]. rewrite Observe. split; [exact HeadPC|].
    unfold choice_machine_binding. rewrite Z2Nat.id by lia. exact HeadIndex.
Qed.

Theorem choose_machine_permutation nondet layout (frame : call_frame layout program_bytes)
    d (p : 'S_(S d)) bp c state :
  (S d <= 1024)%nat -> (S d <= block_words (cell_layout layout) bp)%nat ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  array_at c bp (words (fun index => nat_of_ord (p index))) ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 275)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat d)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame +
      choice_machine_target (option_map (fun x : 'I_(S d) => nat_of_ord x)
        (Legacy.Permute.choose p ord_max)))) /\
    choice_machine_binding final (option_map (fun x : 'I_(S d) => nat_of_ord x)
      (Legacy.Permute.choose p ord_max)).
Proof.
  intros Bound Capacity Related Array Code Present PC Perm Top.
  assert (Values : List.Forall (fun x => 0 <= x <= 1024)
    (words (fun index => nat_of_ord (p index)))).
  { unfold words. apply List.Forall_map, List.Forall_forall. intros index Inside.
    pose proof (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord (p index))) as Range. lia. }
  assert (Model : ChooseModel.choose_observation d (words (fun index => nat_of_ord (p index))) =
    option_map (fun x : 'I_(S d) => nat_of_ord x) (Legacy.Permute.choose p ord_max)).
  { exact (@choose_matches_model d p (words (fun index => nat_of_ord (p index)))
      (fun x => words_nth (fun index => nat_of_ord (p index)) x)). }
  rewrite <- Model.
  exact (choose_machine_array nondet layout frame bp (words (fun index => nat_of_ord (p index))) c d state
    ltac:(rewrite words_length; exact Bound) ltac:(rewrite words_length; exact Capacity)
    Values Array ltac:(rewrite words_length; lia) Related Code Present PC Perm Top).
Qed.

Print Assumptions choose_machine_array.
Print Assumptions choose_machine_permutation.
