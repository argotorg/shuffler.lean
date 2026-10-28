(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import ClightMemory ClightChoose ChooseModel CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86ArrayDecode X86CellAddress X86Address X86Compare
  X86Alu X86Flags X86Data X86StackMemory X86MemoryStore X86MemoryFrame X86Prologue
  X86StackFrame X86Call X86CallFrame X86Arguments X86UsedZero X86ValidationSteps
  X86Validation X86Search X86ChoiceSteps X86Choice.
Import ListNotations.
Open Scope Z_scope.

Lemma choice_zero nondet layout (frame : call_frame layout program_bytes) state index :
  (index <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 284)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat index =? 0 then 311 else 292))) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat index)).
Proof.
  intros Bound Code Present PC Index.
  destruct (choice_compare_zero nondet layout frame state 284 4 13
    (machine_address (Z.of_nat index)) (Z.of_nat index)
    ltac:(left; reflexivity) ltac:(lia) Code Present PC Index
    ltac:(change (low_register32 0 (machine_address (Z.of_nat index)) = Z_to_bv 32 (Z.of_nat index));
      apply machine_low32; change Int.modulus with 4294967296; lia)) as [f1 [Step1 Zero]].
  pose (s1 := write_reg_seq_state rflags f1 (validation_pc state (entry_pc frame) 288)).
  pose (s2 := validation_pc s1 (entry_pc frame) (if Z.of_nat index =? 0 then 290 else 292)).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { pose proof (choice_jne_step nondet layout frame s1 288 2 2 f1
      (negb (Z.of_nat index =? 0)) ltac:(right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero) as Jump.
    destruct (Z.of_nat index =? 0); exact Jump. }
  assert (Steps2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 2 state s2).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step1|exact Step2]. }
  destruct (Z.of_nat index =? 0) eqn:AtZero.
  - pose (final := validation_pc s2 (entry_pc frame) 311).
    assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s2 final).
    { exact (choice_jump nondet layout frame s2 290 19 ltac:(left; reflexivity)
        ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)). }
    exists 3%nat, final. split.
    + eapply instruction_steps_append with (count := 2%nat) (rest := 1%nat); [exact Steps2|exact Step3].
    + split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|].
      split; validation_reads; [reflexivity|exact Index].
  - exists 2%nat, s2. split; [exact Steps2|].
    split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|].
    split; validation_reads; [reflexivity|exact Index].
Qed.

Lemma choice_result nondet layout (frame : call_frame layout program_bytes)
    state bp index value c :
  (index < 1024)%nat -> (index < block_words (cell_layout layout) bp)%nat ->
  0 <= value <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 311)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat index) = Some (Vint (Int.repr value)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if value =? Z.of_nat index then 419 else 322))) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat index)).
Proof.
  intros IndexBound Capacity Value Code Present PC Perm Index Related Load.
  pose (s1 := write_reg_seq_state rbx (machine_address value)
    (validation_pc state (entry_pc frame) 315)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (choice_load nondet layout frame state 311 4 3 13 bp index value c
      ltac:(right; right; left; reflexivity) Capacity Value Code Present PC Perm Index Related Load). }
  destruct (choice_compare_step nondet layout frame s1 315 3 3 13
    (machine_address value) (machine_address (Z.of_nat index)) value (Z.of_nat index)
    ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address value) = Z_to_bv 32 value);
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; exact Index)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat index)) = Z_to_bv 32 (Z.of_nat index));
      apply machine_low32; change Int.modulus with 4294967296; lia)) as [f2 [Step2 Zero]].
  pose (s2 := write_reg_seq_state rflags f2 (validation_pc s1 (entry_pc frame) 318)).
  pose (s3 := validation_pc s2 (entry_pc frame) (if value =? Z.of_nat index then 320 else 322)).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3).
  { pose proof (choice_jne_step nondet layout frame s2 318 2 2 f2
      (negb (value =? Z.of_nat index)) ltac:(right; right; right; right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero) as Jump.
    destruct (value =? Z.of_nat index); exact Jump. }
  assert (Steps3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 3 state s3).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step2|exact Step3]. }
  destruct (value =? Z.of_nat index) eqn:Equal.
  - pose (final := validation_pc s3 (entry_pc frame) 419).
    assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s3 final).
    { exact (choice_jump nondet layout frame s3 320 97 ltac:(right; left; reflexivity)
        ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)). }
    exists 4%nat, final. split.
    + eapply instruction_steps_append with (count := 3%nat) (rest := 1%nat); [exact Steps3|exact Step4].
    + split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|].
      split; validation_reads; [reflexivity|exact Index].
  - exists 3%nat, s3. split; [exact Steps3|].
    split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|].
    split; validation_reads; [reflexivity|exact Index].
Qed.

Section Descending.
Context (nondet : bool) (layout : finite_layout) (frame : call_frame layout program_bytes)
    (bp : Values.block) (xs : list Z) (c : Mem.mem).
Hypothesis Bound : (List.length xs <= 1024)%nat.
Hypothesis Capacity : (List.length xs <= block_words (cell_layout layout) bp)%nat.
Hypothesis Values : Forall (fun value => 0 <= value <= 1024) xs.
Hypothesis Array : array_at c bp xs.

Theorem choice_scan_loop : forall index state,
  (0 < index <= List.length xs)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 292)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 311)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat (descending_position xs index))).
Proof.
  intro index. induction index as [|index IH]; intros state Range Code Present PC Perm Index Related; [lia|].
  assert (Value : 0 <= List.nth index xs 0 <= 1024) by (apply choice_value_bound; [exact Values|lia]).
  assert (At : nth_error xs index = Some (List.nth index xs 0)) by (apply nth_error_nth'; lia).
  destruct (choice_scan_iteration nondet layout frame state bp (S index) (List.nth index xs 0) c
    ltac:(lia) ltac:(cbn; lia) Value Code Present PC Perm Index Related (proj1 (Array _ _ At)))
    as [step_count [next [Step [StepFrame [NextCode [NextPresent [NextPC NextIndex]]]]]]].
  cbn [Nat.pred] in NextPC, NextIndex.
  assert (NextPerm : read_reg_seq_state rdx next = Some (pointer_to_block layout bp)).
  { rewrite (proj2 StepFrame rdx) by (unfold search_clobbered; cbn; intuition discriminate). exact Perm. }
  assert (NextRelated : machine_cells_related layout c (archState.memory (sst next))).
  { rewrite (proj1 StepFrame). exact Related. }
  destruct (Z.eq_dec (List.nth index xs 0) (Z.of_nat index)) as [Same|Different] eqn:Decision.
  - assert (Equal : (List.nth index xs 0 =? Z.of_nat index) = true) by (apply Z.eqb_eq; exact Same).
    rewrite Equal in NextPC. cbn [andb] in NextPC.
    destruct index as [|index].
    + exists step_count, next. split; [exact Step|]. split; [exact StepFrame|].
      split; [exact NextCode|]. split; [exact NextPresent|]. split; [exact NextPC|].
      change (read_reg_seq_state r13 next = Some (machine_address
        (Z.of_nat (if Z.eq_dec (List.nth 0 xs 0) 0 then 0 else 0)))).
      destruct (Z.eq_dec (List.nth 0 xs 0) 0); exact NextIndex.
    + assert (Positive : (Z.of_nat (S index) =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Positive in NextPC. cbn [negb] in NextPC.
      destruct (IH next ltac:(lia) NextCode NextPresent NextPC NextPerm NextIndex NextRelated)
        as [rest_count [final [Rest [RestFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]]].
      exists (step_count + rest_count)%nat, final. split.
      * eapply instruction_steps_append; [exact Step|exact Rest].
      * split; [eapply search_frame_trans; [exact StepFrame|exact RestFrame]|].
        split; [exact FinalCode|]. split; [exact FinalPresent|]. split; [exact FinalPC|].
        change (read_reg_seq_state r13 final = Some (machine_address (Z.of_nat
          (if Z.eq_dec (List.nth (S index) xs 0) (Z.of_nat (S index))
           then descending_position xs (S index) else S index)))).
        rewrite Decision. exact FinalIndex.
  - assert (Unequal : (List.nth index xs 0 =? Z.of_nat index) = false) by (apply Z.eqb_neq; exact Different).
    rewrite Unequal in NextPC. cbn [andb] in NextPC.
    exists step_count, next. split; [exact Step|]. split; [exact StepFrame|].
    split; [exact NextCode|]. split; [exact NextPresent|]. split; [exact NextPC|].
    change (read_reg_seq_state r13 next = Some (machine_address (Z.of_nat
      (if Z.eq_dec (List.nth index xs 0) (Z.of_nat index) then descending_position xs index else index)))).
    rewrite Decision. exact NextIndex.
Qed.
Theorem choice_descending index state :
  (index < List.length xs)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 284)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 311)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat (descending_position xs index))).
Proof.
  intros IndexBound Code Present PC Perm Index Related.
  destruct (choice_zero nondet layout frame state index ltac:(lia) Code Present PC Index)
    as [zero_count [next [Zero [ZeroFrame [NextCode [NextPresent [NextPC NextIndex]]]]]]].
  destruct index as [|index].
  - exists zero_count, next. split; [exact Zero|]. split; [exact ZeroFrame|].
    split; [exact NextCode|]. split; [exact NextPresent|]. split; [exact NextPC|exact NextIndex].
  - assert (Positive : (Z.of_nat (S index) =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Positive in NextPC.
    assert (NextPerm : read_reg_seq_state rdx next = Some (pointer_to_block layout bp)).
    { rewrite (proj2 ZeroFrame rdx) by (unfold search_clobbered; cbn; intuition discriminate). exact Perm. }
    assert (NextRelated : machine_cells_related layout c (archState.memory (sst next))).
    { rewrite (proj1 ZeroFrame). exact Related. }
    destruct (choice_scan_loop (S index) next ltac:(lia) NextCode NextPresent NextPC NextPerm NextIndex NextRelated)
      as [rest_count [final [Rest [RestFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]]].
    exists (zero_count + rest_count)%nat, final. split.
    + eapply instruction_steps_append; [exact Zero|exact Rest].
    + split; [eapply search_frame_trans; [exact ZeroFrame|exact RestFrame]|].
      split; [exact FinalCode|]. split; [exact FinalPresent|]. split; assumption.
Qed.
End Descending.

Print Assumptions choice_zero.
Print Assumptions choice_result.
Print Assumptions choice_scan_loop.
Print Assumptions choice_descending.
