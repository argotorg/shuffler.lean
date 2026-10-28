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
  X86Validation X86Search X86ChoiceSteps.
Import ListNotations.
Open Scope Z_scope.

Lemma choice_load nondet layout (frame : call_frame layout program_bytes)
    state offset bytes destination index_register bp index value c :
  In (offset, bytes, destination, index_register) [(275, 4, 13, 12); (296, 4, 3, 13); (311, 4, 3, 13)] ->
  (index < block_words (cell_layout layout) bp)%nat -> 0 <= value <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state (Values.reg (gpr_reference index_register)) state =
    Some (Values.from_ty (gpr_reference index_register) (machine_address (Z.of_nat index))) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat index) = Some (Vint (Int.repr value)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination) (machine_address value))
      (validation_pc state (entry_pc frame) (offset + bytes))).
Proof.
  intros Site Capacity Value Code Present PC Perm Index Related Load.
  assert (InTable : In (offset, bytes, destination, 2, index_register) array_load_sites).
  { destruct Site as [Here|[Here|[Here|No]]];
      [inversion Here|inversion Here|inversion Here|contradiction];
      subst; unfold array_load_sites; cbn; tauto. }
  assert (NotPC : Values.reg (gpr_reference destination) <> rip).
  { destruct Site as [Here|[Here|[Here|No]]];
      [inversion Here|inversion Here|inversion Here|contradiction]; subst; discriminate. }
  pose proof (validation_array_load nondet layout frame state offset bytes destination 2
    index_register bp index (Int.repr value) c InTable NotPC Capacity Code Present PC
    ltac:(apply validation_scaled_address; [exact Perm|exact Index]) Related Load) as Step.
  unfold gpr32_written in Step. rewrite zero_extend_word_repr in Step
    by (change Int.modulus with 4294967296; lia).
  exact Step.
Qed.

Lemma choice_value_bound xs index :
  Forall (fun value => 0 <= value <= 1024) xs -> (index < List.length xs)%nat ->
  0 <= List.nth index xs 0 <= 1024.
Proof.
  intros Values Index. apply List.Forall_forall with (x := List.nth index xs 0) in Values;
    [exact Values|apply nth_In, Index].
Qed.

Lemma choice_head nondet layout (frame : call_frame layout program_bytes)
    state bp top value c :
  (top < 1024)%nat -> (top < block_words (cell_layout layout) bp)%nat ->
  0 <= value <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 275)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat top) = Some (Vint (Int.repr value)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 3 state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if value =? Z.of_nat top then 284 else 322))) /\
    read_reg_seq_state r13 final = Some (machine_address value).
Proof.
  intros Top Capacity Value Code Present PC Perm Index Related Load.
  pose (s1 := write_reg_seq_state r13 (machine_address value)
    (validation_pc state (entry_pc frame) 279)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (choice_load nondet layout frame state 275 4 13 12 bp top value c
      ltac:(left; reflexivity) Capacity Value Code Present PC Perm Index Related Load). }
  destruct (choice_compare_step nondet layout frame s1 279 3 13 12
    (machine_address value) (machine_address (Z.of_nat top)) value (Z.of_nat top)
    ltac:(left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address value) = Z_to_bv 32 value);
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; exact Index)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat top)) = Z_to_bv 32 (Z.of_nat top));
      apply machine_low32; change Int.modulus with 4294967296; lia)) as [flags [Step2 Zero]].
  pose (s2 := write_reg_seq_state rflags flags (validation_pc s1 (entry_pc frame) 282)).
  pose (final := validation_pc s2 (entry_pc frame) (if value =? Z.of_nat top then 284 else 322)).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 final).
  { pose proof (choice_jne_step nondet layout frame s2 282 38 38 flags
      (negb (value =? Z.of_nat top)) ltac:(left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero) as Jump.
    destruct (value =? Z.of_nat top); exact Jump. }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step2|exact Step3].
  - split; [search_frame_build|]. split; [validation_code|].
    split; [validation_present|]. split; validation_reads; reflexivity.
Qed.

Lemma choice_scan_iteration nondet layout (frame : call_frame layout program_bytes)
    state bp index value c :
  (0 < index <= 1024)%nat -> (Nat.pred index < block_words (cell_layout layout) bp)%nat ->
  0 <= value <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 292)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat (Nat.pred index)) = Some (Vint (Int.repr value)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame +
      (if andb (value =? Z.of_nat (Nat.pred index)) (negb (Z.of_nat (Nat.pred index) =? 0))
       then 292 else 311))) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat (Nat.pred index))).
Proof.
  intros Range Capacity Value Code Present PC Perm Index Related Load.
  destruct (choice_decrement nondet layout frame state index Range Code Present PC Index)
    as [f1 Step1].
  pose (s1 := write_reg_seq_state rflags f1
    (write_reg_seq_state r13 (machine_address (Z.of_nat (Nat.pred index)))
      (validation_pc state (entry_pc frame) 296))).
  pose (s2 := write_reg_seq_state rbx (machine_address value)
    (validation_pc s1 (entry_pc frame) 300)).
  assert (Related1 : machine_cells_related layout c (archState.memory (sst s1))).
  { validation_states. rewrite !register_write_memory. exact Related. }
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { exact (choice_load nondet layout frame s1 296 4 3 13 bp (Nat.pred index) value c
      ltac:(right; left; reflexivity) Capacity Value
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; exact Perm) ltac:(validation_reads; reflexivity) Related1 Load). }
  destruct (choice_compare_step nondet layout frame s2 300 3 3 13
    (machine_address value) (machine_address (Z.of_nat (Nat.pred index))) value (Z.of_nat (Nat.pred index))
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address value) = Z_to_bv 32 value);
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat (Nat.pred index))) =
        Z_to_bv 32 (Z.of_nat (Nat.pred index)));
      apply machine_low32; change Int.modulus with 4294967296; lia)) as [f3 [Step3 Zero3]].
  pose (s3 := write_reg_seq_state rflags f3 (validation_pc s2 (entry_pc frame) 303)).
  pose (s4 := validation_pc s3 (entry_pc frame)
    (if value =? Z.of_nat (Nat.pred index) then 305 else 311)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { pose proof (choice_jne_step nondet layout frame s3 303 6 6 f3
      (negb (value =? Z.of_nat (Nat.pred index))) ltac:(right; right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero3) as Jump.
    destruct (value =? Z.of_nat (Nat.pred index)); exact Jump. }
  assert (Steps4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 4 state s4).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4]. }
  destruct (value =? Z.of_nat (Nat.pred index)) eqn:Equal.
  - destruct (choice_compare_zero nondet layout frame s4 305 4 13
      (machine_address (Z.of_nat (Nat.pred index))) (Z.of_nat (Nat.pred index))
      ltac:(right; left; reflexivity) ltac:(lia)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity)
      ltac:(change (low_register32 0 (machine_address (Z.of_nat (Nat.pred index))) =
          Z_to_bv 32 (Z.of_nat (Nat.pred index)));
        apply machine_low32; change Int.modulus with 4294967296; lia)) as [f5 [Step5 Zero5]].
    pose (s5 := write_reg_seq_state rflags f5 (validation_pc s4 (entry_pc frame) 309)).
    pose (final := validation_pc s5 (entry_pc frame)
      (if Z.of_nat (Nat.pred index) =? 0 then 311 else 292)).
    assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s5 final).
    { pose proof (choice_jne_step nondet layout frame s5 309 237 (-19) f5
        (negb (Z.of_nat (Nat.pred index) =? 0)) ltac:(right; right; right; left; reflexivity)
        ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
        ltac:(validation_reads; reflexivity) Zero5) as Jump.
      destruct (Z.of_nat (Nat.pred index) =? 0); exact Jump. }
    exists 6%nat, final. split.
    + eapply instruction_steps_append with (count := 4%nat) (rest := 2%nat); [exact Steps4|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step5|exact Step6].
    + split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|]. split.
      * validation_reads. destruct (Z.of_nat (Nat.pred index) =? 0); reflexivity.
      * validation_reads. reflexivity.
  - exists 4%nat, s4. split; [exact Steps4|].
    split; [search_frame_build|]. split; [validation_code|]. split; [validation_present|].
    split; validation_reads; reflexivity.
Qed.

Print Assumptions choice_head.
Print Assumptions choice_scan_iteration.
