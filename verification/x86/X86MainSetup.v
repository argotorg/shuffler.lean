(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Address X86Data X86Alu X86Compare X86Flags X86Arithmetic
  X86Call X86Arguments X86UsedZero X86ValidationSteps X86Validation.
Import ListNotations.
Open Scope Z_scope.

Lemma setup_copy_size nondet layout (frame : call_frame layout program_bytes)
    state offset destination old number :
  In (offset, destination) [(262, 12); (269, 15)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rdi state = Some old -> low_register32 7 old = Z_to_bv 32 number ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (gpr32_written destination (Z_to_bv 32 number)
      (validation_pc state (entry_pc frame) (offset + 3))).
Proof.
  intros Site Code Present PC Old Low.
  destruct (Present (Values.reg (gpr_reference destination))) as [previous Previous].
  assert (NotPC : Values.reg (gpr_reference destination) <> rip).
  { destruct Site as [Here|[Here|[]]]; inversion Here; subst; discriminate. }
  eapply framed_instruction with (offset := offset) (size := 3)
    (instruction := MOV (32, rm_REG (REG_NORMAL destination), rmi_REG (REG_NORMAL 7)));
    [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|[]]]; inversion Here; subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|[]]]; inversion Here; subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + offset + 3) with (entry_pc frame + (offset + 3)) by lia.
    pose proof (execute_mov32_registers nondet 7 destination
      (validation_pc state (entry_pc frame) (offset + 3)) old previous
      ltac:(unfold validation_pc; rewrite register_read_frame by discriminate; exact Old)
      ltac:(unfold validation_pc; rewrite register_read_frame by congruence; exact Previous)) as Execute.
    fold (low_register32 7 old) in Execute. rewrite Low in Execute. exact Execute.
Qed.

Lemma setup_top nondet layout (frame : call_frame layout program_bytes) state number :
  0 < number <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 265)) ->
  read_reg_seq_state r12 state = Some (machine_address number) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (write_reg_seq_state r12 (machine_address (number - 1))
        (validation_pc state (entry_pc frame) 269))).
Proof.
  intros Range Code Present PC Top.
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 269).
  destruct (execute_sub32_imm8 nondet 12 next (machine_address number) flags (Z_to_bv 8 1)
    ltac:(discriminate)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Top)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 12 (machine_address number)) with
    (low_register32 0 (machine_address number)) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Execute.
  rewrite subtract32 in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (number - 1))) overflow carry
    (zero_flag32 (Z_to_bv 32 (number - 1))) auxiliary parity).
  eapply framed_instruction with (offset := 265) (size := 4)
    (instruction := SUB (false, 32, rm_REG (REG_NORMAL 12), rmi_IMM (IMM8 (Z_to_bv 8 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 265 + 4) with (entry_pc frame + 269) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 12) (@zero_extend 32 (Z_to_bv 32 (number - 1)) 64))
      with (@zero_extend 32 (Z_to_bv 32 (number - 1)) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Lemma setup_trace_capacity nondet layout (frame : call_frame layout program_bytes) state old number :
  0 < number <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 272)) ->
  read_reg_seq_state r15 state = Some (machine_address number) ->
  read_reg_seq_state rdi state = Some old -> low_register32 7 old = Z_to_bv 32 number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (write_reg_seq_state r15 (machine_address (2 * number))
        (validation_pc state (entry_pc frame) 275))).
Proof.
  intros Range Code Present PC Capacity Old Low.
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 275).
  destruct (execute_add32_registers nondet 15 7 next (machine_address number) old flags
    ltac:(discriminate)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Capacity)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Old)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 15 (machine_address number)) with
    (low_register32 0 (machine_address number)) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  rewrite Low, add32_words in Execute.
  replace (number + number) with (2 * number) in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (2 * number))) overflow carry
    (zero_flag32 (Z_to_bv 32 (2 * number))) auxiliary parity).
  eapply framed_instruction with (offset := 272) (size := 3)
    (instruction := ADD (false, 32, rm_REG (REG_NORMAL 15), rmi_REG (REG_NORMAL 7)));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 272 + 3) with (entry_pc frame + 275) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 15) (@zero_extend 32 (Z_to_bv 32 (2 * number)) 64))
      with (@zero_extend 32 (Z_to_bv 32 (2 * number)) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Theorem main_setup_path nondet layout (frame : call_frame layout program_bytes)
    initial state size bd bp bt bu trace output :
  (0 < size <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 262)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 4 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 275)) /\
    read_reg_seq_state r12 final = Some (machine_address (Z.of_nat size - 1)) /\
    read_reg_seq_state r15 final = Some (machine_address (2 * Z.of_nat size)).
Proof.
  intros Range Code Present Arguments Stack PC.
  destruct (core_size _ _ _ _ _ _ _ _ _ Arguments) as (old & Old & Low).
  assert (Low32 : low_register32 7 old = Z_to_bv 32 (Z.of_nat size)).
  { change (bv_extract 0 32 old = Z_to_bv 32 (Z.of_nat size)).
    unfold machine_word in Low. rewrite Int.unsigned_repr in Low;
      [exact Low|change Int.max_unsigned with 4294967295; lia]. }
  pose (s1 := write_reg_seq_state r12 (machine_address (Z.of_nat size))
    (validation_pc state (entry_pc frame) 265)).
  pose proof (setup_copy_size nondet layout frame state 262 12 old (Z.of_nat size)
    ltac:(left; reflexivity) Code Present PC Old Low32) as Step1.
  unfold gpr32_written in Step1.
  change (Values.from_ty (gpr_reference 12) (@zero_extend 32 (Z_to_bv 32 (Z.of_nat size)) 64))
    with (@zero_extend 32 (Z_to_bv 32 (Z.of_nat size)) 64) in Step1.
  rewrite zero_extend32_word in Step1 by (change Int.modulus with 4294967296; lia).
  destruct (setup_top nondet layout frame s1 (Z.of_nat size) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity)) as (flags2 & Step2).
  pose (s2 := write_reg_seq_state rflags flags2
    (write_reg_seq_state r12 (machine_address (Z.of_nat size - 1))
      (validation_pc s1 (entry_pc frame) 269))).
  pose (s3 := write_reg_seq_state r15 (machine_address (Z.of_nat size))
    (validation_pc s2 (entry_pc frame) 272)).
  pose proof (setup_copy_size nondet layout frame s2 269 15 old (Z.of_nat size)
    ltac:(right; left; reflexivity) ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; exact Old) Low32) as Step3.
  unfold gpr32_written in Step3.
  change (Values.from_ty (gpr_reference 15) (@zero_extend 32 (Z_to_bv 32 (Z.of_nat size)) 64))
    with (@zero_extend 32 (Z_to_bv 32 (Z.of_nat size)) 64) in Step3.
  rewrite zero_extend32_word in Step3 by (change Int.modulus with 4294967296; lia).
  destruct (setup_trace_capacity nondet layout frame s3 old (Z.of_nat size) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; exact Old) Low32) as (flags4 & Step4).
  pose (final := write_reg_seq_state rflags flags4
    (write_reg_seq_state r15 (machine_address (2 * Z.of_nat size))
      (validation_pc s3 (entry_pc frame) 275))).
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
  - split; [reflexivity|]. split; [validation_code|]. split; [validation_present|]. split.
    + apply (core_arguments_frame layout size bd bp bt bu trace output state final Arguments).
      intros reg Inside. unfold argument_registers in Inside.
      repeat destruct Inside as [<-|Inside]; try contradiction; validation_reads; reflexivity.
    + split.
      * apply (call_stack_same_memory layout frame initial state final Stack).
        -- validation_reads. reflexivity.
        -- validation_reads. reflexivity.
        -- reflexivity.
      * split; [validation_reads; reflexivity|]. split; validation_reads; reflexivity.
Qed.

Print Assumptions main_setup_path.
