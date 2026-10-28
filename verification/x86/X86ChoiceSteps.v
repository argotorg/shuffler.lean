(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Address X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments X86UsedZero X86ValidationSteps.
Import ListNotations.
Open Scope Z_scope.

Lemma choice_compare_zero nondet layout (frame : call_frame layout program_bytes)
    state offset bytes index old number :
  In (offset, bytes, index) [(284, 4, 13); (305, 4, 13)] ->
  0 <= number < 4294967296 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  low_register32 index old = Z_to_bv 32 number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (number =? 0).
Proof.
  intros Site Range Code Present PC Old Low.
  assert (NotPC : Values.reg (gpr_reference index) <> rip).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction]; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  assert (ReadNext : read_reg_seq_state (Values.reg (gpr_reference index)) next = Some old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm8 nondet index next old flags (Z_to_bv 8 0) ReadNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  change (@sign_extend 8 (Z_to_bv 8 0) 32) with (Z_to_bv 32 0) in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 number) (Z_to_bv 32 0)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL index), rmi_IMM (IMM8 (Z_to_bv 8 0))));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - unfold result. apply comparison_jne; lia.
Qed.

Lemma choice_compare_step nondet layout (frame : call_frame layout program_bytes)
    state offset bytes first second first_old second_old first_number second_number :
  In (offset, bytes, first, second) [(279, 3, 13, 12); (300, 3, 3, 13); (315, 3, 3, 13)] ->
  0 <= first_number < 4294967296 -> 0 <= second_number < 4294967296 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference first)) state = Some first_old ->
  low_register32 first first_old = Z_to_bv 32 first_number ->
  read_reg_seq_state (Values.reg (gpr_reference second)) state = Some second_old ->
  low_register32 second second_old = Z_to_bv 32 second_number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (first_number =? second_number).
Proof.
  intros Site FirstRange SecondRange Code Present PC First FirstLow Second SecondLow.
  assert (FirstNotPC : Values.reg (gpr_reference first) <> rip).
  { destruct Site as [Here|[Here|[Here|No]]]; [inversion Here|inversion Here|inversion Here|contradiction]; subst; discriminate. }
  assert (SecondNotPC : Values.reg (gpr_reference second) <> rip).
  { destruct Site as [Here|[Here|[Here|No]]]; [inversion Here|inversion Here|inversion Here|contradiction]; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  assert (FirstNext : read_reg_seq_state (Values.reg (gpr_reference first)) next = Some first_old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact First. }
  assert (SecondNext : read_reg_seq_state (Values.reg (gpr_reference second)) next = Some second_old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact Second. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_registers nondet first second next first_old second_old flags
    FirstNext SecondNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite FirstLow, SecondLow in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 first_number) (Z_to_bv 32 second_number)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL first), rmi_REG (REG_NORMAL second)));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|[Here|No]]]; [inversion Here|inversion Here|inversion Here|contradiction];
        subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|[Here|No]]]; [inversion Here|inversion Here|inversion Here|contradiction];
        subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - unfold result. apply comparison_jne; assumption.
Qed.

Lemma choice_jne_step nondet layout (frame : call_frame layout program_bytes)
    state offset byte displacement flags taken :
  In (offset, byte, displacement) [(282, 38, 38); (288, 2, 2); (303, 6, 6); (309, 237, -19); (318, 2, 2)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame)
      (if taken then offset + 2 + displacement else offset + 2)).
Proof.
  intros Site Code Present PC Flags Taken.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 byte) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|[Here|[Here|[Here|No]]]]]; [inversion Here|inversion Here|inversion Here|inversion Here|inversion Here|contradiction];
      subst; apply bv_eq; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNE (Z_to_bv 8 byte)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|[Here|[Here|[Here|No]]]]]; [inversion Here|inversion Here|inversion Here|inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|[Here|[Here|[Here|No]]]]]; [inversion Here|inversion Here|inversion Here|inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jne with (pc := machine_address (entry_pc frame + offset + 2)) (flags := flags).
    + rewrite Taken. destruct taken.
      * rewrite Extend.
        change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
          with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + offset + 2 + displacement) with
          (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
      * replace (entry_pc frame + offset + 2) with (entry_pc frame + (offset + 2)) by lia.
        reflexivity.
    + apply register_read_written.
    + rewrite register_read_frame by discriminate. exact Flags.
Qed.

Lemma sub32_words first second :
  @sub_vec 32 (Z_to_bv 32 first) (Z_to_bv 32 second) = Z_to_bv 32 (first - second).
Proof.
  change (bv_sub (Z_to_bv 32 first) (Z_to_bv 32 second) = Z_to_bv 32 (first - second)).
  apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned, bv_wrap_sub_idemp. reflexivity.
Qed.

Lemma choice_decrement nondet layout (frame : call_frame layout program_bytes)
    state index :
  (0 < index <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 292)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags
        (write_reg_seq_state r13 (machine_address (Z.of_nat (Nat.pred index)))
          (validation_pc state (entry_pc frame) 296))).
Proof.
  intros Range Code Present PC Counter.
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 296).
  assert (CounterNext : read_reg_seq_state r13 next = Some (machine_address (Z.of_nat index))).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Counter. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_sub32_imm8 nondet 13 next (machine_address (Z.of_nat index)) flags
    (Z_to_bv 8 1) ltac:(discriminate) CounterNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute.
  change (low_register32 13 (machine_address (Z.of_nat index)))
    with (low_register32 0 (machine_address (Z.of_nat index))) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Execute.
  rewrite sub32_words in Execute.
  replace (Z.of_nat index - 1) with (Z.of_nat (Nat.pred index)) in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (Z.of_nat (Nat.pred index)))) overflow carry
    (zero_flag32 (Z_to_bv 32 (Z.of_nat (Nat.pred index)))) auxiliary parity).
  eapply framed_instruction with (offset := 292) (size := 4)
    (instruction := SUB (false, 32, rm_REG (REG_NORMAL 13), rmi_IMM (IMM8 (Z_to_bv 8 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 292 + 4) with (entry_pc frame + 296) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 13)
      (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (Nat.pred index))) 64))
      with (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (Nat.pred index))) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Print Assumptions choice_decrement.

Lemma choice_jump nondet layout (frame : call_frame layout program_bytes) state offset displacement :
  In (offset, displacement) [(290, 19); (320, 97)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame) (offset + 2 + displacement)).
Proof.
  intros Site Code Present PC.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 displacement) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; apply bv_eq; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JMP (Z_to_bv 8 displacement)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jmp8 with (pc := machine_address (entry_pc frame + offset + 2)).
    + rewrite Extend.
      change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
        with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
      rewrite machine_address_next, register_write_overwrite.
      replace (entry_pc frame + offset + 2 + displacement)
        with (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
    + apply register_read_written.
Qed.

Print Assumptions choice_jump.
