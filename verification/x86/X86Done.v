(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Address X86Data X86Alu X86Flags X86Call X86Arguments
  X86ValidationSteps X86Validation.
Import ListNotations.
Open Scope Z_scope.

Theorem done_path nondet layout (frame : call_frame layout program_bytes) initial state :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 419)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 2 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax final = Some (machine_address 0).
Proof.
  intros Code Present Stack PC.
  destruct (Present rax) as (old & Old).
  destruct (Present rflags) as (flags & Flags).
  pose (middle := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state rax (Z_to_bv 64 0) (validation_pc state (entry_pc frame) 421))).
  assert (Clear : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state middle).
  { eapply framed_instruction with (offset := 419) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0)));
      [exact Code|exact Present|exact PC| | |].
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 419 + 2) with (entry_pc frame + 421) by lia.
      apply (execute_xor32_self nondet 0 _ old flags).
      + discriminate.
      + rewrite register_read_frame by discriminate. exact Old.
      + rewrite register_read_frame by discriminate. exact Flags. }
  pose (final := validation_pc middle (entry_pc frame) 428).
  assert (Jump : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 middle final).
  { eapply framed_instruction with (offset := 421) (size := 2)
      (instruction := JMP (Z_to_bv 8 5));
      [validation_code|validation_present|validation_reads; reflexivity| | |].
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 421 + 2) with (entry_pc frame + 423) by lia.
      erewrite execute_jmp8 with (pc := machine_address (entry_pc frame + 423)).
      + change (@sign_extend 8 (Z_to_bv 8 5) 64) with (Z_to_bv 64 5).
        change (@add_vec 64 (machine_address (entry_pc frame + 423)) (Z_to_bv 64 5))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 423)) 5).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 423 + 5) with (entry_pc frame + 428) by lia.
        reflexivity.
      + apply register_read_written. }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); eassumption.
  - split; [reflexivity|]. split; [validation_code|]. split; [validation_present|]. split.
    + apply (call_stack_same_memory layout frame initial state final Stack).
      * validation_reads. reflexivity.
      * validation_reads. reflexivity.
      * reflexivity.
    + split; validation_reads; reflexivity.
Qed.

Print Assumptions done_path.
