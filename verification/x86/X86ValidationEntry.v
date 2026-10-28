(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86Address X86Compare X86Alu X86StackMemory
  X86Call X86CallFrame X86Arguments X86ValidationSteps.
Import ListNotations.
Open Scope Z_scope.

Theorem validation_preheader nondet layout (frame : call_frame layout program_bytes)
    initial state size bd bp bt bu trace output :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 87)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 89)) /\
    read_reg_seq_state rax final = Some (machine_address 0).
Proof.
  intros Code Present Arguments Stack PC.
  destruct (Present rax) as [old Old]. destruct (Present rflags) as [flags Flags].
  pose (final := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state rax (machine_address 0) (validation_pc state (entry_pc frame) 89))).
  exists final. split.
  - eapply framed_instruction with (offset := 87) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0)));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 87 + 2) with (entry_pc frame + 89) by lia.
      apply (execute_xor32_self nondet 0 _ old flags).
      * discriminate.
      * change (read_reg_seq_state rax
          (write_reg_seq_state rip (machine_address (entry_pc frame + 89)) state) = Some old).
        rewrite register_read_frame by discriminate. exact Old.
      * rewrite register_read_frame by discriminate. exact Flags.
  - split.
    + unfold final, validation_pc. rewrite !register_write_memory. reflexivity.
    + split.
      * unfold final, validation_pc. do 3 apply code_at_register_write. exact Code.
      * split.
        -- unfold final, validation_pc. do 3 apply registers_present_write. exact Present.
        -- split.
           ++ unfold final, validation_pc.
              do 3 (apply core_arguments_write; [cbn; intuition discriminate|]). exact Arguments.
           ++ split.
              ** unfold final, validation_pc.
                 do 3 (apply call_stack_register_write; [|discriminate|discriminate]). exact Stack.
              ** split; unfold final, validation_pc;
                   repeat first [rewrite register_read_written |
                     rewrite register_read_frame by discriminate]; reflexivity.
Qed.

Print Assumptions validation_preheader.
