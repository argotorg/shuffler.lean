(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Flags X86Instructions X86Data X86Sail.
Import ListNotations.

Lemma execute_ret_from_read nondet state stack pc return_address :
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state rip state = Some pc ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rm_operand_without_lock 64 (rm_MEM stack)))
    state state return_address ->
  sail_run nondet (Tiny_x86.execute (RET tt)) state =
    Exec.make [(write_reg_seq_state rsp
      (SailStdpp.Operators_mwords.add_vec_int stack 8)
      (write_reg_seq_state rip return_address state), tt)] [].
Proof.
  intros Stack PC Read.
  unfold Tiny_x86.execute, Tiny_x86.execute_RET, Tiny_x86_types.Defs.bind0.
  repeat rewrite sail_bind_assoc.
  erewrite sail_run_bind by exact (@sail_read_reg_trace nondet rsp state stack Stack).
  erewrite sail_run_bind by exact Read.
  repeat rewrite sail_bind_assoc.
  erewrite sail_run_bind by exact (@sail_write_reg_trace nondet rip state pc return_address PC).
  assert (Stack' : read_reg_seq_state rsp
    (write_reg_seq_state rip return_address state) = Some stack).
  { rewrite register_read_frame by discriminate. exact Stack. }
  erewrite sail_run_bind by exact (@sail_read_reg_trace nondet rsp _ stack Stack').
  apply sail_trace_run with (nondet := nondet).
  exact (@sail_write_reg_trace nondet rsp _ stack _ Stack').
Qed.

Lemma execute_mov64_from_read nondet destination address state old value :
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rmi_operand_without_lock 64 (rmi_MEM address)))
    state state value ->
  sail_run nondet (Tiny_x86.execute
    (MOV (64, rm_REG (REG_NORMAL destination), rmi_MEM address))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination) value) state, tt)] [].
Proof.
  intros Destination Read.
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind
    Tiny_x86.write_rm_operand_without_lock Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  erewrite sail_run_bind by exact Read.
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  now apply write_gpr64_trace with (old := old).
Qed.

Lemma execute_mov32_from_read nondet destination address state old value :
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rmi_operand_without_lock 32 (rmi_MEM address)))
    state state value ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_REG (REG_NORMAL destination), rmi_MEM address))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination)
        (SailStdpp.Operators_mwords.zero_extend value 64)) state, tt)] [].
Proof.
  intros Destination Read.
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind
    Tiny_x86.write_rm_operand_without_lock Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  erewrite sail_run_bind by exact Read.
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  now apply write_gpr32_trace_single with (old := old).
Qed.

Lemma execute_pop64_from_read nondet destination state stack old value :
  Values.reg (gpr_reference destination) <> rsp ->
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rm_operand_without_lock 64 (rm_MEM stack)))
    state state value ->
  sail_run nondet (Tiny_x86.execute
    (POP (64, rm_REG (REG_NORMAL destination)))) state =
    Exec.make [(write_reg_seq_state rsp
      (SailStdpp.Operators_mwords.add_vec_int stack 8)
      (write_reg_seq_state (Values.reg (gpr_reference destination))
        (Values.from_ty (gpr_reference destination) value) state), tt)] [].
Proof.
  intros Different Stack Destination Read.
  assert (Stack' : read_reg_seq_state rsp
    (write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination) value) state) = Some stack).
  { rewrite register_read_frame by exact Different. exact Stack. }
  apply sail_trace_run with (nondet := nondet).
  unfold Tiny_x86.execute, Tiny_x86.execute_POP.
  eapply trace_sail_bind.
  - exact (@sail_read_reg_trace nondet rsp state stack Stack).
  - eapply trace_sail_bind.
    + exact Read.
    + eapply trace_sail_bind.
      * eapply trace_sail_bind.
        -- exact (write_gpr64_trace nondet destination state old value Destination).
        -- exact (@sail_read_reg_trace nondet rsp _ stack Stack').
      * exact (@sail_write_reg_trace nondet rsp _ stack _ Stack').
Qed.

Definition stack_down (stack : bv 64) : bv 64 :=
  @SailStdpp.Operators_mwords.sub_vec 64 stack (Z_to_bv 64 8).

Lemma execute_push64_to_write nondet source state stack value final :
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_rm_operand_without_lock 64 (rm_MEM (stack_down stack))
      (Values.to_ty (gpr_reference source) value)))
    (write_reg_seq_state rsp (stack_down stack) state) final tt ->
  sail_run nondet (Tiny_x86.execute
    (PUSH (64, rmi_REG (REG_NORMAL source)))) state = Exec.make [(final, tt)] [].
Proof.
  intros Stack Source Write.
  apply sail_trace_run with (nondet := nondet).
  unfold Tiny_x86.execute, Tiny_x86.execute_PUSH.
  eapply trace_sail_bind.
  - exact (read_gpr64_trace nondet source state value Source).
  - rewrite sign_extend64. eapply trace_sail_bind.
    + exact (@sail_read_reg_trace nondet rsp state stack Stack).
    + eapply trace_sail_bind.
      * eapply trace_sail_bind.
        -- exact (@sail_write_reg_trace nondet rsp state stack (stack_down stack) Stack).
        -- exact (@sail_read_reg_trace nondet rsp _ (stack_down stack)
             (register_read_written rsp (stack_down stack) state)).
      * exact Write.
Qed.

Lemma execute_mov32_to_write nondet source address state value final :
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_rm_operand_without_lock 32 (rm_MEM address)
      (SailStdpp.Operators_mwords.subrange_vec_dec
        (Values.to_ty (gpr_reference source) value) 31 0))) state final tt ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_MEM address, rmi_REG (REG_NORMAL source)))) state =
    Exec.make [(final, tt)] [].
Proof.
  intros Source Write. apply sail_trace_run with (nondet := nondet).
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  eapply trace_sail_bind.
  - exact (read_gpr32_trace nondet source state value Source).
  - exact Write.
Qed.

Lemma read_immediate32_trace nondet state value :
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_imm 32 (IMM32 value))) state state value.
Proof.
  change (sail_trace nondet (FMon.Ret
    (SailStdpp.Operators_mwords.sign_extend value 32)) state state value).
  rewrite sign_extend32. constructor.
Qed.

Lemma execute_mov32_immediate_to_write nondet address state value final :
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_rm_operand_without_lock 32 (rm_MEM address) value)) state final tt ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_MEM address, rmi_IMM (IMM32 value)))) state =
    Exec.make [(final, tt)] [].
Proof.
  intro Write. apply sail_trace_run with (nondet := nondet).
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  eapply trace_sail_bind.
  - apply read_immediate32_trace.
  - exact Write.
Qed.

Print Assumptions execute_ret_from_read.
Print Assumptions execute_pop64_from_read.
Print Assumptions execute_push64_to_write.
Print Assumptions execute_mov32_immediate_to_write.
