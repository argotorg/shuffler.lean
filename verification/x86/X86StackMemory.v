(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Flags X86Instructions X86Data X86Sail
  X86Memory X86MemoryInstructions X86Stack.
Import ListNotations.

Lemma register_write_memory reg value state :
  archState.memory (sst (write_reg_seq_state reg value state)) =
    archState.memory (sst state).
Proof. reflexivity. Qed.

Lemma register_write_written reg value state :
  written (write_reg_seq_state reg value state) = written state.
Proof. reflexivity. Qed.

Lemma register_write_read_memory reg value state size addr :
  read_mem_seq_state size addr (write_reg_seq_state reg value state) =
    read_mem_seq_state size addr state.
Proof. reflexivity. Qed.

Lemma read_rm32_memory_trace nondet addr state (value : bv 32) :
  read_mem_seq_state 4 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rm_operand_without_lock 32 (rm_MEM addr))) state state value.
Proof.
  intro Read. unfold Tiny_x86.read_rm_operand_without_lock, Tiny_x86.read_rm_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  eapply trace_sail_bind; [exact (sail_read_word_trace nondet addr state value Read)|].
  constructor.
Qed.

Lemma read_rm64_memory_trace nondet addr state (value : bv 64) :
  read_mem_seq_state 8 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rm_operand_without_lock 64 (rm_MEM addr))) state state value.
Proof.
  intro Read. unfold Tiny_x86.read_rm_operand_without_lock, Tiny_x86.read_rm_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  eapply trace_sail_bind; [exact (sail_read_doubleword_trace nondet addr state value Read)|].
  constructor.
Qed.

Lemma read_rmi32_memory_trace nondet addr state (value : bv 32) :
  read_mem_seq_state 4 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rmi_operand_without_lock 32 (rmi_MEM addr))) state state value.
Proof.
  intro Read. unfold Tiny_x86.read_rmi_operand_without_lock, Tiny_x86.read_rmi_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  eapply trace_sail_bind; [exact (sail_read_word_trace nondet addr state value Read)|].
  constructor.
Qed.

Lemma read_rmi64_memory_trace nondet addr state (value : bv 64) :
  read_mem_seq_state 8 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_rmi_operand_without_lock 64 (rmi_MEM addr))) state state value.
Proof.
  intro Read. unfold Tiny_x86.read_rmi_operand_without_lock, Tiny_x86.read_rmi_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  eapply trace_sail_bind; [exact (sail_read_doubleword_trace nondet addr state value Read)|].
  constructor.
Qed.

Theorem execute_ret nondet state stack pc return_address :
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state rip state = Some pc ->
  read_mem_seq_state 8 stack state = Some return_address ->
  sail_run nondet (Tiny_x86.execute (RET tt)) state =
    Exec.make [(write_reg_seq_state rsp
      (SailStdpp.Operators_mwords.add_vec_int stack 8)
      (write_reg_seq_state rip return_address state), tt)] [].
Proof.
  intros Stack PC Read. apply execute_ret_from_read with (pc := pc); auto.
  now apply read_rm64_memory_trace.
Qed.

Theorem execute_pop64 nondet destination state stack old value :
  Values.reg (gpr_reference destination) <> rsp ->
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_mem_seq_state 8 stack state = Some value ->
  sail_run nondet (Tiny_x86.execute
    (POP (64, rm_REG (REG_NORMAL destination)))) state =
    Exec.make [(write_reg_seq_state rsp
      (SailStdpp.Operators_mwords.add_vec_int stack 8)
      (write_reg_seq_state (Values.reg (gpr_reference destination))
        (Values.from_ty (gpr_reference destination) value) state), tt)] [].
Proof.
  intros Different Stack Destination Read.
  apply execute_pop64_from_read with (old := old); auto.
  now apply read_rm64_memory_trace.
Qed.

Theorem execute_mov64_load nondet destination address state old value :
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_mem_seq_state 8 address state = Some value ->
  sail_run nondet (Tiny_x86.execute
    (MOV (64, rm_REG (REG_NORMAL destination), rmi_MEM address))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination) value) state, tt)] [].
Proof.
  intros Destination Read. apply execute_mov64_from_read with (old := old); auto.
  now apply read_rmi64_memory_trace.
Qed.

Theorem execute_mov32_load nondet destination address state old value :
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_mem_seq_state 4 address state = Some value ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_REG (REG_NORMAL destination), rmi_MEM address))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination)
        (@SailStdpp.Operators_mwords.zero_extend 32 value 64)) state, tt)] [].
Proof.
  intros Destination Read. apply execute_mov32_from_read with (old := old); auto.
  now apply read_rmi32_memory_trace.
Qed.

Print Assumptions execute_ret.
Print Assumptions execute_pop64.
Print Assumptions execute_mov64_load.
Print Assumptions execute_mov32_load.

Lemma write_rm32_memory_trace nondet addr state (value : bv 32) :
  mem_present addr 4 (archState.memory (sst state)) = true ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_rm_operand_without_lock 32 (rm_MEM addr) value)) state
    (stored_bytes_state state addr (bv_to_bytes 8 value)) tt.
Proof.
  intro Mapped. unfold Tiny_x86.write_rm_operand_without_lock,
    Tiny_x86.write_rm_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  exact (sail_write_word_trace nondet addr state value Mapped).
Qed.

Lemma write_rm64_memory_trace nondet addr state (value : bv 64) :
  mem_present addr 8 (archState.memory (sst state)) = true ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_rm_operand_without_lock 64 (rm_MEM addr) value)) state
    (stored_bytes_state state addr (bv_to_bytes 8 value)) tt.
Proof.
  intro Mapped. unfold Tiny_x86.write_rm_operand_without_lock,
    Tiny_x86.write_rm_operand_with_lock.
  eapply trace_sail_bind; [constructor|].
  exact (sail_write_doubleword_trace nondet addr state value Mapped).
Qed.

Theorem execute_push64 nondet source state stack value :
  read_reg_seq_state rsp state = Some stack ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some value ->
  mem_present (stack_down stack) 8 (archState.memory (sst state)) = true ->
  sail_run nondet (Tiny_x86.execute
    (PUSH (64, rmi_REG (REG_NORMAL source)))) state =
    Exec.make [(stored_bytes_state
      (write_reg_seq_state rsp (stack_down stack) state) (stack_down stack)
      (bv_to_bytes 8 (Values.to_ty (gpr_reference source) value)), tt)] [].
Proof.
  intros Stack Source Mapped. apply execute_push64_to_write with (stack := stack) (value := value); auto.
  apply write_rm64_memory_trace. rewrite register_write_memory. exact Mapped.
Qed.

Theorem execute_mov32_store nondet source address state value :
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some value ->
  mem_present address 4 (archState.memory (sst state)) = true ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_MEM address, rmi_REG (REG_NORMAL source)))) state =
    Exec.make [(stored_bytes_state state address
      (bv_to_bytes 8 (SailStdpp.Operators_mwords.subrange_vec_dec
        (Values.to_ty (gpr_reference source) value) 31 0)), tt)] [].
Proof.
  intros Source Mapped. apply execute_mov32_to_write with (value := value); auto.
  now apply write_rm32_memory_trace.
Qed.

Theorem execute_mov32_immediate_store nondet address state value :
  mem_present address 4 (archState.memory (sst state)) = true ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_MEM address, rmi_IMM (IMM32 value)))) state =
    Exec.make [(stored_bytes_state state address (bv_to_bytes 8 value), tt)] [].
Proof.
  intro Mapped. apply execute_mov32_immediate_to_write.
  now apply write_rm32_memory_trace.
Qed.

Print Assumptions execute_push64.
Print Assumptions execute_mov32_store.
Print Assumptions execute_mov32_immediate_store.
