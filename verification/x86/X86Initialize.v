(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation.
From X86 Require Import X86Layout X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86Decoded
  X86StackMemory X86MemoryStore X86MemoryFrame X86Prologue X86StackFrame.
Import ListNotations.
Open Scope Z_scope.

Definition zero_sites : list (Z * Z * nat) := [(14, 7, 0%nat); (21, 8, 1%nat); (29, 8, 2%nat)].

Lemma zero_site_decodes nondet pc (registers : register_values) layout output offset size index :
  In (offset, size, index) zero_sites ->
  registers r10 = pointer_to_block layout output ->
  In (offset, size) program_instructions /\ (index < 3)%nat /\
  decoded_instruction nondet pc registers offset =
    Some (MOV (32, rm_MEM (machine_address (cell_address (cell_layout layout) output index)),
      rmi_IMM (IMM32 (machine_word Int.zero)))).
Proof.
  intros At Pointer.
  destruct At as [At|[At|[At|No]]]; [inversion At; subst|inversion At; subst|inversion At; subst|contradiction].
  all: split; [unfold program_instructions; simpl; tauto|split; [lia|]].
  - rewrite decode_output_zero, Pointer. unfold pointer_to_block, cell_address.
    replace (block_address (cell_layout layout) output + 4 * Z.of_nat 0) with
      (block_address (cell_layout layout) output) by lia. reflexivity.
  - rewrite (decode_output_fields nondet pc registers 21 4 ltac:(left; reflexivity)), Pointer.
    unfold pointer_to_block. rewrite machine_address_next. reflexivity.
  - rewrite (decode_output_fields nondet pc registers 29 8 ltac:(right; left; reflexivity)), Pointer.
    unfold pointer_to_block. rewrite machine_address_next. reflexivity.
Qed.

Definition zero_state layout (frame : call_frame layout program_bytes)
    offset size index output state : seq_state :=
  stored_bytes_state (advance state (entry_pc frame) (offset + size))
    (machine_address (cell_address (cell_layout layout) output index))
    (bv_to_bytes 8 (machine_word Int.zero)).

Theorem zero_output_step nondet layout (frame : call_frame layout program_bytes)
    state output offset size index :
  In (offset, size, index) zero_sites ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  mem_present (machine_address (cell_address (cell_layout layout) output index)) 4
    (archState.memory (sst state)) = true ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (zero_state layout frame offset size index output state).
Proof.
  intros At Code Registers PC Pointer Mapped.
  destruct (zero_site_decodes nondet (machine_address (entry_pc frame + offset))
    (register_values_of state) layout output offset size index At
    (register_value_known state r10 _ Pointer)) as [Instruction [Index Decode]].
  eapply framed_instruction; [exact Code|exact Registers|exact PC|exact Instruction|exact Decode|].
  rewrite machine_address_next.
  unfold zero_state, advance.
  replace (entry_pc frame + (offset + size)) with (entry_pc frame + offset + size) by lia.
  apply execute_mov32_immediate_store. rewrite register_write_memory. exact Mapped.
Qed.

Lemma zero_code layout (frame : call_frame layout program_bytes) state output offset size index :
  (index < block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes ->
  code_at (zero_state layout frame offset size index output state) (entry_pc frame) program_bytes.
Proof. intros Index Code. apply code_preserved_cell_store; [apply code_at_register_write, Code|exact Index]. Qed.

Lemma zero_registers layout (frame : call_frame layout program_bytes) state output offset size index :
  registers_present state -> registers_present (zero_state layout frame offset size index output state).
Proof. intro Present. apply registers_present_store, registers_present_write, Present. Qed.

Lemma zero_related layout (frame : call_frame layout program_bytes) c c' state output offset size index :
  machine_cells_related layout c (archState.memory (sst state)) ->
  (index < block_words (cell_layout layout) output)%nat ->
  Mem.store Mint32 c output (4 * Z.of_nat index) (Vint Int.zero) = Some c' ->
  machine_cells_related layout c'
    (archState.memory (sst (zero_state layout frame offset size index output state))).
Proof.
  intros Related Index Store. unfold zero_state, advance. rewrite stored_bytes_memory, register_write_memory.
  apply (machine_cells_related_store layout c _ output index Int.zero c'); assumption.
Qed.

Print Assumptions zero_output_step.
Print Assumptions zero_related.

Definition initialized_state layout (frame : call_frame layout program_bytes) output state : seq_state :=
  zero_state layout frame 29 8 2 output
    (zero_state layout frame 21 8 1 output (zero_state layout frame 14 7 0 output state)).

Ltac zero_read :=
  unfold zero_state, advance;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Theorem initialize_steps nondet layout (frame : call_frame layout program_bytes)
    output c c1 c2 c3 state :
  (3 <= block_words (cell_layout layout) output)%nat ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c output 0 (Vint Int.zero) = Some c1 ->
  Mem.store Mint32 c1 output 4 (Vint Int.zero) = Some c2 ->
  Mem.store Mint32 c2 output 8 (Vint Int.zero) = Some c3 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 14)) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 3 state
    (initialized_state layout frame output state) /\
  machine_cells_related layout c3
    (archState.memory (sst (initialized_state layout frame output state))).
Proof.
  intros Capacity Related W0 W1 W2 Code Present PC Pointer.
  pose (s1 := zero_state layout frame 14 7 0 output state).
  pose (s2 := zero_state layout frame 21 8 1 output s1).
  assert (R1 : machine_cells_related layout c1 (archState.memory (sst s1))).
  { apply zero_related with (c := c); [exact Related|lia|exact W0]. }
  assert (R2 : machine_cells_related layout c2 (archState.memory (sst s2))).
  { apply zero_related with (c := c1); [exact R1|lia|exact W1]. }
  split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat) (middle := s1).
    + apply zero_output_step; try assumption.
      * left. reflexivity.
      * exact (proj1 (Related output 0%nat ltac:(lia))).
    + eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat) (middle := s2).
      * apply (zero_output_step nondet layout frame s1 output 21 8 1).
        -- right. left. reflexivity.
        -- apply zero_code; [lia|exact Code].
        -- apply zero_registers, Present.
        -- unfold s1. zero_read. reflexivity.
        -- unfold s1. zero_read. exact Pointer.
        -- exact (proj1 (R1 output 1%nat ltac:(lia))).
      * apply (zero_output_step nondet layout frame s2 output 29 8 2).
        -- right. right. left. reflexivity.
        -- apply zero_code; [lia|apply zero_code; [lia|exact Code]].
        -- do 2 apply zero_registers. exact Present.
        -- unfold s2, s1. zero_read. reflexivity.
        -- unfold s2, s1. zero_read. exact Pointer.
        -- exact (proj1 (R2 output 2%nat ltac:(lia))).
  - apply (zero_related layout frame c2 c3 s2 output 29 8 2); [exact R2|lia|exact W2].
Qed.

Lemma initialized_code layout (frame : call_frame layout program_bytes) output state :
  (3 <= block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes ->
  code_at (initialized_state layout frame output state) (entry_pc frame) program_bytes.
Proof.
  intros Capacity Code. unfold initialized_state.
  do 3 (apply zero_code; [lia|]). exact Code.
Qed.

Lemma initialized_registers layout (frame : call_frame layout program_bytes) output state :
  registers_present state -> registers_present (initialized_state layout frame output state).
Proof. intro Present. unfold initialized_state. do 3 apply zero_registers. exact Present. Qed.

Lemma initialized_pc layout (frame : call_frame layout program_bytes) output state :
  read_reg_seq_state rip (initialized_state layout frame output state) =
    Some (machine_address (entry_pc frame + 37)).
Proof. unfold initialized_state. zero_read. reflexivity. Qed.

Lemma initialized_other layout (frame : call_frame layout program_bytes) output state reg :
  reg <> rip -> read_reg_seq_state reg (initialized_state layout frame output state) =
    read_reg_seq_state reg state.
Proof.
  intro Different. unfold initialized_state, zero_state, advance.
  repeat first [rewrite stored_register_read | rewrite register_read_frame by congruence]. reflexivity.
Qed.

Lemma initialized_stack_read layout (frame : call_frame layout program_bytes) output state stack :
  (3 <= block_words (cell_layout layout) output)%nat ->
  entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
  read_mem_seq_state 8 (machine_address stack) (initialized_state layout frame output state) =
    read_mem_seq_state 8 (machine_address stack) state.
Proof.
  intros Capacity Low High. unfold initialized_state, zero_state, advance.
  do 3 (rewrite (stack_read_cell_store layout program_bytes frame) by lia;
    rewrite register_write_read_memory).
  reflexivity.
Qed.

Print Assumptions initialize_steps.
