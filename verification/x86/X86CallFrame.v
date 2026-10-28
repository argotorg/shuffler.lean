(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From compcert Require Import AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Program X86Execution
  X86Instructions X86Control X86StackMemory X86Prologue X86MemoryStore
  X86MemoryFrame X86StackFrame X86Call.
Open Scope Z_scope.

Lemma call_stack_register_write layout (frame : call_frame layout program_bytes)
    initial state (reg : Arch.reg) value :
  call_stack layout frame initial state -> reg <> rsp -> reg <> rbp ->
  call_stack layout frame initial (write_reg_seq_state reg value state).
Proof.
  intros Stack NotSP NotBP.
  apply (call_stack_same_memory layout frame initial state _ Stack).
  - apply register_read_frame, NotSP.
  - apply register_read_frame, NotBP.
  - apply register_write_memory.
Qed.

Lemma call_stack_cell_store layout (frame : call_frame layout program_bytes)
    initial state b k value :
  call_stack layout frame initial state ->
  (k < block_words (cell_layout layout) b)%nat ->
  call_stack layout frame initial
    (stored_bytes_state state (machine_address (cell_address (cell_layout layout) b k))
      (bv_to_bytes 8 (machine_word value))).
Proof.
  intros Stack Index.
  apply (call_stack_preserved layout frame initial state _ Stack).
  - apply stored_register_read.
  - apply stored_register_read.
  - intros stack Low High.
    exact (stack_read_cell_store layout program_bytes frame state b k value stack Index Low High).
Qed.

Theorem cell_store_frame layout (frame : call_frame layout program_bytes)
    initial state c c' b k value :
  machine_cells_related layout c (archState.memory (sst state)) ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  (k < block_words (cell_layout layout) b)%nat ->
  Mem.store Mint32 c b (4 * Z.of_nat k) (Vint value) = Some c' ->
  let final := stored_bytes_state state
    (machine_address (cell_address (cell_layout layout) b k))
    (bv_to_bytes 8 (machine_word value)) in
  machine_cells_related layout c' (archState.memory (sst final)) /\
  code_at final (entry_pc frame) program_bytes /\ registers_present final /\
  call_stack layout frame initial final.
Proof.
  intros Related Code Present Stack Index Store final.
  split.
  - unfold final. rewrite stored_bytes_memory.
    exact (machine_cells_related_store layout c (archState.memory (sst state))
      b k value c' Related Index Store).
  - split.
    + exact (code_preserved_cell_store layout program_bytes frame state b k value Code Index).
    + split; [apply registers_present_store, Present|].
      exact (call_stack_cell_store layout frame initial state b k value Stack Index).
Qed.

Print Assumptions call_stack_register_write.
Print Assumptions call_stack_cell_store.
Print Assumptions cell_store_frame.
