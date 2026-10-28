(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Program X86Execution
  X86Instructions X86StackMemory X86MemoryStore X86StackLayout X86StackFrame X86Prologue.
Open Scope Z_scope.

Lemma saved_word_here layout (frame : call_frame layout program_bytes)
    offset size slot value state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 8 * Z.of_nat (S slot)))
    (saved_state layout frame offset size slot value state) = Some value.
Proof. apply stored_doubleword_read. Qed.

Lemma saved_word_elsewhere layout (frame : call_frame layout program_bytes)
    offset size slot value state stack :
  (slot < 5)%nat ->
  entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
  entry_sp frame - 8 * Z.of_nat (S slot) + 8 <= stack \/
    stack + 8 <= entry_sp frame - 8 * Z.of_nat (S slot) ->
  read_mem_seq_state 8 (machine_address stack)
    (saved_state layout frame offset size slot value state) =
    read_mem_seq_state 8 (machine_address stack) state.
Proof.
  intros Slot Low High Different. unfold saved_state.
  rewrite (stack_read_stack_store layout program_bytes frame); try assumption; try lia.
  reflexivity.
Qed.

Lemma saved_cells_related layout (frame : call_frame layout program_bytes)
    offset size slot value state c :
  (slot < 5)%nat -> machine_cells_related layout c (archState.memory (sst state)) ->
  machine_cells_related layout c
    (archState.memory (sst (saved_state layout frame offset size slot value state))).
Proof.
  intros Slot Related. unfold saved_state.
  apply (machine_cells_related_stack_store layout program_bytes frame); try lia.
  exact Related.
Qed.

Lemma saves_cells_related layout (frame : call_frame layout program_bytes) state c :
  machine_cells_related layout c (archState.memory (sst state)) ->
  machine_cells_related layout c (archState.memory (sst (saves_state layout frame state))).
Proof.
  intro Related. unfold saves_state.
  do 5 (apply saved_cells_related; [lia|]). exact Related.
Qed.

Lemma saves_read15 layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 40))
    (saves_state layout frame state) = Some (register_values_of state r15).
Proof. unfold saves_state. apply saved_word_here. Qed.

Lemma saves_read14 layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 32))
    (saves_state layout frame state) = Some (register_values_of state r14).
Proof.
  unfold saves_state. rewrite saved_word_elsewhere by lia. apply saved_word_here.
Qed.

Lemma saves_read13 layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 24))
    (saves_state layout frame state) = Some (register_values_of state r13).
Proof.
  unfold saves_state. do 2 (rewrite saved_word_elsewhere by lia). apply saved_word_here.
Qed.

Lemma saves_read12 layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 16))
    (saves_state layout frame state) = Some (register_values_of state r12).
Proof.
  unfold saves_state. do 3 (rewrite saved_word_elsewhere by lia). apply saved_word_here.
Qed.

Lemma saves_read_bx layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame - 8))
    (saves_state layout frame state) = Some (register_values_of state rbx).
Proof.
  unfold saves_state. do 4 (rewrite saved_word_elsewhere by lia). apply saved_word_here.
Qed.

Lemma saves_read_return layout (frame : call_frame layout program_bytes) state :
  read_mem_seq_state 8 (machine_address (entry_sp frame)) (saves_state layout frame state) =
    read_mem_seq_state 8 (machine_address (entry_sp frame)) state.
Proof.
  unfold saves_state. do 5 (rewrite saved_word_elsewhere by lia). reflexivity.
Qed.

Lemma output_pointer_register_value layout (frame : call_frame layout program_bytes)
    output state reg :
  reg <> rip -> reg <> r10 ->
  register_values_of (output_pointer_state layout frame output state) reg =
    register_values_of state reg.
Proof.
  intros NotPC NotOutput. unfold register_values_of, output_pointer_state, advance.
  rewrite !register_read_frame by congruence. reflexivity.
Qed.

Theorem prologue_saved_reads layout (frame : call_frame layout program_bytes) output state :
  let final := prologue_state layout frame output state in
  read_mem_seq_state 8 (machine_address (entry_sp frame - 40)) final =
      Some (register_values_of state r15) /\
  read_mem_seq_state 8 (machine_address (entry_sp frame - 32)) final =
      Some (register_values_of state r14) /\
  read_mem_seq_state 8 (machine_address (entry_sp frame - 24)) final =
      Some (register_values_of state r13) /\
  read_mem_seq_state 8 (machine_address (entry_sp frame - 16)) final =
      Some (register_values_of state r12) /\
  read_mem_seq_state 8 (machine_address (entry_sp frame - 8)) final =
      Some (register_values_of state rbx) /\
  read_mem_seq_state 8 (machine_address (entry_sp frame)) final =
      read_mem_seq_state 8 (machine_address (entry_sp frame)) state.
Proof.
  unfold prologue_state. cbn zeta. repeat split.
  - rewrite saves_read15, output_pointer_register_value by discriminate. reflexivity.
  - rewrite saves_read14, output_pointer_register_value by discriminate. reflexivity.
  - rewrite saves_read13, output_pointer_register_value by discriminate. reflexivity.
  - rewrite saves_read12, output_pointer_register_value by discriminate. reflexivity.
  - rewrite saves_read_bx, output_pointer_register_value by discriminate. reflexivity.
  - rewrite saves_read_return. reflexivity.
Qed.

Theorem prologue_cells_related layout (frame : call_frame layout program_bytes) output state c :
  machine_cells_related layout c (archState.memory (sst state)) ->
  machine_cells_related layout c
    (archState.memory (sst (prologue_state layout frame output state))).
Proof. intro Related. apply saves_cells_related. exact Related. Qed.

Print Assumptions prologue_saved_reads.
Print Assumptions prologue_cells_related.
