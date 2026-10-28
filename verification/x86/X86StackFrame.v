(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86MemoryStore X86ABI X86MemoryFrame X86StackLayout.
Open Scope Z_scope.

Lemma memory_store_read_frame addr contents other size machine :
  (forall i j, (i < length contents)%nat -> (j < N.to_nat size)%nat ->
    addr_addN addr (N.of_nat i) <> addr_addN other (N.of_nat j)) ->
  mem_lookup other size (mem_insert_bytes addr contents machine) = mem_lookup other size machine.
Proof.
  intro Frame. apply mem_lookup_frame. intros location At.
  unfold addr_range, seqN in At.
  apply in_map_iff in At as [n [Address At]].
  apply in_map_iff in At as [j [Number At]].
  apply in_seq in At. cbn in At. subst n location.
  apply mem_insert_bytes_frame. intros i I. apply Frame; lia.
Qed.

Lemma stack_cell_disjoint layout code (frame : call_frame layout code) stack b k i :
  entry_sp frame - 40 <= stack < entry_sp frame + 16 ->
  (k < block_words (cell_layout layout) b)%nat -> (i < 4)%nat ->
  machine_address stack <>
    addr_addN (machine_address (cell_address (cell_layout layout) b k)) (N.of_nat i).
Proof.
  intros Stack K I. rewrite machine_address_offset. intro Equal.
  pose proof (frame_stack_bounds layout code frame) as StackBounds.
  pose proof (cell_byte_range layout b k (Z.of_nat i) K ltac:(lia)) as CellRange.
  pose proof (frame_buffers_stack layout code frame b ltac:(lia)) as Separate.
  apply (f_equal bv_unsigned) in Equal. unfold machine_address in Equal.
  rewrite !Z_to_bv_small in Equal by
    (change (bv_modulus 64) with address_modulus; lia).
  unfold cell_address in Equal, CellRange. lia.
Qed.

Theorem machine_cells_related_stack_store layout code (frame : call_frame layout code)
    c state stack (value : bv 64) :
  machine_cells_related layout c (archState.memory (sst state)) ->
  entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
  machine_cells_related layout c
    (archState.memory (sst (stored_bytes_state state (machine_address stack) (bv_to_bytes 8 value)))).
Proof.
  intros Related Low High. rewrite stored_bytes_memory.
  intros b k K. destruct (Related b k K) as [Mapped Read]. split.
  - eapply mem_present_mapping; [apply memory_insert_bytes_mapping|exact Mapped].
  - intros x Load. unfold machine_word_at. rewrite memory_store_read_frame.
    + apply Read, Load.
    + intros i j I J. rewrite length_bv_to_bytes in I.
      change (i < 8)%nat in I. change (j < 4)%nat in J.
      rewrite machine_address_offset.
      apply (stack_cell_disjoint layout code frame (stack + Z.of_nat i) b k j); try assumption; lia.
Qed.

Lemma stack_read_cell_store layout code (frame : call_frame layout code)
    state b k value stack :
  (k < block_words (cell_layout layout) b)%nat ->
  entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
  read_mem_seq_state 8 (machine_address stack)
    (stored_bytes_state state (machine_address (cell_address (cell_layout layout) b k))
      (bv_to_bytes 8 (machine_word value))) =
    read_mem_seq_state 8 (machine_address stack) state.
Proof.
  intros K Low High. rewrite !read_mem_is_lookup, stored_bytes_memory.
  apply memory_store_read_frame. intros i j I J.
  rewrite length_bv_to_bytes in I. change (i < 4)%nat in I. change (j < 8)%nat in J.
  rewrite (machine_address_offset stack j). intro Equal.
  exact (stack_cell_disjoint layout code frame (stack + Z.of_nat j) b k i
    ltac:(lia) K I (eq_sym Equal)).
Qed.

Print Assumptions memory_store_read_frame.
Print Assumptions machine_cells_related_stack_store.
Print Assumptions stack_read_cell_store.

Lemma stack_read_stack_store layout code (frame : call_frame layout code)
    state write_stack read_stack (value : bv 64) :
  entry_sp frame - 40 <= write_stack -> write_stack + 8 <= entry_sp frame + 16 ->
  entry_sp frame - 40 <= read_stack -> read_stack + 8 <= entry_sp frame + 16 ->
  write_stack + 8 <= read_stack \/ read_stack + 8 <= write_stack ->
  read_mem_seq_state 8 (machine_address read_stack)
    (stored_bytes_state state (machine_address write_stack) (bv_to_bytes 8 value)) =
    read_mem_seq_state 8 (machine_address read_stack) state.
Proof.
  intros WriteLow WriteHigh ReadLow ReadHigh Separate.
  rewrite !read_mem_is_lookup, stored_bytes_memory.
  apply memory_store_read_frame. intros i j I J.
  rewrite length_bv_to_bytes in I. change (i < 8)%nat in I. change (j < 8)%nat in J.
  rewrite !machine_address_offset. intro Equal.
  pose proof (frame_stack_bounds layout code frame) as Bounds.
  apply (f_equal bv_unsigned) in Equal. unfold machine_address in Equal.
  rewrite !Z_to_bv_small in Equal by
    (change (bv_modulus 64) with address_modulus; lia).
  lia.
Qed.

Lemma stored_doubleword_read state addr (value : bv 64) :
  read_mem_seq_state 8 addr (stored_bytes_state state addr (bv_to_bytes 8 value)) = Some value.
Proof.
  rewrite read_mem_is_lookup, stored_bytes_memory. apply read_insert_doubleword.
Qed.

Print Assumptions stack_read_stack_store.
Print Assumptions stored_doubleword_read.
