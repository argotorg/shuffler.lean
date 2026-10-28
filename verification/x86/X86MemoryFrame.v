(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86MemoryStore X86ABI.
Open Scope Z_scope.

Lemma stored_bytes_unwritten contents addr state other :
  other ∉ written state ->
  (forall i, (i < List.length contents)%nat ->
    addr_addN addr (N.of_nat i) <> other) ->
  other ∉ written (stored_bytes_state state addr contents).
Proof.
  revert addr state. induction contents as [|byte rest IH]; intros addr state Clean Frame.
  - exact Clean.
  - cbn [stored_bytes_state]. apply IH.
    + change (other ∉ written state ∪ {[addr]}).
      specialize (Frame 0%nat ltac:(cbn; lia)). rewrite addr_addN_zero in Frame.
      set_solver.
    + intros i I. change (addr_addN (addr_addN addr 1) (N.of_nat i) <> other).
      rewrite addr_addN_assoc.
      replace (1 + N.of_nat i)%N with (N.of_nat (S i)) by lia.
      apply Frame. cbn. lia.
Qed.

Lemma code_preserved_store state base code addr contents :
  code_at state base code ->
  (forall index byte, nth_error code index = Some byte ->
    forall i, (i < List.length contents)%nat ->
      addr_addN addr (N.of_nat i) <> machine_address (base + Z.of_nat index)) ->
  code_at (stored_bytes_state state addr contents) base code.
Proof.
  intros Code Disjoint index byte Byte. destruct (Code index byte Byte) as [Read Clean].
  split.
  - unfold read_byte_seq_state. rewrite stored_bytes_memory, mem_insert_bytes_frame.
    + exact Read.
    + exact (Disjoint index byte Byte).
  - apply stored_bytes_unwritten; [exact Clean|exact (Disjoint index byte Byte)].
Qed.

Lemma frame_cell_code_disjoint layout code (frame : call_frame layout code)
    b k index byte i :
  (k < block_words (cell_layout layout) b)%nat ->
  nth_error code index = Some byte -> (i < 4)%nat ->
  addr_addN (machine_address (cell_address (cell_layout layout) b k)) (N.of_nat i) <>
    machine_address (entry_pc frame + Z.of_nat index).
Proof.
  intros K Byte I. rewrite machine_address_offset. intro Equal.
  assert (Index : (index < List.length code)%nat).
  { apply nth_error_Some. rewrite Byte. discriminate. }
  pose proof (cell_byte_range layout b k (Z.of_nat i) K ltac:(lia)) as CellRange.
  destruct (frame_code_bounds layout code frame) as [CodeLow CodeHigh].
  pose proof (frame_buffers_code layout code frame b ltac:(lia)) as Separate.
  apply (f_equal bv_unsigned) in Equal. unfold machine_address in Equal.
  rewrite !Z_to_bv_small in Equal by
    (change (bv_modulus 64) with address_modulus; lia).
  unfold cell_address in Equal, CellRange. lia.
Qed.

Theorem code_preserved_cell_store layout code (frame : call_frame layout code)
    state b k value :
  code_at state (entry_pc frame) code ->
  (k < block_words (cell_layout layout) b)%nat ->
  code_at
    (stored_bytes_state state
      (machine_address (cell_address (cell_layout layout) b k))
      (bv_to_bytes 8 (machine_word value))) (entry_pc frame) code.
Proof.
  intros Code K. apply code_preserved_store; [exact Code|].
  intros index byte Byte i I.
  rewrite length_bv_to_bytes in I. change (i < 4)%nat in I.
  apply (frame_cell_code_disjoint layout code frame b k index byte i); assumption.
Qed.

Print Assumptions stored_bytes_unwritten.
Print Assumptions code_preserved_store.
Print Assumptions code_preserved_cell_store.
