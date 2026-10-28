(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86MemoryStore X86ABI X86MemoryFrame.
Open Scope Z_scope.

Lemma mem_present_nat_prefix count prefix addr machine :
  (prefix <= count)%nat ->
  mem_present_nat addr count machine = true ->
  mem_present_nat addr prefix machine = true.
Proof.
  revert prefix addr. induction count as [|count IH]; intros [|prefix] addr Bound Present;
    try reflexivity; try lia.
  cbn [mem_present_nat] in Present |- *.
  apply andb_true_iff in Present as [Head Tail]. apply andb_true_iff.
  split; [exact Head|]. eapply IH; [lia|exact Tail].
Qed.

Lemma mem_present_nat_suffix offset count addr machine :
  mem_present_nat addr (offset + count) machine = true ->
  mem_present_nat (addr_addN addr (N.of_nat offset)) count machine = true.
Proof.
  revert addr. induction offset as [|offset IH]; intros addr Present.
  - rewrite addr_addN_zero. exact Present.
  - cbn [Nat.add mem_present_nat] in Present.
    apply andb_true_iff in Present as [_ Tail].
    specialize (IH (bv_succ addr) Tail).
    replace (addr_addN addr (N.of_nat (S offset))) with
      (addr_addN (bv_succ addr) (N.of_nat offset)); [exact IH|].
    change (addr_addN (addr_addN addr 1) (N.of_nat offset) =
      addr_addN addr (N.of_nat (S offset))).
    rewrite addr_addN_assoc. f_equal. lia.
Qed.

Lemma mem_present_subrange addr whole offset count machine :
  (offset + count <= N.to_nat whole)%nat ->
  mem_present addr whole machine = true ->
  mem_present (addr_addN addr (N.of_nat offset)) (N.of_nat count) machine = true.
Proof.
  intros Bound Present. unfold mem_present in Present |- *.
  rewrite Nat2N.id. apply mem_present_nat_suffix.
  eapply mem_present_nat_prefix; eassumption.
Qed.

Lemma save_slot_mapped layout code (frame : call_frame layout code) machine slot :
  (slot < 5)%nat ->
  mem_present (machine_address (entry_sp frame - 40)) 40 machine = true ->
  mem_present (machine_address (entry_sp frame - 8 * Z.of_nat (S slot))) 8 machine = true.
Proof.
  intros Slot Present.
  pose proof (mem_present_subrange
    (machine_address (entry_sp frame - 40)) 40 (8 * (4 - slot)) 8 machine
      ltac:(lia) Present) as Mapped.
  rewrite machine_address_offset in Mapped.
  replace (entry_sp frame - 40 + Z.of_nat (8 * (4 - slot))) with
    (entry_sp frame - 8 * Z.of_nat (S slot)) in Mapped by lia.
  exact Mapped.
Qed.

Lemma stack_byte_code_disjoint layout code (frame : call_frame layout code)
    stack index byte :
  entry_sp frame - 40 <= stack < entry_sp frame + 16 ->
  nth_error code index = Some byte ->
  machine_address stack <> machine_address (entry_pc frame + Z.of_nat index).
Proof.
  intros Stack Byte Equal.
  assert (Index : (index < List.length code)%nat).
  { apply nth_error_Some. rewrite Byte. discriminate. }
  pose proof (frame_stack_bounds layout code frame) as StackBounds.
  pose proof (frame_code_bounds layout code frame) as CodeBounds.
  pose proof (frame_code_stack layout code frame) as Separate.
  apply (f_equal bv_unsigned) in Equal. unfold machine_address in Equal.
  rewrite !Z_to_bv_small in Equal by
    (change (bv_modulus 64) with address_modulus; lia).
  lia.
Qed.

Theorem code_preserved_stack_store layout code (frame : call_frame layout code)
    state slot (value : bv 64) :
  code_at state (entry_pc frame) code -> (slot < 5)%nat ->
  code_at
    (stored_bytes_state state (machine_address (entry_sp frame - 8 * Z.of_nat (S slot)))
      (bv_to_bytes 8 value)) (entry_pc frame) code.
Proof.
  intros Code Slot. apply code_preserved_store; [exact Code|].
  intros index byte Byte i I.
  rewrite length_bv_to_bytes in I. change (i < 8)%nat in I.
  rewrite machine_address_offset.
  apply (stack_byte_code_disjoint layout code frame _ index byte); [lia|exact Byte].
Qed.

Print Assumptions mem_present_subrange.
Print Assumptions save_slot_mapped.
Print Assumptions code_preserved_stack_store.
