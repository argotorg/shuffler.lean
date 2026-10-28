(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers Values.
From ASCommon Require Import Common.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory.
Import ListNotations.
Open Scope Z_scope.

Definition state_registers (state : seq_state) : registerMap :=
  archState.regs (sst state) !!! 0%fin.

Definition code_at (state : seq_state) (base : Z) (code : list (bv 8)) : Prop :=
  forall k byte, List.nth_error code k = Some byte ->
    read_byte_seq_state state (machine_address (base + Z.of_nat k)) = Some byte /\
    machine_address (base + Z.of_nat k) ∉ written state.

Record call_frame (layout : finite_layout) (code : list (bv 8)) := {
  entry_sp : Z;
  entry_pc : Z;
  return_pc : Z;
  frame_stack_bounds : 40 <= entry_sp /\ entry_sp + 16 <= address_modulus;
  frame_stack_alignment : entry_sp mod 16 = 8;
  frame_code_bounds : 0 <= entry_pc /\
    entry_pc + Z.of_nat (List.length code) <= address_modulus;
  frame_return_bounds : 0 <= return_pc < address_modulus;
  frame_return_outside : return_pc < entry_pc \/
    entry_pc + Z.of_nat (List.length code) <= return_pc;
  frame_code_stack : entry_pc + Z.of_nat (List.length code) <= entry_sp - 40 \/
    entry_sp + 16 <= entry_pc;
  frame_buffers_stack : forall b, (0 < block_words (cell_layout layout) b)%nat ->
    block_address (cell_layout layout) b +
      4 * Z.of_nat (block_words (cell_layout layout) b) <= entry_sp - 40 \/
    entry_sp + 16 <= block_address (cell_layout layout) b;
  frame_buffers_code : forall b, (0 < block_words (cell_layout layout) b)%nat ->
    block_address (cell_layout layout) b +
      4 * Z.of_nat (block_words (cell_layout layout) b) <= entry_pc \/
    entry_pc + Z.of_nat (List.length code) <= block_address (cell_layout layout) b
}.
Arguments entry_sp {layout code} _.
Arguments entry_pc {layout code} _.
Arguments return_pc {layout code} _.

Definition pointer_to_block (layout : finite_layout) b : bv 64 :=
  machine_address (block_address (cell_layout layout) b).

Record abi_entry layout code (frame : call_frame layout code)
    (n : Int.int) (bd bp bt bu trace output : Values.block) (state : seq_state) : Prop := {
  entry_registers_present : forall r, is_Some (reg_lookup r (state_registers state));
  entry_rip : reg_lookup rip (state_registers state) = Some (machine_address (entry_pc frame));
  entry_rsp : reg_lookup rsp (state_registers state) = Some (machine_address (entry_sp frame));
  entry_size : exists value, reg_lookup rdi (state_registers state) = Some value /\
    bv_extract 0 32 value = machine_word n;
  entry_data : reg_lookup rsi (state_registers state) = Some (pointer_to_block layout bd);
  entry_permutation : reg_lookup rdx (state_registers state) = Some (pointer_to_block layout bp);
  entry_target : reg_lookup rcx (state_registers state) = Some (pointer_to_block layout bt);
  entry_used : reg_lookup r8 (state_registers state) = Some (pointer_to_block layout bu);
  entry_trace : reg_lookup r9 (state_registers state) = Some (pointer_to_block layout trace);
  entry_return_address : mem_lookup (machine_address (entry_sp frame)) 8
    (archState.memory (sst state)) = Some (machine_address (return_pc frame));
  entry_output_pointer : mem_lookup (machine_address (entry_sp frame + 8)) 8
    (archState.memory (sst state)) = Some (pointer_to_block layout output);
  entry_save_slots : mem_present (machine_address (entry_sp frame - 40)) 40
    (archState.memory (sst state)) = true;
  entry_code : code_at state (entry_pc frame) code
}.

Definition callee_saved : list reg :=
  [(rbx : reg); (rbp : reg); (r12 : reg); (r13 : reg); (r14 : reg); (r15 : reg)].

Definition callee_saved_preserved (before after : seq_state) : Prop :=
  forall r, List.In r callee_saved ->
    reg_lookup r (state_registers after) = reg_lookup r (state_registers before).

Record abi_return layout code (frame : call_frame layout code)
    (before after : seq_state) (result : Int.int) : Prop := {
  return_rip : reg_lookup rip (state_registers after) = Some (machine_address (return_pc frame));
  return_rsp : reg_lookup rsp (state_registers after) = Some (machine_address (entry_sp frame + 8));
  return_value : exists value, reg_lookup rax (state_registers after) = Some value /\
    bv_extract 0 32 value = machine_word result;
  return_saved_registers : callee_saved_preserved before after
}.

Lemma saved_registers_memory_write state addr contents :
  callee_saved_preserved state (stored_bytes_state state addr contents).
Proof.
  intros r In. unfold state_registers. rewrite stored_bytes_registers. reflexivity.
Qed.

Lemma code_unchanged before after base code :
  (forall k byte, List.nth_error code k = Some byte ->
    read_byte_seq_state after (machine_address (base + Z.of_nat k)) =
      read_byte_seq_state before (machine_address (base + Z.of_nat k))) ->
  (forall k byte, List.nth_error code k = Some byte ->
    machine_address (base + Z.of_nat k) ∉ written after) ->
  code_at before base code -> code_at after base code.
Proof.
  intros Contents Untouched Code k byte At. split.
  - rewrite (Contents k byte At). exact (proj1 (Code k byte At)).
  - exact (Untouched k byte At).
Qed.
