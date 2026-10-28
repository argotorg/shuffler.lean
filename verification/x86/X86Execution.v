(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Instructions X86Decode X86Control X86ABI X86Entry
  X86Program X86DecodeReplay X86Decoder X86Memory.
Import ListNotations.
Open Scope Z_scope.

Definition registers_present (state : seq_state) : Prop :=
  forall reg, is_Some (read_reg_seq_state reg state).

Definition register_default (reg : Arch.reg) : reg_type reg :=
  match reg with R_bitvector_64 _ => bv_0 64 end.

Definition register_values_of (state : seq_state) : register_values :=
  fun reg => default (register_default reg) (read_reg_seq_state reg state).

Lemma register_values_agree state :
  registers_present state ->
  forall reg, read_reg_seq_state reg state = Some (register_values_of state reg).
Proof.
  intros Present reg. destruct (Present reg) as [value Read].
  unfold register_values_of. now rewrite Read.
Qed.

Lemma register_value_known state reg value :
  read_reg_seq_state reg state = Some value -> register_values_of state reg = value.
Proof. intro Read. unfold register_values_of. now rewrite Read. Qed.

Lemma registers_present_write reg value state :
  registers_present state -> registers_present (write_reg_seq_state reg value state).
Proof.
  intros Present other. destruct (decide (reg = other)) as [Same|Different].
  - subst other. rewrite register_read_written. eexists. reflexivity.
  - rewrite register_read_frame by exact Different. apply Present.
Qed.

Lemma abi_registers_present layout code frame n bd bp bt bu trace output state :
  abi_entry layout code frame n bd bp bt bu trace output state -> registers_present state.
Proof.
  intro Entry. exact (entry_registers_present layout code frame n bd bp bt bu trace output state Entry).
Qed.

Print Assumptions register_values_agree.
Print Assumptions registers_present_write.

Lemma instruction_offset_range offset size :
  In (offset, size) program_instructions ->
  0 <= offset < Z.of_nat (List.length program_bytes).
Proof.
  intro At.
  assert (Bounds : forallb (fun item =>
    (0 <=? fst item) && (fst item <? Z.of_nat (List.length program_bytes)))
      program_instructions = true) by (vm_compute; reflexivity).
  apply forallb_forall with (x := (offset, size)) in Bounds; [|exact At].
  apply andb_true_iff in Bounds as [Low High].
  split; [now apply Z.leb_le|now apply Z.ltb_lt].
Qed.

Theorem step_from_code nondet state base offset size instruction final :
  code_at state base program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (base + offset)) ->
  In (offset, size) program_instructions ->
  decoded_instruction nondet (machine_address (base + offset))
    (register_values_of state) offset = Some instruction ->
  sail_run nondet (Tiny_x86.execute instruction)
    (write_reg_seq_state rip
      (@SailStdpp.Operators_mwords.add_vec_int 64 (machine_address (base + offset)) size)
      state) = Exec.make [(final, tt)] [] ->
  instruction_step (sail_tiny_x86_sem nondet) state = Exec.make [(final, tt)] [].
Proof.
  intros Code Registers PC At Decode Execute.
  eapply fetch_execute_decoded; [exact PC| |exact Execute].
  apply (decode_from_code nondet state base (register_values_of state) offset size instruction);
    try assumption.
  now apply register_values_agree.
Qed.

Theorem framed_instruction nondet layout (frame : call_frame layout program_bytes)
    state offset size instruction final :
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  In (offset, size) program_instructions ->
  decoded_instruction nondet (machine_address (entry_pc frame + offset))
    (register_values_of state) offset = Some instruction ->
  sail_run nondet (Tiny_x86.execute instruction)
    (write_reg_seq_state rip
      (@SailStdpp.Operators_mwords.add_vec_int 64 (machine_address (entry_pc frame + offset)) size)
      state) = Exec.make [(final, tt)] [] ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state final.
Proof.
  intros Code Registers PC At Decode Execute.
  pose proof (instruction_offset_range offset size At) as Range.
  econstructor.
  - eapply instruction_before_return with (offset := Z.to_nat offset).
    + lia.
    + rewrite Z2Nat.id by lia. exact PC.
  - eapply step_from_code; eassumption.
  - constructor.
Qed.

Print Assumptions step_from_code.
Print Assumptions framed_instruction.
