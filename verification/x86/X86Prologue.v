(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86Decoded
  X86Stack X86StackMemory X86MemoryStore X86StackLayout.
Import ListNotations.
Open Scope Z_scope.

Definition advance (state : seq_state) (base offset : Z) : seq_state :=
  write_reg_seq_state rip (machine_address (base + offset)) state.

Definition output_pointer_state layout (frame : call_frame layout program_bytes)
    output state : seq_state :=
  write_reg_seq_state r10 (pointer_to_block layout output)
    (advance state (entry_pc frame) 5).

Theorem output_pointer_step nondet layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output state :
  abi_entry layout program_bytes frame n bd bp bt bu trace output state ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (output_pointer_state layout frame output state).
Proof.
  intro Entry.
  pose proof (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry) as Registers.
  pose proof (entry_rsp _ _ _ _ _ _ _ _ _ _ _ Entry) as Stack.
  change (read_reg_seq_state rsp state = Some (machine_address (entry_sp frame))) in Stack.
  destruct (Registers r10) as [old Old].
  eapply framed_instruction with (offset := 0) (size := 5)
    (instruction := MOV (64, rm_REG (REG_NORMAL 10),
      rmi_MEM (machine_address (entry_sp frame + 8)))).
  - exact (entry_code _ _ _ _ _ _ _ _ _ _ _ Entry).
  - exact Registers.
  - rewrite Z.add_0_r. exact (entry_rip _ _ _ _ _ _ _ _ _ _ _ Entry).
  - left. reflexivity.
  - rewrite decode_output_pointer, (register_value_known state rsp _ Stack),
      machine_address_next. reflexivity.
  - rewrite machine_address_next, Z.add_0_r.
    unfold output_pointer_state, advance.
    apply (execute_mov64_load nondet 10 _ _ old (pointer_to_block layout output)).
    + change (read_reg_seq_state r10
        (write_reg_seq_state rip (machine_address (entry_pc frame + 5)) state) = Some old).
      rewrite register_read_frame by discriminate. exact Old.
    + rewrite register_write_read_memory.
      exact (entry_output_pointer _ _ _ _ _ _ _ _ _ _ _ Entry).
Qed.

Lemma output_pointer_code layout (frame : call_frame layout program_bytes) output state :
  code_at state (entry_pc frame) program_bytes ->
  code_at (output_pointer_state layout frame output state) (entry_pc frame) program_bytes.
Proof. intro Code. apply code_at_register_write, code_at_register_write, Code. Qed.

Lemma output_pointer_registers layout (frame : call_frame layout program_bytes) output state :
  registers_present state ->
  registers_present (output_pointer_state layout frame output state).
Proof. intro Registers. apply registers_present_write, registers_present_write, Registers. Qed.

Print Assumptions output_pointer_step.

Definition save_sites : list (Z * Z * Z * nat) :=
  [(5, 1, 3, 0%nat); (6, 2, 12, 1%nat); (8, 2, 13, 2%nat);
   (10, 2, 14, 3%nat); (12, 2, 15, 4%nat)].

Lemma save_site_decodes nondet pc registers offset size source slot :
  In (offset, size, source, slot) save_sites ->
  In (offset, size) program_instructions /\ (slot < 5)%nat /\
  Values.reg (gpr_reference source) <> rip /\
  decoded_instruction nondet pc registers offset =
    Some (PUSH (64, rmi_REG (REG_NORMAL source))).
Proof.
  cbn [save_sites].
  intros [Here|[Here|[Here|[Here|[Here|Impossible]]]]];
    try contradiction; inversion Here; subst;
    repeat split; try discriminate; try lia;
    try (unfold program_instructions; simpl; tauto);
    destruct nondet; reflexivity.
Qed.

Definition saved_state layout (frame : call_frame layout program_bytes)
    offset size slot (value : bv 64) state : seq_state :=
  let stack := machine_address (entry_sp frame - 8 * Z.of_nat (S slot)) in
  stored_bytes_state
    (write_reg_seq_state rsp stack (advance state (entry_pc frame) (offset + size)))
    stack (bv_to_bytes 8 value).

Theorem save_step nondet layout (frame : call_frame layout program_bytes)
    state offset size source slot value :
  In (offset, size, source, slot) save_sites ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rsp state = Some (machine_address (entry_sp frame - 8 * Z.of_nat slot)) ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some value ->
  mem_present (machine_address (entry_sp frame - 40)) 40
    (archState.memory (sst state)) = true ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (saved_state layout frame offset size slot
      (Values.to_ty (gpr_reference source) value) state).
Proof.
  intros At Code Registers PC Stack Source Mapped.
  destruct (save_site_decodes nondet (machine_address (entry_pc frame + offset))
    (register_values_of state) offset size source slot At)
    as [Instruction [Slot [Different Decode]]].
  eapply framed_instruction; [exact Code|exact Registers|exact PC|exact Instruction|exact Decode|].
  rewrite machine_address_next.
  assert (Down : stack_down (machine_address (entry_sp frame - 8 * Z.of_nat slot)) =
    machine_address (entry_sp frame - 8 * Z.of_nat (S slot))).
  { change (SailStdpp.Operators_mwords.sub_vec_int
      (machine_address (entry_sp frame - 8 * Z.of_nat slot)) 8 =
        machine_address (entry_sp frame - 8 * Z.of_nat (S slot))).
    rewrite address_subtract. f_equal. lia. }
  pose proof (execute_push64 nondet source
    (write_reg_seq_state rip (machine_address (entry_pc frame + offset + size)) state)
    (machine_address (entry_sp frame - 8 * Z.of_nat slot)) value) as Execute.
  rewrite register_read_frame in Execute by discriminate.
  rewrite register_read_frame in Execute by congruence.
  rewrite register_write_memory, Down in Execute.
  specialize (Execute Stack Source (save_slot_mapped layout program_bytes frame _ slot Slot Mapped)).
  unfold saved_state, advance. replace (entry_pc frame + (offset + size)) with
    (entry_pc frame + offset + size) by lia. exact Execute.
Qed.

Lemma stored_register_read reg state addr contents :
  read_reg_seq_state reg (stored_bytes_state state addr contents) =
    read_reg_seq_state reg state.
Proof. unfold read_reg_seq_state. rewrite stored_bytes_registers. reflexivity. Qed.

Lemma registers_present_store state addr contents :
  registers_present state -> registers_present (stored_bytes_state state addr contents).
Proof. intros Present reg. rewrite stored_register_read. apply Present. Qed.

Lemma save_code layout (frame : call_frame layout program_bytes) offset size slot value state :
  (slot < 5)%nat -> code_at state (entry_pc frame) program_bytes ->
  code_at (saved_state layout frame offset size slot value state) (entry_pc frame) program_bytes.
Proof.
  intros Slot Code. apply code_preserved_stack_store; [|exact Slot].
  apply code_at_register_write, code_at_register_write, Code.
Qed.

Lemma save_registers layout (frame : call_frame layout program_bytes) offset size slot value state :
  registers_present state ->
  registers_present (saved_state layout frame offset size slot value state).
Proof. intro Present. apply registers_present_store, registers_present_write, registers_present_write, Present. Qed.

Lemma save_mapping layout (frame : call_frame layout program_bytes) offset size slot value state addr count :
  mem_present addr count (archState.memory (sst state)) = true ->
  mem_present addr count
    (archState.memory (sst (saved_state layout frame offset size slot value state))) = true.
Proof.
  intro Mapped. unfold saved_state. rewrite stored_bytes_memory, !register_write_memory.
  eapply mem_present_mapping; [apply memory_insert_bytes_mapping|exact Mapped].
Qed.

Print Assumptions save_step.

Definition saves_state layout (frame : call_frame layout program_bytes) state : seq_state :=
  let values := register_values_of state in
  saved_state layout frame 12 2 4 (values r15)
    (saved_state layout frame 10 2 3 (values r14)
      (saved_state layout frame 8 2 2 (values r13)
        (saved_state layout frame 6 2 1 (values r12)
          (saved_state layout frame 5 1 0 (values rbx) state)))).

Ltac saved_read :=
  unfold saved_state, advance;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Theorem save_registers_path nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 5)) ->
  read_reg_seq_state rsp state = Some (machine_address (entry_sp frame)) ->
  mem_present (machine_address (entry_sp frame - 40)) 40
    (archState.memory (sst state)) = true ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 5 state
    (saves_state layout frame state).
Proof.
  intros Code Registers PC Stack Mapped.
  pose (s1 := saved_state layout frame 5 1 0 (register_values_of state rbx) state).
  pose (s2 := saved_state layout frame 6 2 1 (register_values_of state r12) s1).
  pose (s3 := saved_state layout frame 8 2 2 (register_values_of state r13) s2).
  pose (s4 := saved_state layout frame 10 2 3 (register_values_of state r14) s3).
  change (instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 5 state
    (saved_state layout frame 12 2 4 (register_values_of state r15) s4)).
  eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat) (middle := s1).
  - apply (save_step nondet layout frame state 5 1 3 0 (register_values_of state rbx)).
    + left. reflexivity.
    + exact Code.
    + exact Registers.
    + exact PC.
    + replace (entry_sp frame - 8 * Z.of_nat 0) with (entry_sp frame) by lia. exact Stack.
    + apply register_values_agree, Registers.
    + exact Mapped.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat) (middle := s2).
    + apply (save_step nondet layout frame s1 6 2 12 1 (register_values_of state r12)).
      * right. left. reflexivity.
      * apply save_code; [lia|exact Code].
      * apply save_registers, Registers.
      * unfold s1. saved_read. reflexivity.
      * unfold s1. saved_read. reflexivity.
      * unfold s1. saved_read. apply register_values_agree, Registers.
      * apply save_mapping, Mapped.
    + eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat) (middle := s3).
      * apply (save_step nondet layout frame s2 8 2 13 2 (register_values_of state r13)).
        -- right. right. left. reflexivity.
        -- repeat (apply save_code; [lia|]). exact Code.
        -- do 2 apply save_registers. exact Registers.
        -- unfold s2, s1. saved_read. reflexivity.
        -- unfold s2, s1. saved_read. reflexivity.
        -- unfold s2, s1. saved_read. apply register_values_agree, Registers.
        -- repeat apply save_mapping. exact Mapped.
      * eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat) (middle := s4).
        -- apply (save_step nondet layout frame s3 10 2 14 3 (register_values_of state r14)).
           ++ right. right. right. left. reflexivity.
           ++ repeat (apply save_code; [lia|]). exact Code.
           ++ do 3 apply save_registers. exact Registers.
           ++ unfold s3, s2, s1. saved_read. reflexivity.
           ++ unfold s3, s2, s1. saved_read. reflexivity.
           ++ unfold s3, s2, s1. saved_read. apply register_values_agree, Registers.
           ++ repeat apply save_mapping. exact Mapped.
        -- apply (save_step nondet layout frame s4 12 2 15 4 (register_values_of state r15)).
           ++ right. right. right. right. left. reflexivity.
           ++ repeat (apply save_code; [lia|]). exact Code.
           ++ do 4 apply save_registers. exact Registers.
           ++ unfold s4, s3, s2, s1. saved_read. reflexivity.
           ++ unfold s4, s3, s2, s1. saved_read. reflexivity.
           ++ unfold s4, s3, s2, s1. saved_read. apply register_values_agree, Registers.
           ++ repeat apply save_mapping. exact Mapped.
Qed.

Print Assumptions save_registers_path.

Definition prologue_state layout (frame : call_frame layout program_bytes) output state : seq_state :=
  saves_state layout frame (output_pointer_state layout frame output state).

Theorem prologue_steps nondet layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output state :
  abi_entry layout program_bytes frame n bd bp bt bu trace output state ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 6 state
    (prologue_state layout frame output state).
Proof.
  intro Entry.
  eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat).
  - exact (output_pointer_step nondet layout frame n bd bp bt bu trace output state Entry).
  - apply save_registers_path.
    + apply output_pointer_code. exact (entry_code _ _ _ _ _ _ _ _ _ _ _ Entry).
    + apply output_pointer_registers. exact (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry).
    + unfold output_pointer_state, advance. rewrite register_read_frame by discriminate.
      apply register_read_written.
    + unfold output_pointer_state, advance. repeat rewrite register_read_frame by discriminate.
      exact (entry_rsp _ _ _ _ _ _ _ _ _ _ _ Entry).
    + exact (entry_save_slots _ _ _ _ _ _ _ _ _ _ _ Entry).
Qed.

Lemma prologue_code layout (frame : call_frame layout program_bytes) output state :
  code_at state (entry_pc frame) program_bytes ->
  code_at (prologue_state layout frame output state) (entry_pc frame) program_bytes.
Proof.
  intro Code. unfold prologue_state, saves_state.
  repeat (apply save_code; [lia|]). apply output_pointer_code, Code.
Qed.

Lemma prologue_registers layout (frame : call_frame layout program_bytes) output state :
  registers_present state -> registers_present (prologue_state layout frame output state).
Proof.
  intro Present. unfold prologue_state, saves_state.
  do 5 apply save_registers. apply output_pointer_registers, Present.
Qed.

Lemma prologue_pc layout (frame : call_frame layout program_bytes) output state :
  read_reg_seq_state rip (prologue_state layout frame output state) =
    Some (machine_address (entry_pc frame + 14)).
Proof. unfold prologue_state, saves_state. saved_read. reflexivity. Qed.

Lemma prologue_stack layout (frame : call_frame layout program_bytes) output state :
  read_reg_seq_state rsp (prologue_state layout frame output state) =
    Some (machine_address (entry_sp frame - 40)).
Proof. unfold prologue_state, saves_state. saved_read. reflexivity. Qed.

Lemma prologue_output layout (frame : call_frame layout program_bytes) output state :
  read_reg_seq_state r10 (prologue_state layout frame output state) =
    Some (pointer_to_block layout output).
Proof. unfold prologue_state, saves_state, output_pointer_state. saved_read. reflexivity. Qed.

Lemma prologue_other layout (frame : call_frame layout program_bytes) output state reg :
  reg <> rip -> reg <> rsp -> reg <> r10 ->
  read_reg_seq_state reg (prologue_state layout frame output state) = read_reg_seq_state reg state.
Proof.
  intros PC Stack Output. unfold prologue_state, saves_state, output_pointer_state, saved_state, advance.
  repeat first [rewrite stored_register_read | rewrite register_read_frame by congruence]. reflexivity.
Qed.

Print Assumptions prologue_steps.
