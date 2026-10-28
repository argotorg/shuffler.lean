(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Address X86Compare X86Alu X86Flags X86Data X86Arithmetic X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments X86UsedZero
  X86ValidationSteps X86PermuteSwap.
Import ListNotations.
Open Scope Z_scope.

Lemma exchange_compare_step nondet layout (frame : call_frame layout program_bytes)
    state offset bytes first second first_old second_old first_number second_number :
  In (offset, bytes, first, second) [(330, 2, 0, 3); (351, 3, 11, 15)] ->
  0 <= first_number < 4294967296 -> 0 <= second_number < 4294967296 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference first)) state = Some first_old ->
  low_register32 first first_old = Z_to_bv 32 first_number ->
  read_reg_seq_state (Values.reg (gpr_reference second)) state = Some second_old ->
  low_register32 second second_old = Z_to_bv 32 second_number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (first_number =? second_number) /\
    (first_number < 2147483648 -> second_number < 2147483648 ->
      @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = (second_number <=? first_number)).
Proof.
  intros Site FirstRange SecondRange Code Present PC First FirstLow Second SecondLow.
  assert (FirstNotPC : Values.reg (gpr_reference first) <> rip).
  { destruct Site as [Here|[Here|[]]]; inversion Here; subst; discriminate. }
  assert (SecondNotPC : Values.reg (gpr_reference second) <> rip).
  { destruct Site as [Here|[Here|[]]]; inversion Here; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  destruct (execute_cmp32_registers nondet first second next first_old second_old flags
    ltac:(unfold next, validation_pc; rewrite register_read_frame by congruence; exact First)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by congruence; exact Second)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute. rewrite FirstLow, SecondLow in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 first_number) (Z_to_bv 32 second_number)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL first), rmi_REG (REG_NORMAL second)));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|[]]]; inversion Here; subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|[]]]; inversion Here; subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - split.
    + unfold result. apply comparison_jne; assumption.
    + intros. unfold result. apply comparison_jns; lia.
Qed.

Lemma exchange_jne nondet layout (frame : call_frame layout program_bytes) state flags taken :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 332)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame) (if taken then 336 else 334)).
Proof.
  intros Code Present PC Flags Taken.
  eapply framed_instruction with (offset := 332) (size := 2)
    (instruction := JNE (Z_to_bv 8 2)); [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jne with (pc := machine_address (entry_pc frame + 332 + 2)) (flags := flags).
    + rewrite Taken. destruct taken.
      * change (@sign_extend 8 (Z_to_bv 8 2) 64) with (Z_to_bv 64 2).
        change (@add_vec 64 (machine_address (entry_pc frame + 332 + 2)) (Z_to_bv 64 2))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 332 + 2)) 2).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 332 + 2 + 2) with (entry_pc frame + 336) by lia. reflexivity.
      * replace (entry_pc frame + 332 + 2) with (entry_pc frame + 334) by lia. reflexivity.
    + apply register_read_written.
    + rewrite register_read_frame by discriminate. exact Flags.
Qed.

Lemma exchange_jns nondet layout (frame : call_frame layout program_bytes)
    state offset displacement flags taken :
  In (offset, displacement) [(346, 29); (354, 40)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame)
      (if taken then offset + 2 + displacement else offset + 2)).
Proof.
  intros Site Code Present PC Flags Taken.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 displacement) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|[]]]; inversion Here; subst; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNS (Z_to_bv 8 displacement)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|[]]]; inversion Here; subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|[]]]; inversion Here; subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jns with (pc := machine_address (entry_pc frame + offset + 2)) (flags := flags).
    + rewrite Taken. destruct taken.
      * rewrite Extend.
        change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
          with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + offset + 2 + displacement) with
          (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
      * replace (entry_pc frame + offset + 2) with (entry_pc frame + (offset + 2)) by lia.
        reflexivity.
    + apply register_read_written.
    + rewrite register_read_frame by discriminate. exact Flags.
Qed.

Lemma exchange_jump nondet layout (frame : call_frame layout program_bytes)
    state offset displacement :
  In (offset, displacement) [(334, 62); (375, 21); (394, 32)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame) (offset + 2 + displacement)).
Proof.
  intros Site Code Present PC.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 displacement) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JMP (Z_to_bv 8 displacement)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jmp8 with (pc := machine_address (entry_pc frame + offset + 2)).
    + rewrite Extend.
      change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
        with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
      rewrite machine_address_next, register_write_overwrite.
      replace (entry_pc frame + offset + 2 + displacement) with
        (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
    + apply register_read_written.
Qed.

Lemma exchange_copy_top nondet layout (frame : call_frame layout program_bytes) state number :
  0 <= number <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 336)) ->
  read_reg_seq_state r12 state = Some (machine_address number) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state r14 (machine_address number) (validation_pc state (entry_pc frame) 339)).
Proof.
  intros Range Code Present PC Top. destruct (Present r14) as [old Old].
  eapply framed_instruction with (offset := 336) (size := 3)
    (instruction := MOV (32, rm_REG (REG_NORMAL 14), rmi_REG (REG_NORMAL 12)));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 336 + 3) with (entry_pc frame + 339) by lia.
    pose proof (execute_mov32_registers nondet 12 14
      (validation_pc state (entry_pc frame) 339) (machine_address number) old
      ltac:(unfold validation_pc; rewrite register_read_frame by discriminate; exact Top)
      ltac:(unfold validation_pc; rewrite register_read_frame by discriminate; exact Old)) as Execute.
    fold (low_register32 12 (machine_address number)) in Execute.
    change (low_register32 12 (machine_address number)) with
      (low_register32 0 (machine_address number)) in Execute.
    rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Lemma exchange_depth nondet layout (frame : call_frame layout program_bytes) state top position :
  0 <= position <= top -> top <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 339)) ->
  read_reg_seq_state r14 state = Some (machine_address top) ->
  read_reg_seq_state r13 state = Some (machine_address position) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (write_reg_seq_state r14 (machine_address (top - position))
        (validation_pc state (entry_pc frame) 342))).
Proof.
  intros Range Bound Code Present PC Top Position. destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 342).
  destruct (execute_sub32_registers nondet 14 13 next (machine_address top) (machine_address position) flags
    ltac:(discriminate)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Top)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Position)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 14 (machine_address top)) with (low_register32 0 (machine_address top)) in Execute.
  change (low_register32 13 (machine_address position)) with (low_register32 0 (machine_address position)) in Execute.
  rewrite !machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  rewrite subtract32 in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (top - position))) overflow carry
    (zero_flag32 (Z_to_bv 32 (top - position))) auxiliary parity).
  eapply framed_instruction with (offset := 339) (size := 3)
    (instruction := SUB (false, 32, rm_REG (REG_NORMAL 14), rmi_REG (REG_NORMAL 13)));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 339 + 3) with (entry_pc frame + 342) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 14) (@zero_extend 32 (Z_to_bv 32 (top - position)) 64))
      with (@zero_extend 32 (Z_to_bv 32 (top - position)) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Lemma exchange_compare_depth nondet layout (frame : call_frame layout program_bytes) state number :
  0 <= number <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 342)) ->
  read_reg_seq_state r14 state = Some (machine_address number) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) 346)) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = (17 <=? number).
Proof.
  intros Range Code Present PC Depth. destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 346).
  destruct (execute_cmp32_imm8 nondet 14 next (machine_address number) flags (Z_to_bv 8 17)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Depth)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 14 (machine_address number)) with (low_register32 0 (machine_address number)) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 17) 32) with (Z_to_bv 32 17) in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 number) (Z_to_bv 32 17)).
  exists (result_flags flags (sign_flag32 result) overflow carry (zero_flag32 result) auxiliary parity).
  split.
  - eapply framed_instruction with (offset := 342) (size := 4)
      (instruction := CMP (32, rm_REG (REG_NORMAL 14), rmi_IMM (IMM8 (Z_to_bv 8 17))));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 342 + 4) with (entry_pc frame + 346) by lia. exact Execute.
  - unfold result. apply comparison_jns; lia.
Qed.

Print Assumptions exchange_compare_step.
Print Assumptions exchange_jne.
Print Assumptions exchange_jns.
Print Assumptions exchange_jump.
Print Assumptions exchange_copy_top.
Print Assumptions exchange_depth.
Print Assumptions exchange_compare_depth.

Lemma exchange_load_count nondet layout (frame : call_frame layout program_bytes)
    state output value c :
  (0 < block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 348)) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c output 0 = Some (Vint value) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state r11 (@zero_extend 32 (machine_word value) 64)
      (validation_pc state (entry_pc frame) 351)).
Proof.
  intros Capacity Code Present PC Pointer Related Load.
  destruct (Present r11) as [old Old].
  assert (Decode : decoded_instruction nondet (machine_address (entry_pc frame + 348))
    (register_values_of state) 348 = Some (MOV (32, rm_REG (REG_NORMAL 11),
      rmi_MEM (register_values_of state r10)))).
  { rewrite <- (subrange64 (register_values_of state r10)). destruct nondet; reflexivity. }
  rewrite (register_value_known state r10 _ Pointer) in Decode.
  assert (Address : pointer_to_block layout output =
    machine_address (cell_address (cell_layout layout) output 0)).
  { unfold pointer_to_block, cell_address. f_equal. lia. }
  rewrite Address in Decode.
  eapply framed_instruction with (offset := 348) (size := 3)
    (instruction := MOV (32, rm_REG (REG_NORMAL 11),
      rmi_MEM (machine_address (cell_address (cell_layout layout) output 0))));
    [exact Code|exact Present|exact PC| |exact Decode|].
  - vm_compute; tauto.
  - rewrite machine_address_next.
    replace (entry_pc frame + 348 + 3) with (entry_pc frame + 351) by lia.
    apply (execute_mov32_load nondet 11 _ _ old (machine_word value)).
    + unfold validation_pc. rewrite register_read_frame by discriminate. exact Old.
    + unfold validation_pc. rewrite register_write_read_memory, read_mem_is_lookup.
      exact (proj2 (Related output 0%nat Capacity) value Load).
Qed.

Definition exchange_output_sites : list (Z * Z * Z * nat) :=
  [(372, 3, 11, 0%nat); (377, 4, 13, 1%nat); (385, 4, 14, 2%nat)].

Lemma exchange_output_decode nondet pc (registers : register_values) layout output offset bytes source index :
  In (offset, bytes, source, index) exchange_output_sites ->
  registers r10 = pointer_to_block layout output ->
  decoded_instruction nondet pc registers offset = Some (MOV (32,
    rm_MEM (machine_address (cell_address (cell_layout layout) output index)),
    rmi_REG (REG_NORMAL source))).
Proof.
  intros Site Pointer.
  destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst offset bytes source index.
  - unfold cell_address. change (4 * Z.of_nat 0) with 0. rewrite Z.add_0_r.
    change (machine_address (block_address (cell_layout layout) output)) with (pointer_to_block layout output).
    rewrite <- Pointer, <- (subrange64 (registers r10)). destruct nondet; reflexivity.
  - unfold cell_address. change (4 * Z.of_nat 1) with 4.
    rewrite <- machine_address_next.
    change (machine_address (block_address (cell_layout layout) output)) with (pointer_to_block layout output).
    rewrite <- Pointer, <- (subrange64 (registers r10)). destruct nondet; reflexivity.
  - unfold cell_address. change (4 * Z.of_nat 2) with 8.
    rewrite <- machine_address_next.
    change (machine_address (block_address (cell_layout layout) output)) with (pointer_to_block layout output).
    rewrite <- Pointer, <- (subrange64 (registers r10)). destruct nondet; reflexivity.
Qed.

Lemma exchange_output_store nondet layout (frame : call_frame layout program_bytes)
    state offset bytes source output index value old c c' :
  In (offset, bytes, source, index) exchange_output_sites ->
  (index < block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some old ->
  low_register32 source old = machine_word value ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c output (4 * Z.of_nat index) (Vint value) = Some c' ->
  let final := stored_bytes_state (validation_pc state (entry_pc frame) (offset + bytes))
    (machine_address (cell_address (cell_layout layout) output index))
    (bv_to_bytes 8 (machine_word value)) in
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state final /\
  machine_cells_related layout c' (archState.memory (sst final)).
Proof.
  intros Site Capacity Code Present PC Pointer Old Low Related Store final.
  assert (NotPC : Values.reg (gpr_reference source) <> rip).
  { destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst; discriminate. }
  split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := MOV (32, rm_MEM (machine_address (cell_address (cell_layout layout) output index)),
        rmi_REG (REG_NORMAL source))); [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|[Here|[]]]]; inversion Here; subst; vm_compute; tauto.
    + exact (exchange_output_decode nondet _ _ layout output offset bytes source index Site
        (register_value_known state r10 _ Pointer)).
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      pose proof (execute_mov32_store nondet source
        (machine_address (cell_address (cell_layout layout) output index))
        (validation_pc state (entry_pc frame) (offset + bytes)) old) as Execute.
      unfold validation_pc in Execute. rewrite register_read_frame in Execute by congruence.
      rewrite register_write_memory in Execute.
      specialize (Execute Old (proj1 (Related output index Capacity))).
      fold (low_register32 source old) in Execute. rewrite Low in Execute. exact Execute.
  - unfold final, validation_pc. rewrite stored_bytes_memory, register_write_memory.
    exact (machine_cells_related_store layout c (archState.memory (sst state))
      output index value c' Related Capacity Store).
Qed.

Lemma exchange_excess nondet layout (frame : call_frame layout program_bytes) state number :
  17 <= number <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 381)) ->
  read_reg_seq_state r14 state = Some (machine_address number) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (write_reg_seq_state r14 (machine_address (number - 16))
        (validation_pc state (entry_pc frame) 385))).
Proof.
  intros Range Code Present PC Depth. destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 385).
  destruct (execute_sub32_imm8 nondet 14 next (machine_address number) flags (Z_to_bv 8 16)
    ltac:(discriminate)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Depth)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 14 (machine_address number)) with (low_register32 0 (machine_address number)) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 16) 32) with (Z_to_bv 32 16) in Execute.
  rewrite subtract32 in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (number - 16))) overflow carry
    (zero_flag32 (Z_to_bv 32 (number - 16))) auxiliary parity).
  eapply framed_instruction with (offset := 381) (size := 4)
    (instruction := SUB (false, 32, rm_REG (REG_NORMAL 14), rmi_IMM (IMM8 (Z_to_bv 8 16))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 381 + 4) with (entry_pc frame + 385) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 14) (@zero_extend 32 (Z_to_bv 32 (number - 16)) 64))
      with (@zero_extend 32 (Z_to_bv 32 (number - 16)) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Lemma exchange_increment_count nondet layout (frame : call_frame layout program_bytes) state number :
  0 <= number < 2048 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 368)) ->
  read_reg_seq_state r11 state = Some (machine_address number) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (write_reg_seq_state r11 (machine_address (number + 1))
        (validation_pc state (entry_pc frame) 372))).
Proof.
  intros Range Code Present PC Count. destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 372).
  destruct (execute_add32_imm8 nondet 11 next (machine_address number) flags (Z_to_bv 8 1)
    ltac:(discriminate)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Count)
    ltac:(unfold next, validation_pc; rewrite register_read_frame by discriminate; exact Flags))
    as (overflow & carry & auxiliary & parity & Execute).
  cbn beta zeta in Execute.
  change (low_register32 11 (machine_address number)) with (low_register32 0 (machine_address number)) in Execute.
  rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Execute.
  rewrite add32_words in Execute.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (number + 1))) overflow carry
    (zero_flag32 (Z_to_bv 32 (number + 1))) auxiliary parity).
  eapply framed_instruction with (offset := 368) (size := 4)
    (instruction := ADD (false, 32, rm_REG (REG_NORMAL 11), rmi_IMM (IMM8 (Z_to_bv 8 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 368 + 4) with (entry_pc frame + 372) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 11) (@zero_extend 32 (Z_to_bv 32 (number + 1)) 64))
      with (@zero_extend 32 (Z_to_bv 32 (number + 1)) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Lemma exchange_return_one nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 389)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state rax (machine_address 1) (validation_pc state (entry_pc frame) 394)).
Proof.
  intros Code Present PC. destruct (Present rax) as [old Old].
  eapply framed_instruction with (offset := 389) (size := 5)
    (instruction := MOV (32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM32 (Z_to_bv 32 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 389 + 5) with (entry_pc frame + 394) by lia.
    apply (execute_mov32_immediate nondet 0 _ old (Z_to_bv 32 1)).
    unfold validation_pc. rewrite register_read_frame by discriminate. exact Old.
Qed.

Print Assumptions exchange_load_count.
Print Assumptions exchange_output_decode.
Print Assumptions exchange_output_store.
Print Assumptions exchange_excess.
Print Assumptions exchange_increment_count.
Print Assumptions exchange_return_one.
