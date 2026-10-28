(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Address X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments X86UsedZero.
Import ListNotations.
Open Scope Z_scope.

Definition validation_pc state base offset :=
  write_reg_seq_state rip (machine_address (base + offset)) state.

Lemma validation_array_load nondet layout (frame : call_frame layout program_bytes)
    state offset bytes destination base index b k value c :
  In (offset, bytes, destination, base, index) array_load_sites ->
  Values.reg (gpr_reference destination) <> rip ->
  (k < block_words (cell_layout layout) b)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  scaled_address (register_values_of state) base index =
    machine_address (cell_address (cell_layout layout) b k) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint value) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (gpr32_written destination (machine_word value)
      (validation_pc state (entry_pc frame) (offset + bytes))).
Proof.
  intros Site NotPC Index Code Present PC Address Related Load.
  destruct (Present (Values.reg (gpr_reference destination))) as [old Old].
  eapply framed_instruction with (offset := offset) (size := bytes)
    (instruction := MOV (32, rm_REG (REG_NORMAL destination),
      rmi_MEM (machine_address (cell_address (cell_layout layout) b k))));
    [exact Code|exact Present|exact PC| | |].
  - exact (array_load_instruction offset bytes destination base index Site).
  - rewrite (decode_array_load nondet _ _ offset bytes destination base index Site), Address.
    reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
    apply execute_mov32_load with (old := old).
    + unfold validation_pc. rewrite register_read_frame by congruence. exact Old.
    + unfold validation_pc. rewrite register_write_read_memory, read_mem_is_lookup.
      exact (proj2 (Related b k Index) value Load).
Qed.

Lemma validation_array_store nondet layout (frame : call_frame layout program_bytes)
    state offset bytes source base index b k value old c c' :
  In (offset, bytes, source, base, index) array_store_sites ->
  Values.reg (gpr_reference source) <> rip ->
  (k < block_words (cell_layout layout) b)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  scaled_address (register_values_of state) base index =
    machine_address (cell_address (cell_layout layout) b k) ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some old ->
  low_register32 source old = machine_word value ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c b (4 * Z.of_nat k) (Vint value) = Some c' ->
  let final := stored_bytes_state (validation_pc state (entry_pc frame) (offset + bytes))
    (machine_address (cell_address (cell_layout layout) b k))
    (bv_to_bytes 8 (machine_word value)) in
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state final /\
  machine_cells_related layout c' (archState.memory (sst final)).
Proof.
  intros Site NotPC Index Code Present PC Address Old Low Related Store final. split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := MOV (32,
        rm_MEM (machine_address (cell_address (cell_layout layout) b k)),
        rmi_REG (REG_NORMAL source))); [exact Code|exact Present|exact PC| | |].
    + exact (array_store_instruction offset bytes source base index Site).
    + rewrite (decode_array_store nondet _ _ offset bytes source base index Site), Address.
      reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      pose proof (execute_mov32_store nondet source
        (machine_address (cell_address (cell_layout layout) b k))
        (validation_pc state (entry_pc frame) (offset + bytes)) old) as Execute.
      unfold validation_pc in Execute.
      rewrite register_read_frame in Execute by congruence.
      rewrite register_write_memory in Execute.
      specialize (Execute Old (proj1 (Related b k Index))).
      fold (low_register32 source old) in Execute. rewrite Low in Execute. exact Execute.
  - unfold final, validation_pc. rewrite stored_bytes_memory, register_write_memory.
    exact (machine_cells_related_store layout c (archState.memory (sst state))
      b k value c' Related Index Store).
Qed.

Lemma validation_compare_zero nondet layout (frame : call_frame layout program_bytes)
    state offset bytes index old number :
  In (offset, bytes, index) [(93, 4, 11); (113, 3, 3)] ->
  0 <= number < 2147483648 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  low_register32 index old = Z_to_bv 32 number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = true /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (number =? 0).
Proof.
  intros Site Range Code Present PC Old Low.
  assert (NotPC : Values.reg (gpr_reference index) <> rip).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction]; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  assert (ReadNext : read_reg_seq_state (Values.reg (gpr_reference index)) next = Some old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm8 nondet index next old flags (Z_to_bv 8 0) ReadNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  change (@sign_extend 8 (Z_to_bv 8 0) 32) with (Z_to_bv 32 0) in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 number) (Z_to_bv 32 0)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL index), rmi_IMM (IMM8 (Z_to_bv 8 0))));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - split.
    + unfold result. rewrite comparison_jns by lia. apply Z.leb_le. lia.
    + unfold result. apply comparison_jne; lia.
Qed.

Lemma validation_compare_size nondet layout (frame : call_frame layout program_bytes)
    state offset bytes index old size_old number size :
  In (offset, bytes, index) [(104, 3, 11); (136, 2, 0)] ->
  0 <= number < 2147483648 -> 0 <= size < 2147483648 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  low_register32 index old = Z_to_bv 32 number ->
  read_reg_seq_state rdi state = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 size ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = (size <=? number) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (number =? size).
Proof.
  intros Site Number Size Code Present PC Old Low SizeOld SizeLow.
  assert (NotPC : Values.reg (gpr_reference index) <> rip).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction]; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  assert (ReadNext : read_reg_seq_state (Values.reg (gpr_reference index)) next = Some old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact Old. }
  assert (SizeNext : read_reg_seq_state rdi next = Some size_old).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact SizeOld. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_registers nondet index 7 next old size_old flags ReadNext SizeNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low, SizeLow in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 number) (Z_to_bv 32 size)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL index), rmi_REG (REG_NORMAL 7)));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - split; [unfold result; apply comparison_jns|unfold result; apply comparison_jne]; lia.
Qed.

Print Assumptions validation_array_load.
Print Assumptions validation_array_store.
Print Assumptions validation_compare_zero.
Print Assumptions validation_compare_size.

Lemma validation_jns nondet layout (frame : call_frame layout program_bytes)
    state offset displacement flags taken :
  In (offset, displacement) [(97, 5); (107, 33)] ->
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
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNS (Z_to_bv 8 displacement)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
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

Lemma validation_jne nondet layout (frame : call_frame layout program_bytes)
    state offset byte displacement flags taken :
  In (offset, byte, displacement) [(116, 24, 24); (138, 205, -51)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame)
      (if taken then offset + 2 + displacement else offset + 2)).
Proof.
  intros Site Code Present PC Flags Taken.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 byte) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; apply bv_eq; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNE (Z_to_bv 8 byte)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jne with (pc := machine_address (entry_pc frame + offset + 2)) (flags := flags).
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

Lemma validation_exit_jump nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 140)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame) 147).
Proof.
  intros Code Present PC.
  eapply framed_instruction with (offset := 140) (size := 2)
    (instruction := JMP (Z_to_bv 8 5)); [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jmp8 with (pc := machine_address (entry_pc frame + 140 + 2)).
    + change (@sign_extend 8 (Z_to_bv 8 5) 64) with (Z_to_bv 64 5).
      change (@add_vec 64 (machine_address (entry_pc frame + 140 + 2)) (Z_to_bv 64 5))
        with (@add_vec_int 64 (machine_address (entry_pc frame + 140 + 2)) 5).
      rewrite machine_address_next, register_write_overwrite.
      replace (entry_pc frame + 140 + 2 + 5) with (entry_pc frame + 147) by lia.
      reflexivity.
    + apply register_read_written.
Qed.

Lemma validation_mark_used nondet layout (frame : call_frame layout program_bytes)
    state used destination c c' :
  (destination < block_words (cell_layout layout) used)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 118)) ->
  scaled_address (register_values_of state) 8 11 =
    machine_address (cell_address (cell_layout layout) used destination) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c used (4 * Z.of_nat destination) (Vint Int.one) = Some c' ->
  let final := stored_bytes_state (validation_pc state (entry_pc frame) 126)
    (machine_address (cell_address (cell_layout layout) used destination))
    (bv_to_bytes 8 (machine_word Int.one)) in
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state final /\
  machine_cells_related layout c' (archState.memory (sst final)).
Proof.
  intros Index Code Present PC Address Related Store final. split.
  - eapply framed_instruction with (offset := 118) (size := 8)
      (instruction := MOV (32,
        rm_MEM (machine_address (cell_address (cell_layout layout) used destination)),
        rmi_IMM (IMM32 (machine_word Int.one)))); [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + rewrite (decode_array_immediate nondet _ _ 118 8 1 8 11 ltac:(right; left; reflexivity)), Address.
      reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 118 + 8) with (entry_pc frame + 126) by lia.
      apply execute_mov32_immediate_store. rewrite register_write_memory.
      exact (proj1 (Related used destination Index)).
  - unfold final, validation_pc. rewrite stored_bytes_memory, register_write_memory.
    exact (machine_cells_related_store layout c (archState.memory (sst state))
      used destination Int.one c' Related Index Store).
Qed.

Lemma validation_increment nondet layout (frame : call_frame layout program_bytes)
    state index :
  (index < 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 133)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags
        (write_reg_seq_state rax (machine_address (Z.of_nat (S index)))
          (validation_pc state (entry_pc frame) 136))).
Proof.
  intros Range Code Present PC Counter.
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 136).
  assert (CounterNext : read_reg_seq_state rax next = Some (machine_address (Z.of_nat index))).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Counter. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_add32_imm8 nondet 0 next (machine_address (Z.of_nat index)) flags
    (Z_to_bv 8 1) ltac:(discriminate) CounterNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Execute.
  rewrite add32_words in Execute.
  replace (Z.of_nat index + 1) with (Z.of_nat (S index)) in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) overflow carry
    (zero_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) auxiliary parity).
  eapply framed_instruction with (offset := 133) (size := 3)
    (instruction := ADD (false, 32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM8 (Z_to_bv 8 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 133 + 3) with (entry_pc frame + 136) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 0)
      (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (S index))) 64))
      with (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (S index))) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Print Assumptions validation_jns.
Print Assumptions validation_jne.
Print Assumptions validation_mark_used.
Print Assumptions validation_increment.
