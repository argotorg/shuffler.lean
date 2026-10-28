(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86Decode X86ArrayDecode X86CellAddress X86Address
  X86Flags X86Data X86StackMemory X86MemoryStore X86MemoryFrame X86Prologue
  X86StackFrame X86Call X86CallFrame X86ValidationSteps.
Import ListNotations.
Open Scope Z_scope.

Lemma permute_swap_jump nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 414)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame) 275).
Proof.
  intros Code Present PC.
  eapply framed_instruction with (offset := 414) (size := 5)
    (instruction := JMP32 (Z_to_bv 32 4294967152));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jmp32 with (pc := machine_address (entry_pc frame + 414 + 5)).
    + assert (Extend : @sign_extend 32 (Z_to_bv 32 4294967152) 64 = Z_to_bv 64 (-144))
        by (apply bv_eq; reflexivity).
      rewrite Extend.
      change (@add_vec 64 (machine_address (entry_pc frame + 414 + 5)) (Z_to_bv 64 (-144)))
        with (@add_vec_int 64 (machine_address (entry_pc frame + 414 + 5)) (-144)).
      rewrite machine_address_next, register_write_overwrite.
      replace (entry_pc frame + 414 + 5 + -144) with (entry_pc frame + 275) by lia.
      reflexivity.
    + apply register_read_written.
Qed.

Lemma permute_swap_address layout state index block position :
  read_reg_seq_state (Values.reg (gpr_reference 2)) state =
    Some (Values.from_ty (gpr_reference 2) (pointer_to_block layout block)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state =
    Some (Values.from_ty (gpr_reference index) (machine_address (Z.of_nat position))) ->
  scaled_address (register_values_of state) 2 index =
    machine_address (cell_address (cell_layout layout) block position).
Proof.
  intros Base Index. unfold scaled_address, scaled_gprs, gpr64.
  rewrite (register_value_known state _ _ Base), (register_value_known state _ _ Index),
    !gpr_reference_inverse.
  apply scaled_cell_address.
Qed.

Ltac permute_swap_unfold :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold validation_pc.

Ltac permute_swap_reads :=
  permute_swap_unfold;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by congruence].

Ltac permute_swap_code :=
  permute_swap_unfold;
  repeat first [apply code_at_register_write | apply code_preserved_cell_store; [|lia]];
  assumption.

Ltac permute_swap_present :=
  permute_swap_unfold;
  repeat first [apply registers_present_write | apply registers_present_store]; assumption.

Ltac permute_swap_stack :=
  permute_swap_unfold;
  repeat first [apply call_stack_register_write; [|discriminate|discriminate] |
    apply call_stack_cell_store; [|lia]]; assumption.

Theorem permute_swap_block nondet layout (frame : call_frame layout program_bytes)
    initial state bp position top position_value top_value c c1 c2 :
  (position < block_words (cell_layout layout) bp)%nat ->
  (top < block_words (cell_layout layout) bp)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 398)) ->
  read_reg_seq_state rdx state = Some (pointer_to_block layout bp) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat position) = Some (Vint position_value) ->
  Mem.load Mint32 c bp (4 * Z.of_nat top) = Some (Vint top_value) ->
  Mem.store Mint32 c bp (4 * Z.of_nat position) (Vint top_value) = Some c1 ->
  Mem.store Mint32 c1 bp (4 * Z.of_nat top) (Vint position_value) = Some c2 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 5 state final /\
    machine_cells_related layout c2 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 275)) /\
    read_reg_seq_state rax final = Some (@zero_extend 32 (machine_word position_value) 64) /\
    read_reg_seq_state rbx final = Some (@zero_extend 32 (machine_word top_value) 64) /\
    (forall reg : Arch.reg, reg <> rip -> reg <> rax -> reg <> rbx ->
      read_reg_seq_state reg final = read_reg_seq_state reg state).
Proof.
  intros PositionCapacity TopCapacity Code Present Stack PC Perm Position Top Related
    PositionLoad TopLoad PositionStore TopStore.
  pose (s1 := write_reg_seq_state rax (@zero_extend 32 (machine_word position_value) 64)
    (validation_pc state (entry_pc frame) 402)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (validation_array_load nondet layout frame state 398 4 0 2 13 bp position
      position_value c ltac:(cbn; tauto) ltac:(discriminate) PositionCapacity Code Present PC
      ltac:(apply permute_swap_address; [exact Perm|exact Position]) Related PositionLoad). }
  assert (Related1 : machine_cells_related layout c (archState.memory (sst s1))).
  { unfold s1, validation_pc. rewrite !register_write_memory. exact Related. }
  pose (s2 := write_reg_seq_state rbx (@zero_extend 32 (machine_word top_value) 64)
    (validation_pc s1 (entry_pc frame) 406)).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { apply (validation_array_load nondet layout frame s1 402 4 3 2 12 bp top top_value c).
    - cbn; tauto.
    - discriminate.
    - exact TopCapacity.
    - permute_swap_code.
    - permute_swap_present.
    - permute_swap_reads; reflexivity.
    - apply (permute_swap_address layout s1 12 bp top).
      + change (read_reg_seq_state rdx s1 = Some (pointer_to_block layout bp)).
        permute_swap_reads; exact Perm.
      + change (read_reg_seq_state r12 s1 = Some (machine_address (Z.of_nat top))).
        permute_swap_reads; exact Top.
    - exact Related1.
    - exact TopLoad. }
  assert (Related2 : machine_cells_related layout c (archState.memory (sst s2))).
  { unfold s2, validation_pc. rewrite !register_write_memory. exact Related1. }
  pose (s3 := stored_bytes_state (validation_pc s2 (entry_pc frame) 410)
    (machine_address (cell_address (cell_layout layout) bp position))
    (bv_to_bytes 8 (machine_word top_value))).
  destruct (validation_array_store nondet layout frame s2 406 4 3 2 13 bp position top_value
    (@zero_extend 32 (machine_word top_value) 64) c c1
    ltac:(cbn; tauto) ltac:(discriminate) PositionCapacity
    ltac:(permute_swap_code) ltac:(permute_swap_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(apply (permute_swap_address layout s2 13 bp position);
      [change (read_reg_seq_state rdx s2 = Some (pointer_to_block layout bp));
       permute_swap_reads; exact Perm|
       change (read_reg_seq_state r13 s2 = Some (machine_address (Z.of_nat position)));
       permute_swap_reads; exact Position])
    ltac:(permute_swap_reads; reflexivity) ltac:(apply low32_zero_extend)
    Related2 PositionStore) as [Step3 Related3].
  pose (s4 := stored_bytes_state (validation_pc s3 (entry_pc frame) 414)
    (machine_address (cell_address (cell_layout layout) bp top))
    (bv_to_bytes 8 (machine_word position_value))).
  assert (Write4 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s3 s4 /\
      machine_cells_related layout c2 (archState.memory (sst s4))).
  { apply (validation_array_store nondet layout frame s3 410 4 0 2 12 bp top position_value
      (@zero_extend 32 (machine_word position_value) 64) c1 c2).
    - cbn; tauto.
    - discriminate.
    - exact TopCapacity.
    - permute_swap_code.
    - permute_swap_present.
    - permute_swap_reads; reflexivity.
    - apply (permute_swap_address layout s3 12 bp top).
      + change (read_reg_seq_state rdx s3 = Some (pointer_to_block layout bp)).
        permute_swap_reads; exact Perm.
      + change (read_reg_seq_state r12 s3 = Some (machine_address (Z.of_nat top))).
        permute_swap_reads; exact Top.
    - change (read_reg_seq_state rax s3 = Some (@zero_extend 32 (machine_word position_value) 64)).
      permute_swap_reads; reflexivity.
    - apply low32_zero_extend.
    - exact Related3.
    - exact TopStore. }
  destruct Write4 as [Step4 Related4].
  pose (final := validation_pc s4 (entry_pc frame) 275).
  assert (Step5 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s4 final).
  { apply permute_swap_jump; [permute_swap_code|permute_swap_present|permute_swap_reads; reflexivity]. }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step4|exact Step5].
  - split.
    { unfold final, validation_pc. rewrite register_write_memory. exact Related4. }
    split; [permute_swap_code|]. split; [permute_swap_present|]. split; [permute_swap_stack|].
    split; [permute_swap_reads; reflexivity|]. split; [permute_swap_reads; reflexivity|].
    split; [permute_swap_reads; reflexivity|].
    intros reg NotPC NotAX NotBX. permute_swap_reads. reflexivity.
Qed.

Print Assumptions permute_swap_jump.
Print Assumptions permute_swap_address.
Print Assumptions permute_swap_block.
