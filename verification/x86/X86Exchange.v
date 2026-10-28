(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation FixedBlocks.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86ArrayDecode X86CellAddress X86Address X86Compare
  X86Alu X86Flags X86Data X86StackMemory X86MemoryStore X86MemoryFrame X86Prologue
  X86StackFrame X86Call X86CallFrame X86Arguments X86UsedZero X86ValidationSteps
  X86Normalize X86PermuteSwap X86ExchangeSteps.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_clobbered : list Arch.reg :=
  [(rip : Arch.reg); (rax : Arch.reg); (rbx : Arch.reg); (r11 : Arch.reg);
   (r14 : Arch.reg); (rflags : Arch.reg)].

Definition exchange_register_frame before after : Prop :=
  forall reg : Arch.reg, ~ In reg exchange_clobbered ->
    read_reg_seq_state reg after = read_reg_seq_state reg before.

Lemma exchange_frame_trans first middle final :
  exchange_register_frame first middle -> exchange_register_frame middle final ->
  exchange_register_frame first final.
Proof. intros First Final reg Outside. rewrite Final, First by exact Outside. reflexivity. Qed.

Lemma exchange_frame_arguments layout size bd bp bt bu trace output before after :
  exchange_register_frame before after -> core_arguments layout size bd bp bt bu trace output before ->
  core_arguments layout size bd bp bt bu trace output after.
Proof.
  intros Registers Arguments.
  apply (core_arguments_frame _ _ _ _ _ _ _ _ before after Arguments).
  intros reg Inside. apply Registers. unfold argument_registers in Inside.
  repeat destruct Inside as [<-|Inside]; try contradiction;
    unfold exchange_clobbered; cbn; intuition discriminate.
Qed.

Lemma exchange_frame_write before after (reg : Arch.reg) value :
  In reg exchange_clobbered -> exchange_register_frame before after ->
  exchange_register_frame before (write_reg_seq_state reg value after).
Proof.
  intros Inside Frame other Outside. rewrite register_read_frame by congruence.
  apply Frame, Outside.
Qed.

Lemma exchange_frame_store before after address bytes :
  exchange_register_frame before after ->
  exchange_register_frame before (stored_bytes_state after address bytes).
Proof. intros Frame other Outside. rewrite stored_register_read. apply Frame, Outside. Qed.

Ltac exchange_code :=
  permute_swap_unfold;
  repeat lazymatch goal with
  | |- code_at (write_reg_seq_state _ _ _) _ _ => apply code_at_register_write
  | |- code_at (stored_bytes_state _ _ _) _ _ => apply code_preserved_cell_store; [|lia]
  end; assumption.

Ltac exchange_present :=
  permute_swap_unfold;
  repeat lazymatch goal with
  | |- registers_present (write_reg_seq_state _ _ _) => apply registers_present_write
  | |- registers_present (stored_bytes_state _ _ _) => apply registers_present_store
  end; assumption.

Ltac exchange_stack :=
  permute_swap_unfold;
  repeat lazymatch goal with
  | |- call_stack _ _ _ (write_reg_seq_state _ _ _) =>
      apply call_stack_register_write; [|discriminate|discriminate]
  | |- call_stack _ _ _ (stored_bytes_state _ _ _) => apply call_stack_cell_store; [|lia]
  end; assumption.

Ltac exchange_frame_build :=
  permute_swap_unfold;
  repeat lazymatch goal with
  | |- exchange_register_frame _ (write_reg_seq_state _ _ _) =>
      apply exchange_frame_write; [unfold exchange_clobbered; cbn; tauto|]
  | |- exchange_register_frame _ (stored_bytes_state _ _ _) => apply exchange_frame_store
  end; intros reg Outside; reflexivity.

Ltac exchange_frame_read Frame :=
  rewrite Frame by (unfold exchange_clobbered; cbn; intuition discriminate).

Lemma exchange_probe nondet layout (frame : call_frame layout program_bytes)
    initial state bd position top x y c :
  (position < block_words (cell_layout layout) bd)%nat ->
  (top < block_words (cell_layout layout) bd)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state rsi state = Some (pointer_to_block layout bd) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat position) = Some (Vint x) ->
  Mem.load Mint32 c bd (4 * Z.of_nat top) = Some (Vint y) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 4 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if word_equal x y then 334 else 336))) /\
    read_reg_seq_state rax final = Some (@zero_extend 32 (machine_word x) 64) /\
    read_reg_seq_state rbx final = Some (@zero_extend 32 (machine_word y) 64) /\
    exchange_register_frame state final.
Proof.
  intros PositionCapacity TopCapacity Code Present Stack PC Data Position Top Related LoadX LoadY.
  pose (s1 := write_reg_seq_state rax (@zero_extend 32 (machine_word x) 64)
    (validation_pc state (entry_pc frame) 326)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (validation_array_load nondet layout frame state 322 4 0 6 13 bd position x c
      ltac:(cbn; tauto) ltac:(discriminate) PositionCapacity Code Present PC
      ltac:(apply (normalize_array_address layout state 6 13 bd position); [exact Data|exact Position])
      Related LoadX). }
  assert (Related1 : machine_cells_related layout c (archState.memory (sst s1))).
  { unfold s1, validation_pc. rewrite !register_write_memory. exact Related. }
  pose (s2 := write_reg_seq_state rbx (@zero_extend 32 (machine_word y) 64)
    (validation_pc s1 (entry_pc frame) 330)).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { exact (validation_array_load nondet layout frame s1 326 4 3 6 12 bd top y c
      ltac:(cbn; tauto) ltac:(discriminate) TopCapacity
      ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
      ltac:(apply (normalize_array_address layout s1 6 12 bd top);
        [change (read_reg_seq_state rsi s1 = Some (pointer_to_block layout bd)); permute_swap_reads; exact Data|
         change (read_reg_seq_state r12 s1 = Some (machine_address (Z.of_nat top))); permute_swap_reads; exact Top])
      Related1 LoadY). }
  destruct (exchange_compare_step nondet layout frame s2 330 2 0 3
    (@zero_extend 32 (machine_word x) 64) (@zero_extend 32 (machine_word y) 64)
    (Int.unsigned x) (Int.unsigned y) ltac:(left; reflexivity)
    (Int.unsigned_range x) (Int.unsigned_range y)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(change (read_reg_seq_state rax s2 = Some (@zero_extend 32 (machine_word x) 64));
      permute_swap_reads; reflexivity) ltac:(apply low32_zero_extend)
    ltac:(change (read_reg_seq_state rbx s2 = Some (@zero_extend 32 (machine_word y) 64));
      permute_swap_reads; reflexivity) ltac:(apply low32_zero_extend))
    as (flags & Step3 & Zero & Sign).
  change (@eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (word_equal x y)) in Zero.
  pose (s3 := write_reg_seq_state rflags flags (validation_pc s2 (entry_pc frame) 332)).
  pose (final := validation_pc s3 (entry_pc frame) (if word_equal x y then 334 else 336)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 final).
  { pose proof (exchange_jne nondet layout frame s3 flags (negb (word_equal x y))
      ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
      ltac:(permute_swap_reads; reflexivity) Zero) as Step.
    destruct (word_equal x y); exact Step. }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
  - split; [unfold final, s3, s2, s1, validation_pc; rewrite !register_write_memory; reflexivity|].
    split; [exchange_code|]. split; [exchange_present|]. split; [exchange_stack|].
    split; [permute_swap_reads; reflexivity|]. split; [permute_swap_reads; reflexivity|].
    split; [permute_swap_reads; reflexivity|exchange_frame_build].
Qed.

Theorem exchange_equal nondet layout (frame : call_frame layout program_bytes)
    initial state bd position top x y c :
  (position < block_words (cell_layout layout) bd)%nat ->
  (top < block_words (cell_layout layout) bd)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state rsi state = Some (pointer_to_block layout bd) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat position) = Some (Vint x) ->
  Mem.load Mint32 c bd (4 * Z.of_nat top) = Some (Vint y) -> word_equal x y = true ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 5 state final /\
    machine_cells_related layout c (archState.memory (sst final)) /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 398)) /\
    exchange_register_frame state final.
Proof.
  intros PositionCapacity TopCapacity Code Present Stack PC Data Position Top Related LoadX LoadY Equal.
  destruct (exchange_probe nondet layout frame initial state bd position top x y c
    PositionCapacity TopCapacity Code Present Stack PC Data Position Top Related LoadX LoadY)
    as (middle & Steps & Memory & Code1 & Present1 & Stack1 & PC1 & AX & BX & Frame1).
  rewrite Equal in PC1.
  pose (final := validation_pc middle (entry_pc frame) 398).
  assert (Step : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 middle final).
  { exact (exchange_jump nondet layout frame middle 334 62 ltac:(left; reflexivity) Code1 Present1 PC1). }
  exists final. split.
  - eapply instruction_steps_append with (count := 4%nat) (rest := 1%nat); eassumption.
  - assert (FinalMemory : archState.memory (sst final) = archState.memory (sst state)).
    { unfold final, validation_pc. rewrite register_write_memory. exact Memory. }
    split; [rewrite FinalMemory; exact Related|]. split; [exact FinalMemory|].
    split; [exchange_code|]. split; [exchange_present|]. split; [exchange_stack|].
    split; [permute_swap_reads; reflexivity|].
    eapply exchange_frame_trans; [exact Frame1|exchange_frame_build].
Qed.

Lemma exchange_depth_path nondet layout (frame : call_frame layout program_bytes)
    initial state position top :
  (position <= top <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 336)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 4 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if 17 <=? Z.of_nat top - Z.of_nat position then 377 else 348))) /\
    read_reg_seq_state r14 final = Some (machine_address (Z.of_nat top - Z.of_nat position)) /\
    (forall reg : Arch.reg, reg <> rip -> reg <> r14 -> reg <> rflags ->
      read_reg_seq_state reg final = read_reg_seq_state reg state).
Proof.
  intros Range Code Present Stack PC Position Top.
  pose (s1 := write_reg_seq_state r14 (machine_address (Z.of_nat top))
    (validation_pc state (entry_pc frame) 339)).
  pose proof (exchange_copy_top nondet layout frame state (Z.of_nat top) ltac:(lia)
    Code Present PC Top) as Step1.
  destruct (exchange_depth nondet layout frame s1 (Z.of_nat top) (Z.of_nat position)
    ltac:(lia) ltac:(lia) ltac:(exchange_code) ltac:(exchange_present)
    ltac:(permute_swap_reads; reflexivity) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; exact Position)) as (f2 & Step2).
  pose (s2 := write_reg_seq_state rflags f2
    (write_reg_seq_state r14 (machine_address (Z.of_nat top - Z.of_nat position))
      (validation_pc s1 (entry_pc frame) 342))).
  destruct (exchange_compare_depth nondet layout frame s2 (Z.of_nat top - Z.of_nat position)
    ltac:(lia) ltac:(exchange_code) ltac:(exchange_present)
    ltac:(permute_swap_reads; reflexivity) ltac:(permute_swap_reads; reflexivity))
    as (f3 & Step3 & Sign).
  pose (s3 := write_reg_seq_state rflags f3 (validation_pc s2 (entry_pc frame) 346)).
  pose (final := validation_pc s3 (entry_pc frame)
    (if 17 <=? Z.of_nat top - Z.of_nat position then 377 else 348)).
  pose proof (exchange_jns nondet layout frame s3 346 29 f3
    (17 <=? Z.of_nat top - Z.of_nat position) ltac:(left; reflexivity)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; reflexivity) Sign) as Step4.
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
  - split; [unfold final, s3, s2, s1, validation_pc; rewrite !register_write_memory; reflexivity|].
    split; [exchange_code|]. split; [exchange_present|]. split; [exchange_stack|].
    split; [permute_swap_reads; reflexivity|]. split; [permute_swap_reads; reflexivity|].
    intros reg NotPC NotDepth NotFlags. permute_swap_reads; reflexivity.
Qed.

Print Assumptions exchange_probe.
Print Assumptions exchange_equal.
Print Assumptions exchange_depth_path.

Lemma exchange_blocked_writes nondet layout (frame : call_frame layout program_bytes)
    initial state output position depth c c1 c2 :
  (position <= 1024)%nat -> 17 <= depth <= 1024 ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 377)) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r14 state = Some (machine_address depth) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c output 4 (Vint (Int.repr (Z.of_nat position))) = Some c1 ->
  Mem.store Mint32 c1 output 8 (Vint (Int.repr (depth - 16))) = Some c2 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 5 state final /\
    machine_cells_related layout c2 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax final = Some (machine_address 1) /\
    exchange_register_frame state final.
Proof.
  intros PositionBound DepthRange Capacity Code Present Stack PC Output Position Depth Related Store1 Store2.
  pose (s1 := stored_bytes_state (validation_pc state (entry_pc frame) 381)
    (machine_address (cell_address (cell_layout layout) output 1))
    (bv_to_bytes 8 (machine_word (Int.repr (Z.of_nat position))))).
  destruct (exchange_output_store nondet layout frame state 377 4 13 output 1
    (Int.repr (Z.of_nat position)) (machine_address (Z.of_nat position)) c c1
    ltac:(cbn; tauto) ltac:(lia) Code Present PC Output Position
    ltac:(change (low_register32 0 (machine_address (Z.of_nat position)) = machine_word (Int.repr (Z.of_nat position)));
      rewrite machine_low32 by (change Int.modulus with 4294967296; lia);
      unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
      reflexivity) Related Store1) as (Step1 & Related1).
  destruct (exchange_excess nondet layout frame s1 depth DepthRange
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; exact Depth)) as (flags & Step2).
  pose (s2 := write_reg_seq_state rflags flags (write_reg_seq_state r14 (machine_address (depth - 16))
    (validation_pc s1 (entry_pc frame) 385))).
  assert (Related2 : machine_cells_related layout c1 (archState.memory (sst s2))).
  { unfold s2, validation_pc. rewrite !register_write_memory. exact Related1. }
  pose (s3 := stored_bytes_state (validation_pc s2 (entry_pc frame) 389)
    (machine_address (cell_address (cell_layout layout) output 2))
    (bv_to_bytes 8 (machine_word (Int.repr (depth - 16))))).
  destruct (exchange_output_store nondet layout frame s2 385 4 14 output 2
    (Int.repr (depth - 16)) (machine_address (depth - 16)) c1 c2
    ltac:(cbn; tauto) ltac:(lia)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; exact Output)
    ltac:(change (read_reg_seq_state r14 s2 = Some (machine_address (depth - 16)));
      permute_swap_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (depth - 16)) = machine_word (Int.repr (depth - 16)));
      rewrite machine_low32 by (change Int.modulus with 4294967296; lia);
      unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
      reflexivity) Related2 Store2) as (Step3 & Related3).
  pose (s4 := write_reg_seq_state rax (machine_address 1) (validation_pc s3 (entry_pc frame) 394)).
  pose proof (exchange_return_one nondet layout frame s3
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)) as Step4.
  pose (final := validation_pc s4 (entry_pc frame) 428).
  pose proof (exchange_jump nondet layout frame s4 394 32 ltac:(cbn; tauto)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)) as Step5.
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step4|exact Step5].
  - split; [unfold final, s4, validation_pc; rewrite !register_write_memory; exact Related3|].
    split; [exchange_code|]. split; [exchange_present|]. split; [exchange_stack|].
    split; [permute_swap_reads; reflexivity|]. split; [permute_swap_reads; reflexivity|exchange_frame_build].
Qed.

Theorem exchange_exhausted nondet layout (frame : call_frame layout program_bytes)
    initial state bd output position top x y c c1 c2 :
  (position <= top <= 1024)%nat -> 17 <= Z.of_nat top - Z.of_nat position ->
  (position < block_words (cell_layout layout) bd)%nat ->
  (top < block_words (cell_layout layout) bd)%nat ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state rsi state = Some (pointer_to_block layout bd) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat position) = Some (Vint x) ->
  Mem.load Mint32 c bd (4 * Z.of_nat top) = Some (Vint y) -> word_equal x y = false ->
  Mem.store Mint32 c output 4 (Vint (Int.repr (Z.of_nat position))) = Some c1 ->
  Mem.store Mint32 c1 output 8 (Vint (Int.repr (Z.of_nat top - Z.of_nat position - 16))) = Some c2 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 13 state final /\
    machine_cells_related layout c2 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax final = Some (machine_address 1) /\
    exchange_register_frame state final.
Proof.
  intros Range Depth PositionCapacity TopCapacity OutputCapacity Code Present Stack PC Data Output
    Position Top Related LoadX LoadY Unequal Store1 Store2.
  destruct (exchange_probe nondet layout frame initial state bd position top x y c
    PositionCapacity TopCapacity Code Present Stack PC Data Position Top Related LoadX LoadY)
    as (s1 & Probe & Memory1 & Code1 & Present1 & Stack1 & PC1 & AX & BX & Frame1).
  rewrite Unequal in PC1.
  destruct (exchange_depth_path nondet layout frame initial s1 position top Range Code1 Present1 Stack1 PC1
    ltac:(exchange_frame_read Frame1; exact Position) ltac:(exchange_frame_read Frame1; exact Top))
    as (s2 & DepthSteps & Memory2 & Code2 & Present2 & Stack2 & PC2 & Depth2 & Registers2).
  assert (Deep : (17 <=? Z.of_nat top - Z.of_nat position) = true) by (apply Z.leb_le; exact Depth).
  rewrite Deep in PC2.
  assert (Frame2 : exchange_register_frame s1 s2).
  { intros reg Outside. apply Registers2; unfold exchange_clobbered in Outside; cbn in Outside; intuition congruence. }
  destruct (exchange_blocked_writes nondet layout frame initial s2 output position
    (Z.of_nat top - Z.of_nat position) c c1 c2 ltac:(lia) ltac:(lia) OutputCapacity
    Code2 Present2 Stack2 PC2
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Output)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Position)
    Depth2 ltac:(rewrite Memory2, Memory1; exact Related) Store1 Store2)
    as (final & Writes & RelatedFinal & CodeFinal & PresentFinal & StackFinal & PCFinal & Return & Frame3).
  exists final. split.
  - eapply instruction_steps_append with (count := 4%nat) (rest := 9%nat); [exact Probe|].
    eapply instruction_steps_append with (count := 4%nat) (rest := 5%nat); eassumption.
  - split; [exact RelatedFinal|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact StackFinal|]. split; [exact PCFinal|]. split; [exact Return|].
    eapply exchange_frame_trans; [exact Frame1|]. eapply exchange_frame_trans; eassumption.
Qed.

Print Assumptions exchange_blocked_writes.
Print Assumptions exchange_exhausted.

Lemma exchange_success_writes nondet layout (frame : call_frame layout program_bytes)
    initial state bd trace output position top count capacity depth x y c c1 c2 c3 c4 :
  (count < capacity <= 2048)%nat -> 1 <= depth <= 16 ->
  (position < block_words (cell_layout layout) bd)%nat ->
  (top < block_words (cell_layout layout) bd)%nat ->
  (count < block_words (cell_layout layout) trace)%nat ->
  (0 < block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 348)) ->
  read_reg_seq_state rsi state = Some (pointer_to_block layout bd) ->
  read_reg_seq_state r9 state = Some (pointer_to_block layout trace) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  read_reg_seq_state r15 state = Some (machine_address (Z.of_nat capacity)) ->
  read_reg_seq_state r14 state = Some (machine_address depth) ->
  read_reg_seq_state rax state = Some (@zero_extend 32 (machine_word x) 64) ->
  read_reg_seq_state rbx state = Some (@zero_extend 32 (machine_word y) 64) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c output 0 = Some (Vint (Int.repr (Z.of_nat count))) ->
  Mem.store Mint32 c bd (4 * Z.of_nat position) (Vint y) = Some c1 ->
  Mem.store Mint32 c1 bd (4 * Z.of_nat top) (Vint x) = Some c2 ->
  Mem.store Mint32 c2 trace (4 * Z.of_nat count) (Vint (Int.repr depth)) = Some c3 ->
  Mem.store Mint32 c3 output 0 (Vint (Int.repr (Z.of_nat count + 1))) = Some c4 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 9 state final /\
    machine_cells_related layout c4 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 398)) /\
    exchange_register_frame state final.
Proof.
  intros CountRange DepthRange PositionCapacity TopCapacity TraceCapacity OutputCapacity Code Present Stack
    PC Data Trace Output Position Top Capacity Depth AX BX Related CountLoad Store1 Store2 Store3 Store4.
  pose (s1 := write_reg_seq_state r11 (machine_address (Z.of_nat count))
    (validation_pc state (entry_pc frame) 351)).
  pose proof (exchange_load_count nondet layout frame state output (Int.repr (Z.of_nat count)) c
    OutputCapacity Code Present PC Output Related CountLoad) as Step1.
  rewrite zero_extend_word_repr in Step1 by (change Int.modulus with 4294967296; lia).
  destruct (exchange_compare_step nondet layout frame s1 351 3 11 15
    (machine_address (Z.of_nat count)) (machine_address (Z.of_nat capacity))
    (Z.of_nat count) (Z.of_nat capacity) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(change (read_reg_seq_state r11 s1 = Some (machine_address (Z.of_nat count)));
      permute_swap_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat count)) = Z_to_bv 32 (Z.of_nat count));
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(change (read_reg_seq_state r15 s1 = Some (machine_address (Z.of_nat capacity)));
      permute_swap_reads; exact Capacity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat capacity)) = Z_to_bv 32 (Z.of_nat capacity));
      apply machine_low32; change Int.modulus with 4294967296; lia))
    as (flags & Step2 & Zero & Sign).
  specialize (Sign ltac:(lia) ltac:(lia)).
  assert (NotFull : (Z.of_nat capacity <=? Z.of_nat count) = false) by (apply Z.leb_gt; lia).
  rewrite NotFull in Sign.
  pose (s2 := write_reg_seq_state rflags flags (validation_pc s1 (entry_pc frame) 354)).
  pose (s3 := validation_pc s2 (entry_pc frame) 356).
  pose proof (exchange_jns nondet layout frame s2 354 40 flags false ltac:(right; left; reflexivity)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; reflexivity) Sign) as Step3.
  assert (Related3 : machine_cells_related layout c (archState.memory (sst s3))).
  { unfold s3, s2, s1, validation_pc. rewrite !register_write_memory. exact Related. }
  pose (s4 := stored_bytes_state (validation_pc s3 (entry_pc frame) 360)
    (machine_address (cell_address (cell_layout layout) bd position)) (bv_to_bytes 8 (machine_word y))).
  destruct (validation_array_store nondet layout frame s3 356 4 3 6 13 bd position y
    (@zero_extend 32 (machine_word y) 64) c c1 ltac:(cbn; tauto) ltac:(discriminate) PositionCapacity
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(apply (normalize_array_address layout s3 6 13 bd position);
      [change (read_reg_seq_state rsi s3 = Some (pointer_to_block layout bd)); permute_swap_reads; exact Data|
       change (read_reg_seq_state r13 s3 = Some (machine_address (Z.of_nat position))); permute_swap_reads; exact Position])
    ltac:(change (read_reg_seq_state rbx s3 = Some (@zero_extend 32 (machine_word y) 64));
      permute_swap_reads; exact BX) ltac:(apply low32_zero_extend) Related3 Store1) as (Step4 & Related4).
  pose (s5 := stored_bytes_state (validation_pc s4 (entry_pc frame) 364)
    (machine_address (cell_address (cell_layout layout) bd top)) (bv_to_bytes 8 (machine_word x))).
  destruct (validation_array_store nondet layout frame s4 360 4 0 6 12 bd top x
    (@zero_extend 32 (machine_word x) 64) c1 c2 ltac:(cbn; tauto) ltac:(discriminate) TopCapacity
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(apply (normalize_array_address layout s4 6 12 bd top);
      [change (read_reg_seq_state rsi s4 = Some (pointer_to_block layout bd)); permute_swap_reads; exact Data|
       change (read_reg_seq_state r12 s4 = Some (machine_address (Z.of_nat top))); permute_swap_reads; exact Top])
    ltac:(change (read_reg_seq_state rax s4 = Some (@zero_extend 32 (machine_word x) 64));
      permute_swap_reads; exact AX) ltac:(apply low32_zero_extend) Related4 Store2) as (Step5 & Related5).
  pose (s6 := stored_bytes_state (validation_pc s5 (entry_pc frame) 368)
    (machine_address (cell_address (cell_layout layout) trace count))
    (bv_to_bytes 8 (machine_word (Int.repr depth)))).
  destruct (validation_array_store nondet layout frame s5 364 4 14 9 11 trace count (Int.repr depth)
    (machine_address depth) c2 c3 ltac:(cbn; tauto) ltac:(discriminate) TraceCapacity
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(apply (normalize_array_address layout s5 9 11 trace count);
      [change (read_reg_seq_state r9 s5 = Some (pointer_to_block layout trace)); permute_swap_reads; exact Trace|
       change (read_reg_seq_state r11 s5 = Some (machine_address (Z.of_nat count))); permute_swap_reads; reflexivity])
    ltac:(change (read_reg_seq_state r14 s5 = Some (machine_address depth)); permute_swap_reads; exact Depth)
    ltac:(change (low_register32 0 (machine_address depth) = machine_word (Int.repr depth));
      rewrite machine_low32 by (change Int.modulus with 4294967296; lia);
      unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
      reflexivity) Related5 Store3) as (Step6 & Related6).
  destruct (exchange_increment_count nondet layout frame s6 (Z.of_nat count) ltac:(lia)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; reflexivity)) as (flags7 & Step7).
  pose (s7 := write_reg_seq_state rflags flags7
    (write_reg_seq_state r11 (machine_address (Z.of_nat count + 1))
      (validation_pc s6 (entry_pc frame) 372))).
  assert (Related7 : machine_cells_related layout c3 (archState.memory (sst s7))).
  { unfold s7, validation_pc. rewrite !register_write_memory. exact Related6. }
  pose (s8 := stored_bytes_state (validation_pc s7 (entry_pc frame) 375)
    (machine_address (cell_address (cell_layout layout) output 0))
    (bv_to_bytes 8 (machine_word (Int.repr (Z.of_nat count + 1))))).
  destruct (exchange_output_store nondet layout frame s7 372 3 11 output 0
    (Int.repr (Z.of_nat count + 1)) (machine_address (Z.of_nat count + 1)) c3 c4
    ltac:(cbn; tauto) OutputCapacity
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)
    ltac:(permute_swap_reads; exact Output)
    ltac:(change (read_reg_seq_state r11 s7 = Some (machine_address (Z.of_nat count + 1)));
      permute_swap_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat count + 1)) = machine_word (Int.repr (Z.of_nat count + 1)));
      rewrite machine_low32 by (change Int.modulus with 4294967296; lia);
      unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
      reflexivity) Related7 Store4) as (Step8 & Related8).
  pose (final := validation_pc s8 (entry_pc frame) 398).
  pose proof (exchange_jump nondet layout frame s8 375 21 ltac:(right; left; reflexivity)
    ltac:(exchange_code) ltac:(exchange_present) ltac:(permute_swap_reads; reflexivity)) as Step9.
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 8%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 7%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 6%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step4|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step5|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step6|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step7|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step8|exact Step9].
  - split; [unfold final, validation_pc; rewrite register_write_memory; exact Related8|].
    split; [exchange_code|]. split; [exchange_present|]. split; [exchange_stack|].
    split; [permute_swap_reads; reflexivity|exchange_frame_build].
Qed.

Theorem exchange_success nondet layout (frame : call_frame layout program_bytes)
    initial state bd trace output position top count capacity x y c c1 c2 c3 c4 :
  (position <= top <= 1024)%nat -> 1 <= Z.of_nat top - Z.of_nat position <= 16 ->
  (count < capacity <= 2048)%nat ->
  (position < block_words (cell_layout layout) bd)%nat ->
  (top < block_words (cell_layout layout) bd)%nat ->
  (count < block_words (cell_layout layout) trace)%nat ->
  (0 < block_words (cell_layout layout) output)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state rsi state = Some (pointer_to_block layout bd) ->
  read_reg_seq_state r9 state = Some (pointer_to_block layout trace) ->
  read_reg_seq_state r10 state = Some (pointer_to_block layout output) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat position)) ->
  read_reg_seq_state r12 state = Some (machine_address (Z.of_nat top)) ->
  read_reg_seq_state r15 state = Some (machine_address (Z.of_nat capacity)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat position) = Some (Vint x) ->
  Mem.load Mint32 c bd (4 * Z.of_nat top) = Some (Vint y) -> word_equal x y = false ->
  Mem.load Mint32 c output 0 = Some (Vint (Int.repr (Z.of_nat count))) ->
  Mem.store Mint32 c bd (4 * Z.of_nat position) (Vint y) = Some c1 ->
  Mem.store Mint32 c1 bd (4 * Z.of_nat top) (Vint x) = Some c2 ->
  Mem.store Mint32 c2 trace (4 * Z.of_nat count)
    (Vint (Int.repr (Z.of_nat top - Z.of_nat position))) = Some c3 ->
  Mem.store Mint32 c3 output 0 (Vint (Int.repr (Z.of_nat count + 1))) = Some c4 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 17 state final /\
    machine_cells_related layout c4 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 398)) /\
    exchange_register_frame state final.
Proof.
  intros Range DepthRange CountRange PositionCapacity TopCapacity TraceCapacity OutputCapacity
    Code Present Stack PC Data Trace Output Position Top Capacity Related LoadX LoadY Unequal
    CountLoad Store1 Store2 Store3 Store4.
  destruct (exchange_probe nondet layout frame initial state bd position top x y c
    PositionCapacity TopCapacity Code Present Stack PC Data Position Top Related LoadX LoadY)
    as (s1 & Probe & Memory1 & Code1 & Present1 & Stack1 & PC1 & AX & BX & Frame1).
  rewrite Unequal in PC1.
  destruct (exchange_depth_path nondet layout frame initial s1 position top Range Code1 Present1 Stack1 PC1
    ltac:(exchange_frame_read Frame1; exact Position) ltac:(exchange_frame_read Frame1; exact Top))
    as (s2 & DepthSteps & Memory2 & Code2 & Present2 & Stack2 & PC2 & Depth2 & Registers2).
  assert (Shallow : (17 <=? Z.of_nat top - Z.of_nat position) = false) by (apply Z.leb_gt; lia).
  rewrite Shallow in PC2.
  assert (Frame2 : exchange_register_frame s1 s2).
  { intros reg Outside. apply Registers2; unfold exchange_clobbered in Outside; cbn in Outside; intuition congruence. }
  destruct (exchange_success_writes nondet layout frame initial s2 bd trace output position top count capacity
    (Z.of_nat top - Z.of_nat position) x y c c1 c2 c3 c4 CountRange DepthRange
    PositionCapacity TopCapacity TraceCapacity OutputCapacity Code2 Present2 Stack2 PC2
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Data)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Trace)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Output)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Position)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Top)
    ltac:(exchange_frame_read Frame2; exchange_frame_read Frame1; exact Capacity)
    Depth2 ltac:(rewrite Registers2 by discriminate; exact AX)
    ltac:(rewrite Registers2 by discriminate; exact BX)
    ltac:(rewrite Memory2, Memory1; exact Related) CountLoad Store1 Store2 Store3 Store4)
    as (final & Writes & RelatedFinal & CodeFinal & PresentFinal & StackFinal & PCFinal & Frame3).
  exists final. split.
  - eapply instruction_steps_append with (count := 4%nat) (rest := 13%nat); [exact Probe|].
    eapply instruction_steps_append with (count := 4%nat) (rest := 9%nat); eassumption.
  - split; [exact RelatedFinal|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact StackFinal|]. split; [exact PCFinal|].
    eapply exchange_frame_trans; [exact Frame1|]. eapply exchange_frame_trans; eassumption.
Qed.

Print Assumptions exchange_success_writes.
Print Assumptions exchange_success.
