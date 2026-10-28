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
  X86Address X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments
  X86UsedZero X86ValidationSteps X86Validation X86SearchSteps.
Import ListNotations.
Open Scope Z_scope.

Definition search_clobbered : list Arch.reg :=
  [(rip : Arch.reg); (rbx : Arch.reg); (r13 : Arch.reg); (rflags : Arch.reg)].

Definition search_frame before after : Prop :=
  archState.memory (sst after) = archState.memory (sst before) /\
  forall reg : Arch.reg, ~ In reg search_clobbered ->
    read_reg_seq_state reg after = read_reg_seq_state reg before.

Lemma search_frame_refl state : search_frame state state.
Proof. split; reflexivity. Qed.

Lemma search_frame_trans first middle final :
  search_frame first middle -> search_frame middle final -> search_frame first final.
Proof.
  intros [Memory1 Registers1] [Memory2 Registers2]. split; [congruence|].
  intros reg Outside. rewrite Registers2, Registers1 by exact Outside. reflexivity.
Qed.

Lemma search_frame_write before after (reg : Arch.reg) value :
  In reg search_clobbered -> search_frame before after ->
  search_frame before (write_reg_seq_state reg value after).
Proof.
  intros Inside [Memory Registers]. split.
  - rewrite register_write_memory. exact Memory.
  - intros other Outside. rewrite register_read_frame by congruence.
    apply Registers, Outside.
Qed.

Lemma search_frame_arguments layout size bd bp bt bu trace output before after :
  search_frame before after -> core_arguments layout size bd bp bt bu trace output before ->
  core_arguments layout size bd bp bt bu trace output after.
Proof.
  intros [Memory Registers] Arguments.
  apply (core_arguments_frame _ _ _ _ _ _ _ _ before after Arguments).
  intros reg Inside. apply Registers. unfold argument_registers in Inside.
  repeat destruct Inside as [<-|Inside]; try contradiction;
    unfold search_clobbered; cbn; intuition discriminate.
Qed.

Lemma search_frame_stack layout (frame : call_frame layout program_bytes) initial before after :
  search_frame before after -> call_stack layout frame initial before ->
  call_stack layout frame initial after.
Proof.
  intros [Memory Registers] Stack.
  apply (call_stack_same_memory layout frame initial before after Stack).
  - apply Registers. unfold search_clobbered; cbn; intuition discriminate.
  - apply Registers. unfold search_clobbered; cbn; intuition discriminate.
  - exact Memory.
Qed.

Ltac search_frame_build :=
  validation_states;
  repeat match goal with
  | |- search_frame _ (write_reg_seq_state _ _ _) =>
      apply search_frame_write; [unfold search_clobbered; cbn; tauto|]
  end; apply search_frame_refl.

Definition search_word_match source target flag :=
  andb (Int.unsigned flag =? 0) (Int.unsigned source =? Int.unsigned target).

Theorem search_probe nondet layout (frame : call_frame layout program_bytes)
    state index bt bu source source_old target flag c :
  (index < block_words (cell_layout layout) bt)%nat ->
  (index < block_words (cell_layout layout) bu)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 204)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state r11 state = Some source_old ->
  low_register32 11 source_old = machine_word source ->
  read_reg_seq_state rcx state = Some (pointer_to_block layout bt) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout bu) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bu (4 * Z.of_nat index) = Some (Vint flag) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint target) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if search_word_match source target flag then 233 else 224))) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat index)).
Proof.
  intros CT CU Code Present PC Index Source SourceLow Target Used Related FlagLoad TargetLoad.
  pose (s1 := write_reg_seq_state rbx (@zero_extend 32 (machine_word flag) 64)
    (validation_pc state (entry_pc frame) 208)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (validation_array_load nondet layout frame state 204 4 3 8 13 bu index flag c
      ltac:(unfold array_load_sites; cbn; tauto) ltac:(discriminate) CU Code Present PC
      ltac:(apply validation_scaled_address; [exact Used|exact Index]) Related FlagLoad). }
  destruct (search_compare_zero nondet layout frame s1 208 3 3
    (@zero_extend 32 (machine_word flag) 64) (Int.unsigned flag)
    ltac:(left; reflexivity) (Int.unsigned_range flag)
    ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; reflexivity)
    ltac:(change (@subrange_vec_dec 64 (@zero_extend 32 (machine_word flag) 64) 31 0 = machine_word flag);
      apply low32_zero_extend)) as [f2 [Step2 Zero2]].
  pose (s2 := write_reg_seq_state rflags f2 (validation_pc s1 (entry_pc frame) 211)).
  pose (s3 := validation_pc s2 (entry_pc frame)
    (if Int.unsigned flag =? 0 then 213 else 224)).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3).
  { pose proof (search_jne_step nondet layout frame s2 211 11 11 f2
      (negb (Int.unsigned flag =? 0)) ltac:(left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero2) as Jump.
    destruct (Int.unsigned flag =? 0); exact Jump. }
  assert (Steps3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 3 state s3).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step2|exact Step3]. }
  destruct (Int.unsigned flag =? 0) eqn:Free.
  - pose (s4 := write_reg_seq_state rbx (@zero_extend 32 (machine_word target) 64)
      (validation_pc s3 (entry_pc frame) 217)).
    assert (Related3 : machine_cells_related layout c (archState.memory (sst s3))).
    { validation_states. rewrite !register_write_memory. exact Related. }
    assert (Code3 : code_at s3 (entry_pc frame) program_bytes) by validation_code.
    assert (Present3 : registers_present s3) by validation_present.
    assert (PC3 : read_reg_seq_state rip s3 = Some (machine_address (entry_pc frame + 213))).
    { validation_reads. try rewrite Free. reflexivity. }
    assert (Address3 : scaled_address (register_values_of s3) 1 13 =
      machine_address (cell_address (cell_layout layout) bt index)).
    { apply validation_scaled_address.
      - validation_reads. exact Target.
      - validation_reads. exact Index. }
    assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s3 s4).
    { exact (validation_array_load nondet layout frame s3 213 4 3 1 13 bt index target c
        ltac:(unfold array_load_sites; cbn; tauto) ltac:(discriminate) CT
        Code3 Present3 PC3 Address3 Related3 TargetLoad). }
    destruct (search_compare_step nondet layout frame s4 217 3 11 3 source_old
      (@zero_extend 32 (machine_word target) 64) (Int.unsigned source) (Int.unsigned target)
      ltac:(left; reflexivity) (Int.unsigned_range source) (Int.unsigned_range target)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; exact Source) SourceLow ltac:(validation_reads; reflexivity)
      ltac:(change (@subrange_vec_dec 64 (@zero_extend 32 (machine_word target) 64) 31 0 = machine_word target);
        apply low32_zero_extend)) as [f5 [Step5 Zero5]].
    pose (s5 := write_reg_seq_state rflags f5 (validation_pc s4 (entry_pc frame) 220)).
    pose (s6 := validation_pc s5 (entry_pc frame)
      (if Int.unsigned source =? Int.unsigned target then 222 else 224)).
    assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s5 s6).
    { pose proof (search_jne_step nondet layout frame s5 220 2 2 f5
        (negb (Int.unsigned source =? Int.unsigned target)) ltac:(right; left; reflexivity)
        ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
        ltac:(validation_reads; reflexivity) Zero5) as Jump.
      destruct (Int.unsigned source =? Int.unsigned target); exact Jump. }
    assert (Steps6 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 6 state s6).
    { eapply instruction_steps_append with (count := 3%nat) (rest := 3%nat); [exact Steps3|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step4|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step5|exact Step6]. }
    destruct (Int.unsigned source =? Int.unsigned target) eqn:Match.
    + pose (s7 := validation_pc s6 (entry_pc frame) 233).
      assert (Step7 : instruction_steps (sail_tiny_x86_sem nondet)
        (return_condition (machine_address (return_pc frame))) 1 s6 s7).
      { apply search_match_jump; [validation_code|validation_present|].
        validation_reads. try rewrite Match. reflexivity. }
      exists 7%nat, s7. split.
      * eapply instruction_steps_append with (count := 6%nat) (rest := 1%nat);
          [exact Steps6|exact Step7].
      * split; [search_frame_build|]. split; [validation_code|].
        split; [validation_present|]. split.
        -- validation_reads. unfold search_word_match. rewrite Free, Match. reflexivity.
        -- validation_reads. exact Index.
    + exists 6%nat, s6. split; [exact Steps6|].
      split; [search_frame_build|]. split; [validation_code|].
      split; [validation_present|]. split.
      * validation_reads. unfold search_word_match. rewrite Free, Match. reflexivity.
      * validation_reads. exact Index.
  - exists 3%nat, s3. split; [exact Steps3|].
    split; [search_frame_build|]. split; [validation_code|].
    split; [validation_present|]. split.
    + validation_reads. unfold search_word_match. rewrite Free. reflexivity.
    + validation_reads. exact Index.
Qed.

Print Assumptions search_probe.
