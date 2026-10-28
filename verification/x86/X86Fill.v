(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ITree Require Import ITree.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index FixedBlocks.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Address X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments
  X86UsedZero X86ValidationSteps X86Normalize X86FillSteps.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma fill_machine_probe nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output x y c :
  (index < size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bd)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 187)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if word_equal x y then 5%nat else 4%nat) state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if word_equal x y then 255 else 201))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat index)) /\
    read_reg_seq_state r11 final = Some (@zero_extend 32 (machine_word x) 64).
Proof.
  intros Range DataCapacity TargetCapacity Code Present Arguments Stack PC Counter
    Related DataLoad TargetLoad.
  pose proof (core_data _ _ _ _ _ _ _ _ _ Arguments) as Data.
  pose proof (core_target _ _ _ _ _ _ _ _ _ Arguments) as Target.
  pose (s1 := write_reg_seq_state r11 (@zero_extend 32 (machine_word x) 64)
    (validation_pc state (entry_pc frame) 191)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (validation_array_load nondet layout frame state 187 4 11 6 0 bd index x c
      ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia) Code Present PC
      ltac:(apply normalize_array_address; [exact Data|exact Counter]) Related DataLoad). }
  pose (s2 := write_reg_seq_state rbx (@zero_extend 32 (machine_word y) 64)
    (validation_pc s1 (entry_pc frame) 194)).
  assert (Related1 : machine_cells_related layout c (archState.memory (sst s1))).
  { unfold s1, validation_pc. rewrite !register_write_memory. exact Related. }
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { exact (validation_array_load nondet layout frame s1 191 3 3 1 0 bt index y c
      ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia)
      ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
      ltac:(apply normalize_array_address; [normalize_reads; exact Target|normalize_reads; exact Counter])
      Related1 TargetLoad). }
  destruct (fill_compare_step nondet layout frame s2 194 3 11 3
    (@zero_extend 32 (machine_word x) 64) (@zero_extend 32 (machine_word y) 64)
    (Int.unsigned x) (Int.unsigned y) ltac:(left; reflexivity)
    (Int.unsigned_range x) (Int.unsigned_range y)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(normalize_reads; reflexivity) ltac:(apply low32_zero_extend)
    ltac:(normalize_reads; reflexivity) ltac:(apply low32_zero_extend))
    as [f3 [Step3 Zero3]].
  change (@eq_vec 1 (_get_rflags_type_ZF f3) (Z_to_bv 1 0) = negb (word_equal x y)) in Zero3.
  pose (s3 := write_reg_seq_state rflags f3 (validation_pc s2 (entry_pc frame) 197)).
  pose (s4 := validation_pc s3 (entry_pc frame) (if word_equal x y then 199 else 201)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { pose proof (fill_jne_step nondet layout frame s3 197 2 2 f3 (negb (word_equal x y))
      ltac:(left; reflexivity) ltac:(normalize_code) ltac:(normalize_present)
      ltac:(normalize_reads; reflexivity) ltac:(normalize_reads; reflexivity) Zero3) as Jump.
    destruct (word_equal x y); exact Jump. }
  assert (Steps4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 4 state s4).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4]. }
  destruct (word_equal x y) eqn:Choice.
  - pose (s5 := validation_pc s4 (entry_pc frame) 255).
    assert (Step5 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s4 s5).
    { apply fill_skip_jump; [normalize_code|normalize_present|].
      normalize_reads; rewrite ?Choice; reflexivity. }
    exists s5. split.
    + eapply instruction_steps_append with (count := 4%nat) (rest := 1%nat); eassumption.
    + split.
      { unfold s5, s4, s3, s2, s1, validation_pc. rewrite !register_write_memory. reflexivity. }
      split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
      split; [normalize_stack|]. split; [normalize_reads; reflexivity|].
      split; normalize_reads; [exact Counter|reflexivity].
  - exists s4. split; [exact Steps4|]. split.
    { unfold s4, s3, s2, s1, validation_pc. rewrite !register_write_memory. reflexivity. }
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; [normalize_reads; rewrite ?Choice; reflexivity|].
    split; normalize_reads; [exact Counter|reflexivity].
Qed.

Lemma fill_machine_assign nondet layout (frame : call_frame layout program_bytes)
    initial state size index chosen bd bp bt bu trace output c c1 c2 :
  (index < size <= 1024)%nat -> (chosen < size)%nat ->
  (size <= block_words (cell_layout layout) bp)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 243)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat chosen)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c bp (4 * Z.of_nat index) (Vint (Int.repr (Z.of_nat chosen))) = Some c1 ->
  Mem.store Mint32 c1 bu (4 * Z.of_nat chosen) (Vint Int.one) = Some c2 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 2 state final /\
    machine_cells_related layout c2 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 255)) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat index)).
Proof.
  intros Range ChosenRange PermCapacity UsedCapacity Code Present Arguments Stack PC Counter Chosen
    Related StorePerm StoreUsed.
  pose proof (core_permutation _ _ _ _ _ _ _ _ _ Arguments) as Perm.
  pose proof (core_used _ _ _ _ _ _ _ _ _ Arguments) as Used.
  pose (s1 := stored_bytes_state (validation_pc state (entry_pc frame) 247)
    (machine_address (cell_address (cell_layout layout) bp index))
    (bv_to_bytes 8 (machine_word (Int.repr (Z.of_nat chosen))))).
  destruct (validation_array_store nondet layout frame state 243 4 13 2 0 bp index
    (Int.repr (Z.of_nat chosen)) (machine_address (Z.of_nat chosen)) c c1
    ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia) Code Present PC
    ltac:(apply normalize_array_address; [exact Perm|exact Counter]) Chosen
    ltac:(unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
      change (low_register32 0 (machine_address (Z.of_nat chosen)) = Z_to_bv 32 (Z.of_nat chosen));
      apply machine_low32; change Int.modulus with 4294967296; lia)
    Related StorePerm) as [Step1 Related1].
  pose (s2 := stored_bytes_state (validation_pc s1 (entry_pc frame) 255)
    (machine_address (cell_address (cell_layout layout) bu chosen))
    (bv_to_bytes 8 (machine_word Int.one))).
  destruct (fill_mark_used nondet layout frame s1 bu chosen c1 c2 ltac:(lia)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(apply normalize_array_address; [normalize_reads; exact Used|normalize_reads; exact Chosen])
    Related1 StoreUsed) as [Step2 Related2].
  exists s2. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); eassumption.
  - split; [exact Related2|]. split; [normalize_code|]. split; [normalize_present|].
    split; [normalize_arguments|]. split; [normalize_stack|].
    split; normalize_reads; [reflexivity|exact Counter].
Qed.

Lemma fill_machine_next nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output :
  (index < size <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 255)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 3 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 262 else 187))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range Code Present Arguments Stack PC Counter.
  destruct (core_size _ _ _ _ _ _ _ _ _ Arguments) as [size_old [SizeRead SizeLow]].
  assert (SizeLow32 : low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size)).
  { change (bv_extract 0 32 size_old = Z_to_bv 32 (Z.of_nat size)).
    rewrite SizeLow. unfold machine_word. rewrite Int.unsigned_repr; [reflexivity|].
    change Int.max_unsigned with 4294967295. lia. }
  destruct (fill_increment nondet layout frame state index ltac:(lia) Code Present PC Counter)
    as [f1 Step1].
  pose (s1 := write_reg_seq_state rflags f1
    (write_reg_seq_state rax (machine_address (Z.of_nat (S index)))
      (validation_pc state (entry_pc frame) 258))).
  destruct (fill_compare_step nondet layout frame s1 258 2 0 7
    (machine_address (Z.of_nat (S index))) size_old (Z.of_nat (S index)) (Z.of_nat size)
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(normalize_reads; reflexivity)
    ltac:(apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(normalize_reads; exact SizeRead) SizeLow32) as [f2 [Step2 Zero2]].
  pose (s2 := write_reg_seq_state rflags f2 (validation_pc s1 (entry_pc frame) 260)).
  pose (s3 := validation_pc s2 (entry_pc frame)
    (if Z.of_nat (S index) =? Z.of_nat size then 262 else 187)).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3).
  { pose proof (fill_jne_step nondet layout frame s2 260 181 (-75) f2
      (negb (Z.of_nat (S index) =? Z.of_nat size)) ltac:(right; left; reflexivity)
      ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
      ltac:(normalize_reads; reflexivity) Zero2) as Jump.
    destruct (Z.of_nat (S index) =? Z.of_nat size); exact Jump. }
  exists s3. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step2|exact Step3].
  - split.
    { unfold s3, s2, s1, validation_pc. rewrite !register_write_memory. reflexivity. }
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; normalize_reads; reflexivity.
Qed.
Theorem fill_preheader nondet layout (frame : call_frame layout program_bytes)
    initial state size bd bp bt bu trace output :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 185)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 187)) /\
    read_reg_seq_state rax final = Some (machine_address 0).
Proof.
  intros Code Present Arguments Stack PC.
  destruct (Present rax) as [old_ax OldAX]. destruct (Present rflags) as [flags Flags].
  pose (final := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state rax (Z_to_bv 64 0) (validation_pc state (entry_pc frame) 187))).
  exists final. split.
  - eapply framed_instruction with (offset := 185) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0)));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 185 + 2) with (entry_pc frame + 187) by lia.
      apply (execute_xor32_self nondet 0 _ old_ax flags).
      * discriminate.
      * change (read_reg_seq_state rax
          (write_reg_seq_state rip (machine_address (entry_pc frame + 187)) state) = Some old_ax).
        rewrite register_read_frame by discriminate. exact OldAX.
      * rewrite register_read_frame by discriminate. exact Flags.
  - split.
    { unfold final, validation_pc. rewrite !register_write_memory. reflexivity. }
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; normalize_reads; reflexivity.
Qed.


Print Assumptions fill_machine_probe.
Print Assumptions fill_machine_assign.
Print Assumptions fill_machine_next.
Print Assumptions fill_preheader.

Theorem fill_equal_iteration nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output x y c :
  (index < size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bd)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 187)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  word_equal x y = true ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 8 state final /\
    machine_cells_related layout c (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 262 else 187))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range DataCapacity TargetCapacity Code Present Arguments Stack PC Counter
    Related DataLoad TargetLoad Equal.
  destruct (fill_machine_probe nondet layout frame initial state size index bd bp bt bu trace output
    x y c Range DataCapacity TargetCapacity Code Present Arguments Stack PC Counter Related
    DataLoad TargetLoad)
    as [branch [Probe [MemoryBranch [CodeBranch [PresentBranch [ArgumentsBranch
      [StackBranch [PCBranch [CounterBranch ValueBranch]]]]]]]]].
  rewrite Equal in Probe, PCBranch.
  destruct (fill_machine_next nondet layout frame initial branch size index bd bp bt bu trace output
    Range CodeBranch PresentBranch ArgumentsBranch StackBranch PCBranch CounterBranch)
    as [final [Next [MemoryFinal Result]]].
  exists final. split.
  - eapply instruction_steps_append with (count := 5%nat) (rest := 3%nat); eassumption.
  - split; [rewrite MemoryFinal, MemoryBranch; exact Related|exact Result].
Qed.

Print Assumptions fill_equal_iteration.
