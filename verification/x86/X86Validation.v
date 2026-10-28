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
  X86UsedZero X86ValidationSteps.
Import ListNotations.
Open Scope Z_scope.

Lemma validation_scaled_address state base index layout b k :
  read_reg_seq_state (Values.reg (gpr_reference base)) state =
    Some (Values.from_ty (gpr_reference base) (pointer_to_block layout b)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state =
    Some (Values.from_ty (gpr_reference index) (machine_address (Z.of_nat k))) ->
  scaled_address (register_values_of state) base index =
    machine_address (cell_address (cell_layout layout) b k).
Proof.
  intros Base Index. unfold scaled_address, scaled_gprs, gpr64.
  rewrite (register_value_known _ _ _ Base), (register_value_known _ _ _ Index),
    !gpr_reference_inverse. apply scaled_cell_address.
Qed.

Ltac validation_states :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold validation_pc.

Ltac validation_reads :=
  validation_states;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Ltac validation_code :=
  validation_states;
  repeat match goal with
  | |- code_at (write_reg_seq_state _ _ _) _ _ => apply code_at_register_write
  | |- code_at (stored_bytes_state _ _ _) _ _ =>
    apply code_preserved_cell_store; [|lia]
  end; assumption.

Ltac validation_present :=
  validation_states;
  repeat match goal with
  | |- registers_present (write_reg_seq_state _ _ _) => apply registers_present_write
  | |- registers_present (stored_bytes_state _ _ _) => apply registers_present_store
  end; assumption.

Theorem validation_iteration nondet layout (frame : call_frame layout program_bytes)
    initial state size index destination bd bp bt bu trace output value c c1 c2 :
  (index < size <= 1024)%nat -> (destination < size)%nat ->
  (size <= block_words (cell_layout layout) bd)%nat ->
  (size <= block_words (cell_layout layout) bp)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 89)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bp (4 * Z.of_nat index) = Some (Vint (Int.repr (Z.of_nat destination))) ->
  Mem.load Mint32 c bu (4 * Z.of_nat destination) = Some (Vint Int.zero) ->
  Mem.store Mint32 c bu (4 * Z.of_nat destination) (Vint Int.one) = Some c1 ->
  Mem.load Mint32 c1 bd (4 * Z.of_nat index) = Some (Vint value) ->
  Mem.store Mint32 c1 bt (4 * Z.of_nat destination) (Vint value) = Some c2 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if Z.of_nat (S index) =? Z.of_nat size then 15%nat else 14%nat) state final /\
    machine_cells_related layout c2 (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 147 else 89))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range Destination DataCapacity PermCapacity TargetCapacity UsedCapacity
    Code Present Arguments Stack PC Counter Related PermLoad UsedLoad UsedStore DataLoad TargetStore.
  destruct Arguments as [[size_old [SizeRead SizeLow]] Data Perm Target Used Trace Output].
  assert (SizeLow32 : low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size)).
  { change (bv_extract 0 32 size_old = Z_to_bv 32 (Z.of_nat size)).
    rewrite SizeLow. unfold machine_word. rewrite Int.unsigned_repr; [reflexivity|].
    change Int.max_unsigned with 4294967295. lia. }
  pose (s1 := write_reg_seq_state r11 (machine_address (Z.of_nat destination))
    (validation_pc state (entry_pc frame) 93)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { pose proof (validation_array_load nondet layout frame state 89 4 11 2 0 bp index
      (Int.repr (Z.of_nat destination)) c ltac:(left; reflexivity) ltac:(discriminate)
      ltac:(lia) Code Present PC
      ltac:(apply validation_scaled_address; [exact Perm|exact Counter]) Related PermLoad) as Load.
    unfold gpr32_written in Load.
    change (Values.from_ty (gpr_reference 11)
      (@zero_extend 32 (machine_word (Int.repr (Z.of_nat destination))) 64))
      with (@zero_extend 32 (machine_word (Int.repr (Z.of_nat destination))) 64) in Load.
    rewrite zero_extend_word_repr in Load by (change Int.modulus with 4294967296; lia).
    exact Load. }
  destruct (validation_compare_zero nondet layout frame s1 93 4 11
    (machine_address (Z.of_nat destination)) (Z.of_nat destination)
    ltac:(left; reflexivity) ltac:(lia) ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat destination)) = Z_to_bv 32 (Z.of_nat destination));
      apply machine_low32; change Int.modulus with 4294967296; lia))
    as [f2 [Step2 [Sign2 Zero2]]].
  pose (s2 := write_reg_seq_state rflags f2 (validation_pc s1 (entry_pc frame) 97)).
  pose (s3 := validation_pc s2 (entry_pc frame) 104).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3).
  { exact (validation_jns nondet layout frame s2 97 5 f2 true ltac:(left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Sign2). }
  destruct (validation_compare_size nondet layout frame s3 104 3 11
    (machine_address (Z.of_nat destination)) size_old (Z.of_nat destination) (Z.of_nat size)
    ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat destination)) = Z_to_bv 32 (Z.of_nat destination));
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; exact SizeRead) SizeLow32) as [f4 [Step4 [Sign4 Zero4]]].
  assert (Negative : (Z.of_nat size <=? Z.of_nat destination) = false) by (apply Z.leb_gt; lia).
  rewrite Negative in Sign4.
  pose (s4 := write_reg_seq_state rflags f4 (validation_pc s3 (entry_pc frame) 107)).
  pose (s5 := validation_pc s4 (entry_pc frame) 109).
  assert (Step5 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s4 s5).
  { exact (validation_jns nondet layout frame s4 107 33 f4 false ltac:(right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Sign4). }
  pose (s6 := write_reg_seq_state rbx (machine_address 0) (validation_pc s5 (entry_pc frame) 113)).
  assert (Code5 : code_at s5 (entry_pc frame) program_bytes) by validation_code.
  assert (Present5 : registers_present s5) by validation_present.
  assert (PC5 : read_reg_seq_state rip s5 = Some (machine_address (entry_pc frame + 109)))
    by (validation_reads; reflexivity).
  assert (Address5 : scaled_address (register_values_of s5) 8 11 =
    machine_address (cell_address (cell_layout layout) bu destination)).
  { apply validation_scaled_address; [validation_reads; exact Used|validation_reads; reflexivity]. }
  assert (Related5 : machine_cells_related layout c (archState.memory (sst s5))) by exact Related.
  assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s5 s6).
  { exact (validation_array_load nondet layout frame s5 109 4 3 8 11 bu destination Int.zero c
      ltac:(right; left; reflexivity) ltac:(discriminate) ltac:(lia)
      Code5 Present5 PC5 Address5 Related5 UsedLoad). }
  destruct (validation_compare_zero nondet layout frame s6 113 3 3 (machine_address 0) 0
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; reflexivity) ltac:(reflexivity))
    as [f7 [Step7 [Sign7 Zero7]]].
  pose (s7 := write_reg_seq_state rflags f7 (validation_pc s6 (entry_pc frame) 116)).
  pose (s8 := validation_pc s7 (entry_pc frame) 118).
  assert (Step8 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s7 s8).
  { exact (validation_jne nondet layout frame s7 116 24 24 f7 false ltac:(left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero7). }
  pose (s9 := stored_bytes_state (validation_pc s8 (entry_pc frame) 126)
    (machine_address (cell_address (cell_layout layout) bu destination))
    (bv_to_bytes 8 (machine_word Int.one))).
  destruct (validation_mark_used nondet layout frame s8 bu destination c c1 ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(apply validation_scaled_address; [validation_reads; exact Used|validation_reads; reflexivity])
    Related UsedStore) as [Step9 Related9].
  pose (s10 := write_reg_seq_state rbx (@zero_extend 32 (machine_word value) 64)
    (validation_pc s9 (entry_pc frame) 129)).
  assert (Step10 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s9 s10).
  { exact (validation_array_load nondet layout frame s9 126 3 3 6 0 bd index value c1
      ltac:(right; right; left; reflexivity) ltac:(discriminate) ltac:(lia)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(apply validation_scaled_address; [validation_reads; exact Data|validation_reads; exact Counter])
      Related9 DataLoad). }
  pose (s11 := stored_bytes_state (validation_pc s10 (entry_pc frame) 133)
    (machine_address (cell_address (cell_layout layout) bt destination))
    (bv_to_bytes 8 (machine_word value))).
  assert (Related10 : machine_cells_related layout c1 (archState.memory (sst s10))).
  { unfold s10, validation_pc. rewrite !register_write_memory. exact Related9. }
  destruct (validation_array_store nondet layout frame s10 129 4 3 1 11 bt destination value
    (@zero_extend 32 (machine_word value) 64) c1 c2 ltac:(left; reflexivity) ltac:(discriminate)
    ltac:(lia) ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(apply validation_scaled_address; [validation_reads; exact Target|validation_reads; reflexivity])
    ltac:(validation_reads; reflexivity) ltac:(apply low32_zero_extend) Related10 TargetStore)
    as [Step11 Related11].
  destruct (validation_increment nondet layout frame s11 index ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; exact Counter)) as [f12 Step12].
  pose (s12 := write_reg_seq_state rflags f12
    (write_reg_seq_state rax (machine_address (Z.of_nat (S index))) (validation_pc s11 (entry_pc frame) 136))).
  destruct (validation_compare_size nondet layout frame s12 136 2 0
    (machine_address (Z.of_nat (S index))) size_old (Z.of_nat (S index)) (Z.of_nat size)
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(validation_code) ltac:(validation_present)
    ltac:(validation_reads; reflexivity) ltac:(validation_reads; reflexivity)
    ltac:(apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; exact SizeRead) SizeLow32) as [f13 [Step13 [Sign13 Zero13]]].
  pose (s13 := write_reg_seq_state rflags f13 (validation_pc s12 (entry_pc frame) 138)).
  pose (s14 := validation_pc s13 (entry_pc frame)
    (if Z.of_nat (S index) =? Z.of_nat size then 140 else 89)).
  assert (Step14 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s13 s14).
  { pose proof (validation_jne nondet layout frame s13 138 205 (-51) f13
      (negb (Z.of_nat (S index) =? Z.of_nat size)) ltac:(right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero13) as Jump.
    destruct (Z.of_nat (S index) =? Z.of_nat size); exact Jump. }
  assert (Steps14 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 14 state s14).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 13%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 12%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 11%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 10%nat); [exact Step4|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 9%nat); [exact Step5|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 8%nat); [exact Step6|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 7%nat); [exact Step7|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 6%nat); [exact Step8|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step9|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step10|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step11|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step12|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step13|exact Step14]. }
  assert (Related14 : machine_cells_related layout c2 (archState.memory (sst s14))).
  { unfold s14, s13, s12, validation_pc. rewrite !register_write_memory. exact Related11. }
  assert (Arguments14 : core_arguments layout size bd bp bt bu trace output s14).
  { apply (core_arguments_frame layout size bd bp bt bu trace output state).
    - constructor; try assumption. exists size_old. split; assumption.
    - intros reg Inside. unfold argument_registers in Inside.
      repeat destruct Inside as [<-|Inside]; try contradiction; validation_reads; reflexivity. }
  assert (Stack14 : call_stack layout frame initial s14).
  { apply (call_stack_preserved layout frame initial state s14 Stack).
    - validation_reads. reflexivity.
    - validation_reads. reflexivity.
    - intros stack Low High. validation_states.
      repeat first [rewrite register_write_read_memory |
        rewrite (stack_read_cell_store layout program_bytes frame) by lia]. reflexivity. }
  destruct (Z.of_nat (S index) =? Z.of_nat size) eqn:Last.
  - pose (final := validation_pc s14 (entry_pc frame) 147).
    assert (Exit : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s14 final).
    { apply validation_exit_jump; [validation_code|validation_present|].
      unfold s14, validation_pc. rewrite ?Last. apply register_read_written. }
    exists final. split.
    + eapply instruction_steps_append with (count := 14%nat) (rest := 1%nat); eassumption.
    + split.
      { unfold final, validation_pc. rewrite register_write_memory. exact Related14. }
      split; [validation_code|]. split; [validation_present|].
      split.
      * apply core_arguments_write; [cbn; intuition discriminate|exact Arguments14].
      * split.
        -- apply call_stack_register_write; [exact Stack14|discriminate|discriminate].
        -- split; [validation_reads; reflexivity|].
           validation_reads. reflexivity.
  - exists s14. split; [exact Steps14|]. split; [exact Related14|].
    split; [validation_code|]. split; [validation_present|].
    split; [exact Arguments14|]. split; [exact Stack14|].
    split; validation_reads; rewrite ?Last; reflexivity.
Qed.

Print Assumptions validation_iteration.
