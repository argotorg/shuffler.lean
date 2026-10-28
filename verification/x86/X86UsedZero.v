(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
Require Import CellRelation Initialize.
From X86 Require Import X86Layout X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore X86MemoryFrame
  X86Prologue X86StackFrame.
Import ListNotations.
Open Scope Z_scope.

Definition used_zero_pc state base offset :=
  write_reg_seq_state rip (machine_address (base + offset)) state.

Definition used_zero_store layout (frame : call_frame layout program_bytes) used index state :=
  stored_bytes_state (used_zero_pc state (entry_pc frame) 80)
    (machine_address (cell_address (cell_layout layout) used index))
    (bv_to_bytes 8 (machine_word Int.zero)).

Lemma machine_low32 index :
  0 <= index < Int.modulus ->
  low_register32 0 (machine_address index) = Z_to_bv 32 index.
Proof.
  intro Range. rewrite <- zero_extend_word_repr by exact Range.
  change (@subrange_vec_dec 64 (@zero_extend 32 (machine_word (Int.repr index)) 64) 31 0 =
    Z_to_bv 32 index).
  rewrite low32_zero_extend. unfold machine_word.
  rewrite Int.unsigned_repr; [reflexivity|unfold Int.max_unsigned; lia].
Qed.

Lemma add32_words first second :
  @add_vec 32 (Z_to_bv 32 first) (Z_to_bv 32 second) = Z_to_bv 32 (first + second).
Proof.
  change (bv_add (Z_to_bv 32 first) (Z_to_bv 32 second) = Z_to_bv 32 (first + second)).
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp. reflexivity.
Qed.

Lemma zero_extend32_word index :
  0 <= index < Int.modulus ->
  @zero_extend 32 (Z_to_bv 32 index) 64 = machine_address index.
Proof.
  intro Range. rewrite <- zero_extend_word_repr by exact Range.
  unfold machine_word. rewrite Int.unsigned_repr; [reflexivity|unfold Int.max_unsigned; lia].
Qed.

Theorem used_zero_store_step nondet layout (frame : call_frame layout program_bytes)
    used index state c c' :
  (index < block_words (cell_layout layout) used)%nat ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 72)) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout used) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c used (4 * Z.of_nat index) (Vint Int.zero) = Some c' ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (used_zero_store layout frame used index state) /\
  machine_cells_related layout c'
    (archState.memory (sst (used_zero_store layout frame used index state))).
Proof.
  intros Index Code Present PC Base Counter Related Store. split.
  - eapply framed_instruction with (offset := 72) (size := 8)
      (instruction := MOV (32,
        rm_MEM (machine_address (cell_address (cell_layout layout) used index)),
        rmi_IMM (IMM32 (machine_word Int.zero))));
      [exact Code|exact Present|exact PC| | |].
    + apply (array_immediate_instruction 72 8 0 8 0). left. reflexivity.
    + rewrite (decode_array_immediate nondet _ _ 72 8 0 8 0 ltac:(left; reflexivity)).
      unfold scaled_address, scaled_gprs.
      change (Some (MOV (32,
        rm_MEM (@add_vec 64 (register_values_of state r8)
          (@shiftl 64 (register_values_of state rax) 2)),
        rmi_IMM (IMM32 (Z_to_bv 32 0)))) =
        Some (MOV (32, rm_MEM (machine_address (cell_address (cell_layout layout) used index)),
          rmi_IMM (IMM32 (machine_word Int.zero))))).
      rewrite (register_value_known state r8 _ Base),
        (register_value_known state rax _ Counter), scaled_cell_address. reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 72 + 8) with (entry_pc frame + 80) by lia.
      apply execute_mov32_immediate_store. rewrite register_write_memory.
      exact (proj1 (Related used index Index)).
  - unfold used_zero_store, used_zero_pc. rewrite stored_bytes_memory, register_write_memory.
    eapply machine_cells_related_store; eassumption.
Qed.

Record used_zero_frame layout (frame : call_frame layout program_bytes)
    (initial final : seq_state) : Prop := {
  used_zero_other : forall reg, reg <> rip -> reg <> rflags -> reg <> rax ->
    read_reg_seq_state reg final = read_reg_seq_state reg initial;
  used_zero_stack : forall stack,
    entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
    read_mem_seq_state 8 (machine_address stack) final =
      read_mem_seq_state 8 (machine_address stack) initial
}.

Lemma used_zero_frame_trans layout (frame : call_frame layout program_bytes) first middle last :
  used_zero_frame layout frame first middle -> used_zero_frame layout frame middle last ->
  used_zero_frame layout frame first last.
Proof.
  intros [FirstRegs FirstStack] [LastRegs LastStack]. constructor.
  - intros reg PC Flags AX. rewrite LastRegs, FirstRegs; auto.
  - intros stack Low High. rewrite LastStack, FirstStack; auto.
Qed.

Ltac unfold_used_states :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold used_zero_store, used_zero_pc.

Ltac used_reads :=
  unfold_used_states;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Ltac used_code :=
  unfold_used_states;
  repeat first [apply code_at_register_write |
    apply code_preserved_cell_store; [|lia]]; assumption.

Ltac used_present :=
  unfold_used_states;
  repeat first [apply registers_present_write | apply registers_present_store]; assumption.

Theorem used_zero_iteration nondet layout (frame : call_frame layout program_bytes)
    used size index old state c c' :
  (index < size <= 1024)%nat -> (size <= block_words (cell_layout layout) used)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 72)) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout used) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 (Z.of_nat size) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c used (4 * Z.of_nat index) (Vint Int.zero) = Some c' ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 4 state final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 87 else 72))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))) /\
    used_zero_frame layout frame state final.
Proof.
  intros Range Capacity Code Present PC Base Counter Old Low Related Store.
  pose (s1 := used_zero_store layout frame used index state).
  destruct (used_zero_store_step nondet layout frame used index state c c'
    ltac:(lia) Code Present PC Base Counter Related Store) as [Step1 Related1].
  destruct (Present rflags) as [flags Flags].
  pose (next := used_zero_pc s1 (entry_pc frame) 83).
  assert (CounterNext : read_reg_seq_state rax next = Some (machine_address (Z.of_nat index)))
    by (used_reads; exact Counter).
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags) by (used_reads; exact Flags).
  destruct (execute_add32_imm8 nondet 0 next (machine_address (Z.of_nat index)) flags
    (Z_to_bv 8 1) ltac:(discriminate) CounterNext FlagsNext)
    as [overflow [carry [auxiliary [parity Add]]]].
  cbn beta zeta in Add. rewrite machine_low32 in Add by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Add.
  rewrite add32_words in Add.
  replace (Z.of_nat index + 1) with (Z.of_nat (S index)) in Add by lia.
  pose (f1 := result_flags flags (sign_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) overflow carry
    (zero_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) auxiliary parity).
  pose (s2 := write_reg_seq_state rflags f1
    (write_reg_seq_state rax (machine_address (Z.of_nat (S index))) next)).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { eapply framed_instruction with (offset := 80) (size := 3)
      (instruction := ADD (false, 32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM8 (Z_to_bv 8 1)))).
    - used_code.
    - used_present.
    - used_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 80 + 3) with (entry_pc frame + 83) by lia.
      unfold gpr32_written in Add.
      change (sail_run nondet
        (Tiny_x86.execute (ADD (false, 32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM8 (Z_to_bv 8 1)))))
        next = Exec.make [(write_reg_seq_state rflags f1
          (write_reg_seq_state rax (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (S index))) 64) next), tt)] []) in Add.
      rewrite zero_extend32_word in Add by (change Int.modulus with 4294967296; lia).
      exact Add. }
  pose (cmp_state := used_zero_pc s2 (entry_pc frame) 85).
  assert (AXCompare : read_reg_seq_state rax cmp_state = Some (machine_address (Z.of_nat (S index))))
    by (used_reads; reflexivity).
  assert (DICompare : read_reg_seq_state rdi cmp_state = Some old) by (used_reads; exact Old).
  assert (FlagsCompare : read_reg_seq_state rflags cmp_state = Some f1) by (used_reads; reflexivity).
  destruct (execute_cmp32_registers nondet 0 7 cmp_state
    (machine_address (Z.of_nat (S index))) old f1 AXCompare DICompare FlagsCompare)
    as [overflow2 [carry2 [auxiliary2 [parity2 Compare]]]].
  cbn beta zeta in Compare. rewrite machine_low32 in Compare by (change Int.modulus with 4294967296; lia).
  rewrite Low in Compare.
  pose (difference := @sub_vec 32 (Z_to_bv 32 (Z.of_nat (S index))) (Z_to_bv 32 (Z.of_nat size))).
  pose (f2 := result_flags f1 (sign_flag32 difference) overflow2 carry2
    (zero_flag32 difference) auxiliary2 parity2).
  pose (s3 := write_reg_seq_state rflags f2 cmp_state).
  assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3).
  { eapply framed_instruction with (offset := 83) (size := 2)
      (instruction := CMP (32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 7))).
    - used_code.
    - used_present.
    - used_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 83 + 2) with (entry_pc frame + 85) by lia.
      exact Compare. }
  assert (Branch : @eq_vec 1 (_get_rflags_type_ZF f2) (Z_to_bv 1 0) =
    negb (Z.of_nat (S index) =? Z.of_nat size)).
  { unfold f2, difference. apply comparison_jne; lia. }
  pose (s4 := used_zero_pc s3 (entry_pc frame)
    (if Z.of_nat (S index) =? Z.of_nat size then 87 else 72)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { eapply framed_instruction with (offset := 85) (size := 2)
      (instruction := JNE (Z_to_bv 8 241)).
    - used_code.
    - used_present.
    - used_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 85 + 2) with (entry_pc frame + 87) by lia.
      erewrite execute_jne with (pc := machine_address (entry_pc frame + 87)) (flags := f2).
      + rewrite Branch. unfold s4.
        destruct (Z.of_nat (S index) =? Z.of_nat size); [reflexivity|].
        assert (Displacement : @sign_extend 8 (Z_to_bv 8 241) 64 = Z_to_bv 64 (-15))
          by (apply bv_eq; reflexivity).
        rewrite Displacement.
        change (@add_vec 64 (machine_address (entry_pc frame + 87)) (Z_to_bv 64 (-15)))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 87)) (-15)).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 87 + -15) with (entry_pc frame + 72) by lia.
        reflexivity.
      + apply register_read_written.
      + used_reads. reflexivity. }
  exists s4. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
  - split.
    + unfold s4, s3, cmp_state, s2, next, used_zero_pc.
      rewrite !register_write_memory. exact Related1.
    + split; [used_code|]. split; [used_present|].
      split; [used_reads; reflexivity|]. split; [used_reads; reflexivity|]. constructor.
      * intros reg NotPC NotFlags NotAX. unfold_used_states.
        repeat first [rewrite stored_register_read | rewrite register_read_frame by congruence].
        reflexivity.
      * intros stack StackLow StackHigh. unfold_used_states.
        repeat rewrite register_write_read_memory.
        rewrite (stack_read_cell_store layout program_bytes frame) by lia.
        apply register_write_read_memory.
Qed.

Print Assumptions used_zero_store_step.
Print Assumptions used_zero_iteration.

Theorem used_zero_loop nondet layout (frame : call_frame layout program_bytes)
    used size old start remaining c c' :
  zero_stores used start remaining c c' ->
  forall state,
  (0 < remaining)%nat -> (start + remaining = size)%nat -> (size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) used)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 72)) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout used) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat start)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 (Z.of_nat size) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) (4 * remaining) state final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 87)) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat size)) /\
    used_zero_frame layout frame state final.
Proof.
  intro Stores. induction Stores as [start c|start count c middle final Store Tail IH];
    intros state Positive Total Small Capacity Code Present PC Base Counter Old Low Related.
  - lia.
  - destruct (used_zero_iteration nondet layout frame used size start old state c middle
      ltac:(lia) Capacity Code Present PC Base Counter Old Low Related Store)
      as [next [Steps [RelatedNext [CodeNext [PresentNext [PCNext [CounterNext FrameNext]]]]]]].
    destruct count as [|count].
    + assert (SameMemory : final = middle) by (inversion Tail; reflexivity).
      subst final.
      assert (Last : Z.of_nat (S start) = Z.of_nat size) by lia.
      rewrite Last, Z.eqb_refl in PCNext. rewrite Last in CounterNext.
      exists next. split; [exact Steps|]. split; [exact RelatedNext|].
      split; [exact CodeNext|]. split; [exact PresentNext|].
      split; [exact PCNext|]. split; assumption.
    + assert (Continue : (Z.of_nat (S start) =? Z.of_nat size) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Continue in PCNext.
      assert (BaseNext : read_reg_seq_state r8 next = Some (pointer_to_block layout used)).
      { rewrite (used_zero_other _ _ _ _ FrameNext) by discriminate. exact Base. }
      assert (OldNext : read_reg_seq_state rdi next = Some old).
      { rewrite (used_zero_other _ _ _ _ FrameNext) by discriminate. exact Old. }
      destruct (IH next ltac:(lia) ltac:(lia) Small Capacity CodeNext PresentNext
        PCNext BaseNext CounterNext OldNext Low RelatedNext)
        as [last [Rest [RelatedLast [CodeLast [PresentLast [PCLast [CounterLast FrameLast]]]]]]].
      exists last. split.
      * replace (4 * S (S count))%nat with (4 + 4 * S count)%nat by lia.
        eapply instruction_steps_append; [exact Steps|exact Rest].
      * split; [exact RelatedLast|]. split; [exact CodeLast|]. split; [exact PresentLast|].
        split; [exact PCLast|]. split; [exact CounterLast|].
        eapply used_zero_frame_trans; eassumption.
Qed.

Theorem used_zero_preheader nondet layout (frame : call_frame layout program_bytes)
    used size old state c c' :
  (0 < size <= 1024)%nat -> (size <= block_words (cell_layout layout) used)%nat ->
  zero_stores used 0 size c c' ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 70)) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout used) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 (Z.of_nat size) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) (1 + 4 * size) state final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 87)) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat size)) /\
    used_zero_frame layout frame state final.
Proof.
  intros Range Capacity Stores Code Present PC Base Old Low Related.
  destruct (Present rax) as [old_ax OldAX]. destruct (Present rflags) as [flags Flags].
  pose (next := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state rax (Z_to_bv 64 0) (used_zero_pc state (entry_pc frame) 72))).
  assert (Preheader : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state next).
  { eapply framed_instruction with (offset := 70) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0)));
      [exact Code|exact Present|exact PC| | |].
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 70 + 2) with (entry_pc frame + 72) by lia.
      apply (execute_xor32_self nondet 0 _ old_ax flags).
      + discriminate.
      + change (read_reg_seq_state rax
          (write_reg_seq_state rip (machine_address (entry_pc frame + 72)) state) = Some old_ax).
        rewrite register_read_frame by discriminate. exact OldAX.
      + rewrite register_read_frame by discriminate. exact Flags. }
  assert (FrameNext : used_zero_frame layout frame state next).
  { constructor.
    - intros reg NotPC NotFlags NotAX. unfold_used_states.
      repeat rewrite register_read_frame by congruence. reflexivity.
    - intros stack StackLow StackHigh. reflexivity. }
  destruct (used_zero_loop nondet layout frame used size old 0 size c c' Stores next
    ltac:(lia) ltac:(lia) ltac:(lia) Capacity ltac:(used_code) ltac:(used_present)
    ltac:(used_reads; reflexivity) ltac:(used_reads; exact Base)
    ltac:(used_reads; reflexivity) ltac:(used_reads; exact Old) Low
    ltac:(unfold next, used_zero_pc; rewrite !register_write_memory; exact Related))
    as [final [Loop [RelatedFinal [CodeFinal [PresentFinal [PCFinal [CounterFinal FrameFinal]]]]]]].
  exists final. split.
  - eapply instruction_steps_append; [exact Preheader|exact Loop].
  - split; [exact RelatedFinal|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact PCFinal|]. split; [exact CounterFinal|].
    eapply used_zero_frame_trans; eassumption.
Qed.

Print Assumptions used_zero_loop.
Print Assumptions used_zero_preheader.
