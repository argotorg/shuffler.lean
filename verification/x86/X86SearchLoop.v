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
  X86UsedZero X86ValidationSteps X86Validation X86SearchSteps X86Search.
Import ListNotations.
Open Scope Z_scope.

Theorem search_preheader nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 201)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 204)) /\
    read_reg_seq_state r13 final = Some (machine_address 0).
Proof.
  intros Code Present PC.
  destruct (Present r13) as [old Old]. destruct (Present rflags) as [flags Flags].
  pose (final := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state r13 (machine_address 0) (validation_pc state (entry_pc frame) 204))).
  exists final. split.
  - eapply framed_instruction with (offset := 201) (size := 3)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 13), rmi_REG (REG_NORMAL 13)));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 201 + 3) with (entry_pc frame + 204) by lia.
      apply (execute_xor32_self nondet 13 _ old flags).
      * discriminate.
      * change (read_reg_seq_state r13
          (write_reg_seq_state rip (machine_address (entry_pc frame + 204)) state) = Some old).
        rewrite register_read_frame by discriminate. exact Old.
      * rewrite register_read_frame by discriminate. exact Flags.
  - split; [search_frame_build|]. split; [validation_code|].
    split; [validation_present|]. split; validation_reads; reflexivity.
Qed.

Lemma search_accept nondet layout (frame : call_frame layout program_bytes)
    state index size size_old :
  (index < size <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 233)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state rdi state = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 2 state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 243)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat index)).
Proof.
  intros Range Code Present PC Index SizeRead SizeLow.
  destruct (search_compare_step nondet layout frame state 233 3 13 7
    (machine_address (Z.of_nat index)) size_old (Z.of_nat index) (Z.of_nat size)
    ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia)
    Code Present PC Index
    ltac:(change (low_register32 0 (machine_address (Z.of_nat index)) = Z_to_bv 32 (Z.of_nat index));
      apply machine_low32; change Int.modulus with 4294967296; lia)
    SizeRead SizeLow) as [flags [Compare Zero]].
  assert (Different : (Z.of_nat index =? Z.of_nat size) = false) by (apply Z.eqb_neq; lia).
  rewrite Different in Zero. cbn in Zero.
  pose (compared := write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) 236)).
  pose (final := validation_pc compared (entry_pc frame) 243).
  assert (Jump : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 compared final).
  { exact (search_jne_step nondet layout frame compared 236 5 5 flags true
      ltac:(right; right; right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero). }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat);
      [exact Compare|exact Jump].
  - split; [search_frame_build|]. split; [validation_code|].
    split; [validation_present|]. split; validation_reads; [reflexivity|exact Index].
Qed.

Lemma search_advance nondet layout (frame : call_frame layout program_bytes)
    state index size size_old :
  (S index < size <= 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 224)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state rdi state = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 3 state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 204)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range Code Present PC Index SizeRead SizeLow.
  destruct (search_increment nondet layout frame state index ltac:(lia)
    Code Present PC Index) as [f1 Increment].
  pose (s1 := write_reg_seq_state rflags f1
    (write_reg_seq_state r13 (machine_address (Z.of_nat (S index)))
      (validation_pc state (entry_pc frame) 228))).
  destruct (search_compare_step nondet layout frame s1 228 3 13 7
    (machine_address (Z.of_nat (S index))) size_old (Z.of_nat (S index)) (Z.of_nat size)
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
    ltac:(validation_reads; reflexivity)
    ltac:(change (low_register32 0 (machine_address (Z.of_nat (S index))) = Z_to_bv 32 (Z.of_nat (S index)));
      apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(validation_reads; exact SizeRead) SizeLow) as [f2 [Compare Zero]].
  assert (Different : (Z.of_nat (S index) =? Z.of_nat size) = false) by (apply Z.eqb_neq; lia).
  rewrite Different in Zero. cbn in Zero.
  pose (s2 := write_reg_seq_state rflags f2 (validation_pc s1 (entry_pc frame) 231)).
  pose (final := validation_pc s2 (entry_pc frame) 204).
  assert (Jump : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 final).
  { exact (search_jne_step nondet layout frame s2 231 227 (-29) f2 true
      ltac:(right; right; left; reflexivity)
      ltac:(validation_code) ltac:(validation_present) ltac:(validation_reads; reflexivity)
      ltac:(validation_reads; reflexivity) Zero). }
  exists final. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Increment|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Compare|exact Jump].
  - split; [search_frame_build|]. split; [validation_code|].
    split; [validation_present|]. split; validation_reads; reflexivity.
Qed.

Print Assumptions search_preheader.
Print Assumptions search_accept.
Print Assumptions search_advance.

Lemma search_found_from nondet layout (frame : call_frame layout program_bytes)
    size found bt bu source source_old size_old (desired flags : nat -> Int.int) c remaining :
  forall start state,
  (start <= found < size)%nat -> (size <= 1024)%nat ->
  found = (start + remaining)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  search_word_match source (desired found) (flags found) = true ->
  (forall index, (start <= index < found)%nat ->
    search_word_match source (desired index) (flags index) = false) ->
  (forall index, (start <= index <= found)%nat ->
    Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint (desired index))) ->
  (forall index, (start <= index <= found)%nat ->
    Mem.load Mint32 c bu (4 * Z.of_nat index) = Some (Vint (flags index))) ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 204)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat start)) ->
  read_reg_seq_state r11 state = Some source_old ->
  low_register32 11 source_old = machine_word source ->
  read_reg_seq_state rcx state = Some (pointer_to_block layout bt) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout bu) ->
  read_reg_seq_state rdi state = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 243)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat found)).
Proof.
  induction remaining as [|remaining IH]; intros start state Range Bound Distance CT CU
    Found Minimum TargetLoads FlagLoads Code Present PC Index Source SourceLow Target Used
    SizeRead SizeLow Related.
  - assert (Equal : start = found) by lia. subst start.
    destruct (search_probe nondet layout frame state found bt bu source source_old
      (desired found) (flags found) c ltac:(lia) ltac:(lia) Code Present PC Index
      Source SourceLow Target Used Related (FlagLoads found ltac:(lia))
      (TargetLoads found ltac:(lia)))
      as [probe_count [probed [Probe [ProbeFrame [ProbeCode [ProbePresent [ProbePC ProbeIndex]]]]]]].
    rewrite Found in ProbePC.
    assert (ProbeSize : read_reg_seq_state rdi probed = Some size_old).
    { rewrite (proj2 ProbeFrame rdi) by (unfold search_clobbered; cbn; intuition discriminate).
      exact SizeRead. }
    destruct (search_accept nondet layout frame probed found size size_old ltac:(lia)
      ProbeCode ProbePresent ProbePC ProbeIndex ProbeSize SizeLow)
      as [final [Accept [AcceptFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]].
    exists (probe_count + 2)%nat, final. split.
    + eapply instruction_steps_append; [exact Probe|exact Accept].
    + split; [eapply search_frame_trans; [exact ProbeFrame|exact AcceptFrame]|].
      split; [exact FinalCode|]. split; [exact FinalPresent|]. split; assumption.
  - assert (Earlier : (start < found)%nat) by lia.
    destruct (search_probe nondet layout frame state start bt bu source source_old
      (desired start) (flags start) c ltac:(lia) ltac:(lia) Code Present PC Index
      Source SourceLow Target Used Related (FlagLoads start ltac:(lia))
      (TargetLoads start ltac:(lia)))
      as [probe_count [probed [Probe [ProbeFrame [ProbeCode [ProbePresent [ProbePC ProbeIndex]]]]]]].
    rewrite (Minimum start ltac:(lia)) in ProbePC.
    assert (ProbeSize : read_reg_seq_state rdi probed = Some size_old).
    { rewrite (proj2 ProbeFrame rdi) by (unfold search_clobbered; cbn; intuition discriminate).
      exact SizeRead. }
    destruct (search_advance nondet layout frame probed start size size_old ltac:(lia)
      ProbeCode ProbePresent ProbePC ProbeIndex ProbeSize SizeLow)
      as [advanced [Advance [AdvanceFrame [AdvanceCode [AdvancePresent [AdvancePC AdvanceIndex]]]]]].
    assert (Frame : search_frame state advanced).
    { eapply search_frame_trans; [exact ProbeFrame|exact AdvanceFrame]. }
    assert (AdvanceRelated : machine_cells_related layout c (archState.memory (sst advanced))).
    { rewrite (proj1 Frame). exact Related. }
    assert (AdvanceSource : read_reg_seq_state r11 advanced = Some source_old).
    { rewrite (proj2 Frame r11) by (unfold search_clobbered; cbn; intuition discriminate).
      exact Source. }
    assert (AdvanceTarget : read_reg_seq_state rcx advanced = Some (pointer_to_block layout bt)).
    { rewrite (proj2 Frame rcx) by (unfold search_clobbered; cbn; intuition discriminate).
      exact Target. }
    assert (AdvanceUsed : read_reg_seq_state r8 advanced = Some (pointer_to_block layout bu)).
    { rewrite (proj2 Frame r8) by (unfold search_clobbered; cbn; intuition discriminate).
      exact Used. }
    assert (AdvanceSize : read_reg_seq_state rdi advanced = Some size_old).
    { rewrite (proj2 Frame rdi) by (unfold search_clobbered; cbn; intuition discriminate).
      exact SizeRead. }
    destruct (IH (S start) advanced ltac:(lia) Bound ltac:(lia) CT CU Found
      ltac:(intros index Between; apply Minimum; lia)
      ltac:(intros index Between; apply TargetLoads; lia)
      ltac:(intros index Between; apply FlagLoads; lia)
      AdvanceCode AdvancePresent AdvancePC AdvanceIndex AdvanceSource SourceLow
      AdvanceTarget AdvanceUsed AdvanceSize SizeLow AdvanceRelated)
      as [rest_count [final [Rest [RestFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]]].
    exists (probe_count + (3 + rest_count))%nat, final. split.
    + eapply instruction_steps_append; [exact Probe|].
      eapply instruction_steps_append; [exact Advance|exact Rest].
    + split; [eapply search_frame_trans; [exact Frame|exact RestFrame]|].
      split; [exact FinalCode|]. split; [exact FinalPresent|]. split; assumption.
Qed.

Theorem search_found_loop nondet layout (frame : call_frame layout program_bytes)
    state size start found bt bu source source_old size_old (desired flags : nat -> Int.int) c :
  (start <= found < size)%nat -> (size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  search_word_match source (desired found) (flags found) = true ->
  (forall index, (start <= index < found)%nat ->
    search_word_match source (desired index) (flags index) = false) ->
  (forall index, (start <= index <= found)%nat ->
    Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint (desired index))) ->
  (forall index, (start <= index <= found)%nat ->
    Mem.load Mint32 c bu (4 * Z.of_nat index) = Some (Vint (flags index))) ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 204)) ->
  read_reg_seq_state r13 state = Some (machine_address (Z.of_nat start)) ->
  read_reg_seq_state r11 state = Some source_old ->
  low_register32 11 source_old = machine_word source ->
  read_reg_seq_state rcx state = Some (pointer_to_block layout bt) ->
  read_reg_seq_state r8 state = Some (pointer_to_block layout bu) ->
  read_reg_seq_state rdi state = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  exists count final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    search_frame state final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 243)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat found)).
Proof.
  intros Range Bound CT CU Found Minimum TargetLoads FlagLoads Code Present PC Index
    Source SourceLow Target Used SizeRead SizeLow Related.
  exact (search_found_from nondet layout frame size found bt bu source source_old size_old
    desired flags c (found - start)%nat start state Range Bound ltac:(lia) CT CU Found
    Minimum TargetLoads FlagLoads Code Present PC Index Source SourceLow Target Used
    SizeRead SizeLow Related).
Qed.

Print Assumptions search_found_loop.
