(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory X86ABI X86Program X86Execution
  X86Instructions X86Control X86StackMemory X86Prologue X86Initialize X86SavedFrame X86Cleanup.
Open Scope Z_scope.

Record call_stack layout (frame : call_frame layout program_bytes)
    (initial state : seq_state) : Prop := {
  call_stack_rsp : read_reg_seq_state rsp state = Some (machine_address (entry_sp frame - 40));
  call_stack_r15 : read_mem_seq_state 8 (machine_address (entry_sp frame - 40)) state =
    Some (register_values_of initial r15);
  call_stack_r14 : read_mem_seq_state 8 (machine_address (entry_sp frame - 32)) state =
    Some (register_values_of initial r14);
  call_stack_r13 : read_mem_seq_state 8 (machine_address (entry_sp frame - 24)) state =
    Some (register_values_of initial r13);
  call_stack_r12 : read_mem_seq_state 8 (machine_address (entry_sp frame - 16)) state =
    Some (register_values_of initial r12);
  call_stack_rbx : read_mem_seq_state 8 (machine_address (entry_sp frame - 8)) state =
    Some (register_values_of initial rbx);
  call_stack_return : read_mem_seq_state 8 (machine_address (entry_sp frame)) state =
    Some (machine_address (return_pc frame));
  call_stack_rbp : read_reg_seq_state rbp state = read_reg_seq_state rbp initial
}.

Definition call_body_state layout (frame : call_frame layout program_bytes) output initial : seq_state :=
  initialized_state layout frame output (prologue_state layout frame output initial).

Lemma prologue_call_stack layout (frame : call_frame layout program_bytes) output initial :
  read_mem_seq_state 8 (machine_address (entry_sp frame)) initial =
    Some (machine_address (return_pc frame)) ->
  call_stack layout frame initial (prologue_state layout frame output initial).
Proof.
  intro Return.
  destruct (prologue_saved_reads layout frame output initial)
    as [R15 [R14 [R13 [R12 [RBX SavedReturn]]]]].
  constructor; try assumption.
  - apply prologue_stack.
  - rewrite SavedReturn. exact Return.
  - apply prologue_other; discriminate.
Qed.

Lemma initialized_call_stack layout (frame : call_frame layout program_bytes) output initial state :
  (3 <= block_words (cell_layout layout) output)%nat ->
  call_stack layout frame initial state ->
  call_stack layout frame initial (initialized_state layout frame output state).
Proof.
  intros Capacity Stack. destruct Stack as [SP R15 R14 R13 R12 RBX Return BP].
  constructor.
  - rewrite initialized_other by discriminate. exact SP.
  - rewrite initialized_stack_read by lia. exact R15.
  - rewrite initialized_stack_read by lia. exact R14.
  - rewrite initialized_stack_read by lia. exact R13.
  - rewrite initialized_stack_read by lia. exact R12.
  - rewrite initialized_stack_read by lia. exact RBX.
  - rewrite initialized_stack_read by lia. exact Return.
  - rewrite initialized_other by discriminate. exact BP.
Qed.

Theorem enter_call nondet layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output c c1 c2 c3 initial :
  abi_entry layout program_bytes frame n bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  machine_cells_related layout c (archState.memory (sst initial)) ->
  Mem.store Mint32 c output 0 (Vint Int.zero) = Some c1 ->
  Mem.store Mint32 c1 output 4 (Vint Int.zero) = Some c2 ->
  Mem.store Mint32 c2 output 8 (Vint Int.zero) = Some c3 ->
  let final := call_body_state layout frame output initial in
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 9 initial final /\
  machine_cells_related layout c3 (archState.memory (sst final)) /\
  code_at final (entry_pc frame) program_bytes /\ registers_present final /\
  read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 37)) /\
  call_stack layout frame initial final.
Proof.
  intros Entry Capacity Related W0 W1 W2 final.
  pose proof (entry_code _ _ _ _ _ _ _ _ _ _ _ Entry) as Code.
  pose proof (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry) as Present.
  destruct (initialize_steps nondet layout frame output c c1 c2 c3
    (prologue_state layout frame output initial) Capacity
    (prologue_cells_related layout frame output initial c Related) W0 W1 W2
    (prologue_code layout frame output initial Code)
    (prologue_registers layout frame output initial Present)
    (prologue_pc layout frame output initial)
    (prologue_output layout frame output initial)) as [Initialize FinalRelated].
  split.
  - eapply instruction_steps_append with (count := 6%nat) (rest := 3%nat).
    + exact (prologue_steps nondet layout frame n bd bp bt bu trace output initial Entry).
    + exact Initialize.
  - split; [exact FinalRelated|]. split.
    + apply initialized_code; [exact Capacity|apply prologue_code, Code].
    + split.
      * apply initialized_registers, prologue_registers, Present.
      * split; [apply initialized_pc|].
        apply initialized_call_stack; [exact Capacity|apply prologue_call_stack].
        exact (entry_return_address _ _ _ _ _ _ _ _ _ _ _ Entry).
Qed.

Definition call_return_state layout (frame : call_frame layout program_bytes) initial state : seq_state :=
  cleanup_result (entry_pc frame) (entry_sp frame)
    (register_values_of initial r15) (register_values_of initial r14)
    (register_values_of initial r13) (register_values_of initial r12)
    (register_values_of initial rbx) (machine_address (return_pc frame)) state.

Theorem finish_call layout (frame : call_frame layout program_bytes) initial state result :
  registers_present initial -> code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 428)) ->
  call_stack layout frame initial state ->
  (exists value, read_reg_seq_state rax state = Some value /\
    bv_extract 0 32 value = machine_word result) ->
  let final := call_return_state layout frame initial state in
  instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 6 state final /\
  abi_return layout program_bytes frame initial final result /\
  archState.memory (sst final) = archState.memory (sst state).
Proof.
  intros InitialPresent Code Present PC Stack Result final.
  destruct Stack as [SP R15 R14 R13 R12 RBX Return BP]. split.
  - exact (cleanup_steps layout frame state
      (register_values_of initial r15) (register_values_of initial r14)
      (register_values_of initial r13) (register_values_of initial r12)
      (register_values_of initial rbx) Code Present PC SP R15 R14 R13 R12 RBX Return).
  - split; [|reflexivity].
    exact (cleanup_abi_return layout frame initial state
      (register_values_of initial r15) (register_values_of initial r14)
      (register_values_of initial r13) (register_values_of initial r12)
      (register_values_of initial rbx) result
      (register_values_agree initial InitialPresent r15)
      (register_values_agree initial InitialPresent r14)
      (register_values_agree initial InitialPresent r13)
      (register_values_agree initial InitialPresent r12)
      (register_values_agree initial InitialPresent rbx) BP Result).
Qed.

Lemma call_stack_preserved layout (frame : call_frame layout program_bytes) initial before after :
  call_stack layout frame initial before ->
  read_reg_seq_state rsp after = read_reg_seq_state rsp before ->
  read_reg_seq_state rbp after = read_reg_seq_state rbp before ->
  (forall stack, entry_sp frame - 40 <= stack -> stack + 8 <= entry_sp frame + 16 ->
    read_mem_seq_state 8 (machine_address stack) after =
      read_mem_seq_state 8 (machine_address stack) before) ->
  call_stack layout frame initial after.
Proof.
  intros Stack SP BP Read. destruct Stack as [Stack R15 R14 R13 R12 RBX Return Base].
  constructor.
  - rewrite SP. exact Stack.
  - rewrite Read by lia. exact R15.
  - rewrite Read by lia. exact R14.
  - rewrite Read by lia. exact R13.
  - rewrite Read by lia. exact R12.
  - rewrite Read by lia. exact RBX.
  - rewrite Read by lia. exact Return.
  - rewrite BP. exact Base.
Qed.

Lemma call_stack_same_memory layout (frame : call_frame layout program_bytes) initial before after :
  call_stack layout frame initial before ->
  read_reg_seq_state rsp after = read_reg_seq_state rsp before ->
  read_reg_seq_state rbp after = read_reg_seq_state rbp before ->
  archState.memory (sst after) = archState.memory (sst before) ->
  call_stack layout frame initial after.
Proof.
  intros Stack SP BP Mem. apply (call_stack_preserved layout frame initial before after Stack SP BP).
  intros stack Low High. rewrite !read_mem_is_lookup, Mem. reflexivity.
Qed.

Print Assumptions enter_call.
Print Assumptions finish_call.
Print Assumptions call_stack_same_memory.
