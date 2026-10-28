(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers Values.
Require Import ClightMemory.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry
  CallBoundary EarlyExit FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Control X86Instructions
  X86Compare X86Program X86Execution X86Prologue X86Initialize X86OversizedBody
  X86Cleanup X86SavedFrame X86Call X86Entry.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* Both executions use the same three output-store witnesses. *)
Theorem oversized_llvm_call_stores layout output n c caller data perm target used trace :
  1024 < Int.unsigned n ->
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%nat ->
  exists c' final,
    output_stores c output c' /\ cells_related layout c' (fst final) /\
    array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      [word_value n; data; perm; target; used; trace; mapped_pointer layout output])
      caller final (inr (word_value (Int.repr 2))) /\
    snd final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Large Related Capacity.
  pose (initial := call_state caller (word_value n) data perm target used trace
    (mapped_pointer layout output)).
  assert (RelatedInitial : cells_related layout c (fst initial)) by (apply call_state_related, Related).
  destruct (call_state_bindings caller (word_value n) data perm target used trace
    (mapped_pointer layout output)) as [N [D [P [T [U [R O]]]]]].
  destruct (@oversized_path layout output n (Some (empty_varargs_pointer (fst caller)))
    c initial Large Capacity RelatedInitial N O)
    as [c' [body [Stores [RelatedBody [Output [Path Frame]]]]]].
  exists c', (returned_state caller body). split; [exact Stores|].
  split; [apply returned_state_related, RelatedBody|].
  split; [exact Output|]. split; [apply full_call_from_path, Path|].
  split; [apply returned_state_caller|exact Frame].
Qed.

Theorem oversized_machine_call layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output c c' initial :
  1024 < Int.unsigned n ->
  abi_entry layout program_bytes frame n bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  machine_cells_related layout c (archState.memory (sst initial)) ->
  output_stores c output c' ->
  exists count final,
    (count = 19 \/ count = 21)%nat /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) count initial final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    abi_return layout program_bytes frame initial final (Int.repr 2).
Proof.
  intros Large Entry Capacity Machine [c1 [c2 [W0 [W1 W2]]]].
  pose (body_start := call_body_state layout frame output initial).
  destruct (enter_call true layout frame n bd bp bt bu trace output c c1 c2 c' initial
    Entry Capacity Machine W0 W1 W2)
    as [Enter [MachineBody [Code [Present [PC Stack]]]]].
  destruct (entry_size _ _ _ _ _ _ _ _ _ _ _ Entry) as [old [Old Low]].
  change (read_reg_seq_state rdi initial = Some old) in Old.
  change (low_register32 7 old = Z_to_bv 32 (Int.unsigned n)) in Low.
  assert (OldBody : read_reg_seq_state rdi body_start = Some old).
  { unfold body_start, call_body_state.
    rewrite initialized_other by discriminate.
    rewrite prologue_other by discriminate. exact Old. }
  assert (Range : 1024 < Int.unsigned n < 4294967296).
  { pose proof (Int.unsigned_range n). change (0 <= Int.unsigned n < 4294967296) in H. lia. }
  destruct (oversized_body_path true layout frame body_start old (Int.unsigned n)
    Range Code Present PC OldBody Low)
    as [body_count [body_final [Count [Body Result]]]].
  destruct Result as [BodyPC RAX Other BodyMemory BodyWritten BodyPresent BodyCode].
  assert (BodyStack : call_stack layout frame initial body_final).
  { eapply call_stack_same_memory; [exact Stack| | |exact BodyMemory];
      apply Other; discriminate. }
  assert (ReturnValue : exists value, read_reg_seq_state rax body_final = Some value /\
    bv_extract 0 32 value = machine_word (Int.repr 2)).
  { exists (Z_to_bv 64 2). split; [exact RAX|reflexivity]. }
  destruct (finish_call layout frame initial body_final (Int.repr 2)
    (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry)
    BodyCode BodyPresent BodyPC BodyStack ReturnValue)
    as [Finish [Returned FinalMemory]].
  exists (9 + body_count + 6)%nat, (call_return_state layout frame initial body_final).
  split; [destruct Count; lia|]. split.
  - replace (9 + body_count + 6)%nat with (9 + (body_count + 6))%nat by lia.
    eapply instruction_steps_append; [exact Enter|].
    eapply instruction_steps_append; [exact Body|exact Finish].
  - split; [|exact Returned]. rewrite FinalMemory, BodyMemory. exact MachineBody.
Qed.

(* The instruction count and the machine execution are conclusions. *)
Theorem oversized_call_agrees layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output c caller initial :
  1024 < Int.unsigned n ->
  abi_entry layout program_bytes frame n bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  exists c' llvm_final machine_final count,
    (count = 19 \/ count = 21)%nat /\
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) n bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr 2))) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) count initial machine_final /\
    abi_return layout program_bytes frame initial machine_final (Int.repr 2) /\
    snd llvm_final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Large Entry Capacity [LLVM Machine].
  destruct (oversized_llvm_call_stores (cell_layout layout) output n c caller
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) Large LLVM Capacity)
    as [c' [llvm_final [Stores [LLVMFinal [Output [LLVMRun [Caller ArrayFrame]]]]]]].
  destruct (oversized_machine_call layout frame n bd bp bt bu trace output c c' initial
    Large Entry Capacity Machine Stores)
    as [count [machine_final [Count [MachineRun [MachineFinal Returned]]]]].
  exists c', llvm_final, machine_final, count.
  split; [exact Count|]. split; [split; assumption|].
  split; [exact Output|]. split; [exact LLVMRun|].
  split; [exact MachineRun|]. split; [exact Returned|]. split; assumption.
Qed.

Theorem oversized_call_run_agrees layout (frame : call_frame layout program_bytes)
    n bd bp bt bu trace output c caller initial :
  1024 < Int.unsigned n ->
  abi_entry layout program_bytes frame n bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  exists c' llvm_final machine_final count terminated,
    (count = 19 \/ count = 21)%nat /\
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) n bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr 2))) /\
    opModel.run (sequential_opmodel None (sail_tiny_x86_sem true)) (S count)
      (return_condition (machine_address (return_pc frame))) (sst initial) initial =
      Exec.make [(machine_final, existT (sst machine_final) terminated)] [] /\
    abi_return layout program_bytes frame initial machine_final (Int.repr 2).
Proof.
  intros Large Entry Capacity Related.
  destruct (oversized_call_agrees layout frame n bd bp bt bu trace output c caller initial
    Large Entry Capacity Related) as [c' [llvm_final [machine_final [count
      [Count [FinalRelated [Output [LLVMRun [Steps [Returned [Caller ArrayFrame]]]]]]]]]]].
  destruct (instruction_steps_run (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) count initial machine_final
    (sst initial) Steps
    (returned_state_terminates layout program_bytes frame initial machine_final (Int.repr 2) Returned))
    as [terminated Run].
  exists c', llvm_final, machine_final, count, terminated.
  split; [exact Count|]. split; [exact FinalRelated|]. split; [exact LLVMRun|].
  split; assumption.
Qed.

Print Assumptions oversized_llvm_call_stores.
Print Assumptions oversized_machine_call.
Print Assumptions oversized_call_agrees.
Print Assumptions oversized_call_run_agrees.
