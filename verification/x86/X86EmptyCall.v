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
  X86Compare X86Program X86Execution X86Prologue X86Initialize X86EmptyBody
  X86Cleanup X86SavedFrame X86Call X86Entry.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* Expose the store witness of the existing LLVM call proof. The same witness
   is used by the machine proof, including uninitialized output cells. *)
Theorem empty_llvm_call_stores layout output c caller data perm target used trace :
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%nat ->
  exists c' final,
    output_stores c output c' /\ cells_related layout c' (fst final) /\
    array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      [word_value Int.zero; data; perm; target; used; trace; mapped_pointer layout output])
      caller final (inr (word_value Int.zero)) /\
    snd final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Related Capacity.
  pose (initial := call_state caller (word_value Int.zero) data perm target used trace
    (mapped_pointer layout output)).
  assert (RelatedInitial : cells_related layout c (fst initial)) by (apply call_state_related, Related).
  destruct (call_state_bindings caller (word_value Int.zero) data perm target used trace
    (mapped_pointer layout output)) as [N [D [P [T [U [R O]]]]]].
  destruct (@empty_path layout output Int.zero (Some (empty_varargs_pointer (fst caller)))
    c initial ltac:(reflexivity) Capacity RelatedInitial N O)
    as [c' [body [Stores [RelatedBody [Output [Path Frame]]]]]].
  exists c', (returned_state caller body). split; [exact Stores|].
  split; [apply returned_state_related, RelatedBody|].
  split; [exact Output|]. split; [apply full_call_from_path, Path|].
  split; [apply returned_state_caller|exact Frame].
Qed.

Print Assumptions empty_llvm_call_stores.

Theorem empty_machine_call layout (frame : call_frame layout program_bytes)
    bd bp bt bu trace output c c' initial :
  abi_entry layout program_bytes frame Int.zero bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  machine_cells_related layout c (archState.memory (sst initial)) ->
  output_stores c output c' ->
  exists final,
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) 24 initial final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    abi_return layout program_bytes frame initial final Int.zero.
Proof.
  intros Entry Capacity Related [c1 [c2 [W0 [W1 W2]]]].
  destruct (enter_call true layout frame Int.zero bd bp bt bu trace output c c1 c2 c' initial
    Entry Capacity Related W0 W1 W2)
    as [Enter [RelatedBody [Code [Present [PC Stack]]]]].
  pose (body := call_body_state layout frame output initial).
  destruct (entry_size _ _ _ _ _ _ _ _ _ _ _ Entry) as [old [Old Low]].
  assert (OldBody : read_reg_seq_state rdi body = Some old).
  { unfold body, call_body_state. rewrite initialized_other, prologue_other by discriminate. exact Old. }
  assert (LowBody : low_register32 7 old = Z_to_bv 32 0).
  { exact Low. }
  destruct (empty_body_path true layout frame body old Code Present PC OldBody LowBody)
    as [middle [Steps Body]].
  assert (StackMiddle : call_stack layout frame initial middle).
  { apply (call_stack_same_memory layout frame initial body middle Stack).
    - apply (empty_body_other _ _ _ Body); discriminate.
    - apply (empty_body_other _ _ _ Body); discriminate.
    - exact (empty_body_memory _ _ _ Body). }
  assert (Result : exists value, read_reg_seq_state rax middle = Some value /\
      bv_extract 0 32 value = machine_word Int.zero).
  { exists (Z_to_bv 64 0). split; [exact (empty_body_rax _ _ _ Body)|reflexivity]. }
  destruct (finish_call layout frame initial middle Int.zero
    (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry)
    (empty_body_code _ _ _ Body) (empty_body_present _ _ _ Body)
    (empty_body_pc _ _ _ Body) StackMiddle Result) as [Finish [Return Memory]].
  exists (call_return_state layout frame initial middle). split.
  - eapply instruction_steps_append with (count := 9%nat) (rest := 15%nat); [exact Enter|].
    eapply instruction_steps_append with (count := 9%nat) (rest := 6%nat); [exact Steps|exact Finish].
  - split; [|exact Return]. rewrite Memory, (empty_body_memory _ _ _ Body). exact RelatedBody.
Qed.

(* This theorem has no machine execution premise. All 24 steps are derived
   from the entry ABI, the actual code bytes, and the memory relation. *)
Theorem empty_call_agrees layout (frame : call_frame layout program_bytes)
    bd bp bt bu trace output c caller initial :
  abi_entry layout program_bytes frame Int.zero bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  exists c' llvm_final machine_final,
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) Int.zero bd bp bt bu trace output))
      caller llvm_final (inr (word_value Int.zero)) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) 24 initial machine_final /\
    abi_return layout program_bytes frame initial machine_final Int.zero /\
    snd llvm_final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Entry Capacity [LLVM Machine].
  destruct (empty_llvm_call_stores (cell_layout layout) output c caller
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) LLVM Capacity)
    as [c' [llvm_final [Stores [LLVMFinal [Output [LLVMRun [Caller Frame]]]]]]].
  destruct (empty_machine_call layout frame bd bp bt bu trace output c c' initial
    Entry Capacity Machine Stores) as [machine_final [MachineRun [MachineFinal Return]]].
  exists c', llvm_final, machine_final.
  split; [split; assumption|]. split; [exact Output|]. split; [exact LLVMRun|].
  split; [exact MachineRun|]. split; [exact Return|]. split; assumption.
Qed.

Theorem empty_call_run_agrees layout (frame : call_frame layout program_bytes)
    bd bp bt bu trace output c caller initial :
  abi_entry layout program_bytes frame Int.zero bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  exists c' llvm_final machine_final terminated,
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) Int.zero bd bp bt bu trace output))
      caller llvm_final (inr (word_value Int.zero)) /\
    opModel.run (sequential_opmodel None (sail_tiny_x86_sem true)) 25
      (return_condition (machine_address (return_pc frame))) (sst initial) initial =
      Exec.make [(machine_final, existT (sst machine_final) terminated)] [] /\
    abi_return layout program_bytes frame initial machine_final Int.zero.
Proof.
  intros Entry Capacity Related.
  destruct (empty_call_agrees layout frame bd bp bt bu trace output c caller initial
    Entry Capacity Related) as [c' [llvm_final [machine_final
      [FinalRelated [Output [LLVMRun [Steps [Return [Caller Frame]]]]]]]]].
  destruct (instruction_steps_run (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 24 initial machine_final
    (sst initial) Steps (returned_state_terminates layout program_bytes frame initial machine_final Int.zero Return))
    as [terminated Run].
  exists c', llvm_final, machine_final, terminated.
  split; [exact FinalRelated|]. split; [exact LLVMRun|]. split; assumption.
Qed.

Print Assumptions empty_machine_call.
Print Assumptions empty_call_agrees.
Print Assumptions empty_call_run_agrees.
