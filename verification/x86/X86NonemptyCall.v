(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix Cleanup CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Entry X86Arguments X86Prefix X86ModelTypes
  X86NormalizationModel X86LoopModel X86MainPrefix X86MainLoopCore X86MainLoop.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section NonemptyCall.
Context (layout : finite_layout) (frame : call_frame layout program_bytes)
    (d : nat) (bd bp bt bu trace output : Values.block).
Hypothesis Separate : separate_arrays bd bp bt bu trace output.
Hypothesis Size : (S d <= 1024)%nat.
Hypotheses (CD : (S d <= block_words (cell_layout layout) bd)%nat)
    (CP : (S d <= block_words (cell_layout layout) bp)%nat)
    (CT : (S d <= block_words (cell_layout layout) bt)%nat)
    (CU : (S d <= block_words (cell_layout layout) bu)%nat)
    (CR : (2 * S d <= block_words (cell_layout layout) trace)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).

Theorem nonempty_call_agrees (source : fintype.ordinal (S d) -> nat)
    (p : model_permutation (S d)) c caller initial :
  (forall i, uint (Z.of_nat (source i))) ->
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat (S d)))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd (words source) -> array_at c bp (words (model_destination p)) ->
  exists result c' llvm_final machine_final steps code,
    model_permute source p = Some result /\
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output result c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr code))) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps initial machine_final /\
    abi_return layout program_bytes frame initial machine_final (Int.repr code) /\
    snd llvm_final = snd caller /\
    (forall other xs, other <> bd -> other <> bp -> other <> bt -> other <> bu ->
      other <> trace -> other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Values Entry Related Data Perm.
  destruct Separate as [DP DT DU DR DO PT PU PR PO TU TR TO UR UO RO].
  destruct (@main_prefix_agrees layout frame d source p bd bp bt bu trace output Size Values
    DP DU DT PU PT TU DO PO (not_eq_sym UO) (not_eq_sym TO) CD CP CT CU CR CO
    c caller initial Entry Related Data Perm)
    as (q & c1 & llvm1 & machine1 & count1 & Normalized & Related1 & Arrays1 & Registers1 &
      LLVMPrefix & MachinePrefix & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Top1 & Capacity1 & Frame1).
  assert (State1 : main_machine_state layout frame initial d bd bp bt bu trace output machine1).
  { exact (conj Code1 (conj Present1 (conj Arguments1 (conj Stack1 (conj Top1 Capacity1))))). }
  destruct (@main_loop_nonempty_agrees layout frame initial d bd bp bt bu trace output
    DP DR DO PR PO RO Size CD CP CR CO source q c1 llvm1 machine1 (Name "while.end105"%string)
    (Some (empty_varargs_pointer (fst caller))) Values Related1 Arrays1 Registers1 State1 PC1)
    as (c' & body & machine2 & count2 & code & Related2 & ResultCode & Result & LLVMLoop & MachineLoop &
      Code2 & Present2 & Stack2 & PC2 & Return2 & Frame2).
  assert (ReturnValue : exists value, read_reg_seq_state rax machine2 = Some value /\
      bv_extract 0 32 value = machine_word (Int.repr code)).
  { exists (machine_address code). split; [exact Return2|].
    destruct ResultCode as [Zero|One]; subst code; reflexivity. }
  destruct (finish_call layout frame initial machine2 (Int.repr code)
    (abi_registers_present _ _ _ _ _ _ _ _ _ _ _ Entry) Code2 Present2 PC2 Stack2 ReturnValue)
    as (Finish & Return & MemoryReturn).
  exists (model_nonempty source q), c', (returned_state caller body),
    (call_return_state layout frame initial machine2), (count1 + (count2 + 6))%nat, code.
  split; [apply model_permute_normalized, Normalized|]. split.
  - split; [apply returned_state_related, (proj1 Related2)|].
    rewrite MemoryReturn. exact (proj2 Related2).
  - split; [exact ResultCode|]. split; [exact Result|]. split.
    + apply full_call_from_path. eapply block_steps_return; eassumption.
    + split.
      * eapply instruction_steps_append; [exact MachinePrefix|].
        eapply instruction_steps_append; eassumption.
      * split; [exact Return|]. split; [apply returned_state_caller|].
        intros other xs ND NP NT NU NR NO A. apply Frame2; try assumption. apply Frame1; assumption.
Qed.

Theorem nonempty_call_run_agrees (source : fintype.ordinal (S d) -> nat)
    (p : model_permutation (S d)) c caller initial :
  (forall i, uint (Z.of_nat (source i))) ->
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat (S d)))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd (words source) -> array_at c bp (words (model_destination p)) ->
  exists result c' llvm_final machine_final steps code terminated,
    model_permute source p = Some result /\
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output result c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    runs (denote_function FullCFG.function
      (permute_arguments (cell_layout layout) (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr code))) /\
    opModel.run (sequential_opmodel None (sail_tiny_x86_sem true)) (S steps)
      (return_condition (machine_address (return_pc frame))) (sst initial) initial =
      Exec.make [(machine_final, existT (sst machine_final) terminated)] [] /\
    abi_return layout program_bytes frame initial machine_final (Int.repr code) /\
    snd llvm_final = snd caller /\
    (forall other xs, other <> bd -> other <> bp -> other <> bt -> other <> bu ->
      other <> trace -> other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Values Entry Related Data Perm.
  destruct (nonempty_call_agrees source p c caller initial Values Entry Related Data Perm)
    as (result & c' & llvm_final & machine_final & steps & code & Model & FinalRelated &
      ResultCode & Result & LLVM & Steps & Return & Caller & Frame).
  destruct (instruction_steps_run (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) steps initial machine_final
    (sst initial) Steps
    (returned_state_terminates layout program_bytes frame initial machine_final (Int.repr code) Return))
    as (terminated & Run).
  exists result, c', llvm_final, machine_final, steps, code, terminated.
  split; [exact Model|]. split; [exact FinalRelated|]. split; [exact ResultCode|]. split; [exact Result|].
  split; [exact LLVM|]. split; [exact Run|]. split; [exact Return|]. split; assumption.
Qed.
End NonemptyCall.

Print Assumptions nonempty_call_agrees.
Print Assumptions nonempty_call_run_agrees.
