(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index MainPrefix Choose.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86ModelTypes X86LoopModel
  X86MainLoopCore X86ExchangeAgreement.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section MainLoop.
Context (layout : finite_layout) (frame : call_frame layout program_bytes) (initial : seq_state)
    (d : nat) (bd bp bt bu trace output : Values.block).
Hypotheses (DP : bd <> bp) (DT : bd <> trace) (DO : bd <> output)
    (PT : bp <> trace) (PO : bp <> output) (TO : trace <> output).
Hypothesis Size : (S d <= 1024)%nat.
Hypotheses (CD : (S d <= block_words (cell_layout layout) bd)%nat)
    (CP : (S d <= block_words (cell_layout layout) bp)%nat)
    (CT : (2 * S d <= block_words (cell_layout layout) trace)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).
Local Notation MachineState := (main_machine_state layout frame initial d bd bp bt bu trace output).

Theorem main_loop_agrees fuel source (p : model_permutation (S d))
    depths c llvm machine from varargs :
  (model_rank p < fuel)%nat -> (List.length depths + fuel <= 2 * S d)%nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm -> MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 275)) ->
  exists c' llvm' machine' steps code,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output (model_run fuel source p depths) c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs from (Name "while.cond106"%string) llvm llvm'
      (word_value (Int.repr code)) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax machine' = Some (machine_address code) /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  eapply (@main_loop_from_exchange_agreements layout frame initial d bd bp bt bu trace output Size CP).
  - intros source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Position Related Arrays Registers Binding Equal (Code & Present & Arguments & Stack & Top & Capacity) PC Selected.
    destruct (@equal_exchange_agrees true layout frame initial d bd bp bt bu trace output
      DP DT DO PT PO TO Size CD CP CT CO source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Position Related Arrays Registers Binding Equal Code Present Arguments Stack PC Top Selected Capacity)
      as (c' & llvm' & machine' & RelatedFinal & ArraysFinal & RegistersFinal & LLVM & Machine & Frame &
        CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & TopFinal & CapacityFinal).
    exists c', llvm', machine', 10%nat.
    split; [exact RelatedFinal|]. split; [exact ArraysFinal|]. split; [exact RegistersFinal|].
    split; [exact LLVM|]. split; [exact Machine|]. split.
    + exact (conj CodeFinal (conj PresentFinal (conj ArgumentsFinal (conj StackFinal (conj TopFinal CapacityFinal))))).
    + split; assumption.
  - intros source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Position Values Different Near TraceSpace Related Arrays Registers Binding
      (Code & Present & Arguments & Stack & Top & Capacity) PC Selected.
    destruct (@successful_exchange_agrees true layout frame initial d bd bp bt bu trace output
      DP DT DO PT PO TO Size CD CP CT CO source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Values Position Different Near TraceSpace Related Arrays Registers Binding
      Code Present Arguments Stack PC Top Selected Capacity)
      as (c' & llvm' & machine' & RelatedFinal & ArraysFinal & RegistersFinal & LLVM & Machine & Frame &
        CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & TopFinal & CapacityFinal).
    exists c', llvm', machine', 22%nat.
    split; [exact RelatedFinal|]. split; [exact ArraysFinal|]. split; [exact RegistersFinal|].
    split; [exact LLVM|]. split; [exact Machine|]. split.
    + exact (conj CodeFinal (conj PresentFinal (conj ArgumentsFinal (conj StackFinal (conj TopFinal CapacityFinal))))).
    + split; assumption.
  - intros source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Values Different Far Related Arrays Registers Binding
      (Code & Present & Arguments & Stack & Top & Capacity) PC Selected.
    destruct (@blocked_exchange_agrees true layout frame initial d bd bp bt bu trace output
      DP DT DO PT PO TO Size CD CP CT CO source0 p0 depths0 position0 c0 llvm0 machine0 from0 varargs0
      Values Different Far Related Arrays Registers Binding Code Present Arguments Stack PC Top Selected Capacity)
      as (c' & llvm' & machine' & RelatedFinal & Result & RegistersFinal & LLVM & Machine & Frame &
        CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & Return & TopFinal & CapacityFinal).
    exists c', llvm', machine', 13%nat.
    split; [exact RelatedFinal|]. split; [exact Result|]. split; [exact LLVM|]. split; [exact Machine|].
    split; [exact CodeFinal|]. split; [exact PresentFinal|]. split; [exact StackFinal|].
    split; [exact PCFinal|]. split; assumption.
Qed.

Corollary main_loop_nonempty_agrees source (p : model_permutation (S d)) c llvm machine from varargs :
  (forall i, uint (Z.of_nat (source i))) ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p [] ->
  main_registers (cell_layout layout) d bd bp trace output llvm -> MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 275)) ->
  exists c' llvm' machine' steps code,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output (model_nonempty source p) c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs from (Name "while.cond106"%string) llvm llvm'
      (word_value (Int.repr code)) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax machine' = Some (machine_address code) /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  intros Values Related Arrays Registers State PC.
  exact (main_loop_agrees (S (model_rank p)) source p [] c llvm machine from varargs
    (Nat.lt_succ_diag_r _) (model_initial_budget d p) Values Related Arrays Registers State PC).
Qed.
End MainLoop.

Print Assumptions main_loop_agrees.
Print Assumptions main_loop_nonempty_agrees.
