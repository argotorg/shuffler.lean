(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers Values Memory.
Require Import ClightMemory ClightValidation.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  ValidationBlocks Validation.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86ValidationEntry X86ValidationAgreement.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section ValidationPass.
Context (nondet : bool) (layout : finite_layout)
    (frame : call_frame layout program_bytes) (initial : seq_state)
    (size : nat) (xs destinations : list Z) (destination : nat -> nat)
    (bd bp bt bu trace output : Values.block).
Hypothesis Size : (size <= 1024)%nat.
Hypothesis Length : List.length xs = size.
Hypothesis Destinations : forall k, (k < size)%nat ->
  nth_error destinations k = Some (Z.of_nat (destination k)).
Hypothesis Bounded : forall k, (k < size)%nat -> (destination k < size)%nat.
Hypothesis Injective : forall k q, (k < size)%nat -> (q < size)%nat ->
  destination k = destination q -> k = q.
Hypotheses (DU : bd <> bu) (DT : bd <> bt) (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu).
Hypotheses (CD : (size <= block_words (cell_layout layout) bd)%nat)
    (CP : (size <= block_words (cell_layout layout) bp)%nat)
    (CT : (size <= block_words (cell_layout layout) bt)%nat)
    (CU : (size <= block_words (cell_layout layout) bu)%nat).

Let invariant := ClightValidation.validation_memory size xs destinations destination bd bp bt bu.

Theorem validation_pass_agrees from varargs c llvm machine :
  (0 < size)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  invariant 0 c ->
  Maps.lookup (Name "v1"%string) (locals llvm) = Some (word_value (Int.repr (Z.of_nat size))) ->
  Maps.lookup (Name "v2"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)) ->
  Maps.lookup (Name "v3"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bp) (block_provenance (cell_layout layout) bp)) ->
  Maps.lookup (Name "v4"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bt) (block_provenance (cell_layout layout) bt)) ->
  Maps.lookup (Name "v5"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bu) (block_provenance (cell_layout layout) bu)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout size bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 87)) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    invariant size c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17.preheader"%string) llvm
      (Name "if.end29"%string) (Name "if.end43.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) (14 * size + 2) machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout size bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 147)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat size)) /\
    (forall id, id <> Name "wide.trip.count299"%string -> ~ In id validation_modified ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Positive Related Inv N Data Perm Target Used Code Present Arguments Stack PC.
  pose (llvm1 := set_local llvm (Name "wide.trip.count299"%string) (index_value (Z.of_nat size))).
  assert (Locals1 : validation_locals (cell_layout layout) size bd bp bt bu llvm1).
  { constructor; unfold llvm1;
      first [apply lookup_local_same | rewrite lookup_local_other by discriminate; assumption]. }
  destruct (validation_preheader nondet layout frame initial machine size bd bp bt bu trace output
    Code Present Arguments Stack PC)
    as [machine1 [MachineEntry [Memory1 [Code1 [Present1 [Arguments1 [Stack1 [PC1 Counter1]]]]]]]].
  assert (Related1 : llvm_machine_related layout c (fst llvm1) (archState.memory (sst machine1))).
  { destruct Related as [LLVM Machine]. split.
    - unfold llvm1. rewrite memory_set_local. exact LLVM.
    - rewrite Memory1. exact Machine. }
  destruct (validation_loop_agrees nondet layout frame initial size xs destinations destination
    bd bp bt bu trace output Size Length Destinations Bounded Injective DU DT PU PT TU CD CP CT CU
    varargs size 0 (Name "if.end17.preheader"%string) c llvm1 machine1
    Positive eq_refl Related1 Inv Locals1 (or_introl (conj eq_refl eq_refl))
    Code1 Present1 Arguments1 Stack1 PC1 Counter1)
    as [c' [llvm' [machine' [RelatedFinal [InvFinal [LLVMLoop [MachineLoop
      [CodeFinal [PresentFinal [ArgumentsFinal [StackFinal [PCFinal
        [CounterFinal [Other Frame]]]]]]]]]]]]]].
  exists c', llvm', machine'. split; [exact RelatedFinal|]. split; [exact InvFinal|]. split.
  - eapply steps_next; [exact (proj2_sig FullCFG.validation_preheader)| |exact LLVMLoop].
    exact (@validation_preheader_runs (cell_layout layout) size xs bd bp bt bu
      Size Length DU DT PU PT TU CD CP CT CU from varargs llvm N).
  - split.
    + replace (14 * size + 2)%nat with (1 + (14 * size + 1))%nat by lia.
      eapply instruction_steps_append; [exact MachineEntry|exact MachineLoop].
    + split; [exact CodeFinal|]. split; [exact PresentFinal|].
      split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
      split; [exact PCFinal|]. split; [exact CounterFinal|]. split; [|exact Frame].
      intros id Different Outside. rewrite Other by exact Outside. unfold llvm1.
      rewrite lookup_local_other by exact Different. reflexivity.
Qed.
End ValidationPass.

Print Assumptions validation_pass_agrees.
