(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightValidation ClightNormalize ModelArrays ClightCorrect.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks CheckedPrefix FixedBlocks Fixed FixedPrefix CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Prefix X86CheckedPrefix X86FixedAgreement X86ModelTypes.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section FixedPrefixAgreement.
Context (layout : finite_layout) (frame : call_frame layout program_bytes)
    (d : nat) (source : fintype.ordinal (S d) -> nat) (p : model_permutation (S d))
    (bd bp bt bu trace output : Values.block).
Hypothesis Size : (S d <= 1024)%nat.
Hypothesis SourceUInt : forall x, uint (Z.of_nat (source x)).
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (DT : bd <> bt)
    (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu) (DO : bd <> output) (PO : bp <> output).
Hypotheses (CD : (S d <= block_words (cell_layout layout) bd)%nat)
    (CP : (S d <= block_words (cell_layout layout) bp)%nat)
    (CT : (S d <= block_words (cell_layout layout) bt)%nat)
    (CU : (S d <= block_words (cell_layout layout) bu)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).

Theorem fixed_prefix_agrees c caller initial :
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat (S d)))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd (words source) -> array_at c bp (words (model_destination p)) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    FixedPrefix.fixed_prefix_arrays d source p bd bp bt bu c' /\
    block_steps (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry"%string) (Name "entry"%string)
      (llvm_entry_state layout (S d) bd bp bt bu trace output caller)
      (Name "if.end57"%string) (Name "if.end65.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps initial machine' /\
    (19 + 27 * S d <= steps <= 19 + 29 * S d)%nat /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 185)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (S d))) /\
    (forall id, fixed_prefix_unmodified id -> Maps.lookup id (locals llvm') =
      Maps.lookup id (locals (llvm_entry_state layout (S d) bd bp bt bu trace output caller))) /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values) /\
    output_registers (cell_layout layout) output llvm' /\
    (output <> bu -> output <> bt -> output <> bp -> array_at c' output [0; 0; 0]).
Proof.
  intros Entry Related AD AP.
  destruct (@checked_prefix_agrees layout frame (S d) (words source)
    (words (model_destination p)) (destination_at p) bd bp bt bu trace output
    ltac:(lia) (words_length source) (@destination_at_words d p)
    (fun k _ => @destination_at_bound d p k) (@destination_at_injective d p)
    DU DT PU PT TU DO PO CD CP CT CU CO c caller initial Entry Related AD AP)
    as (c1 & llvm1 & machine1 & Related1 & Inv & LLVMCheck & MachineCheck &
      Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1 & Other1 & Frame1 & Fields1 & Zeros1).
  destruct Inv as [D1 P1 WT WU Loads Unused].
  assert (T1 : array_at c1 bt (words (model_target source p))).
  { exact (@target_array_from_destinations d source p c1 bt WT Loads). }
  destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat (S d))))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output))
    as (N & Data & Perm & Target & Used & Trace & Output).
  assert (Registers : forall id value, check_unmodified id ->
      Maps.lookup id (locals (llvm_entry_state layout (S d) bd bp bt bu trace output caller)) = Some value ->
      Maps.lookup id (locals llvm1) = Some value).
  { intros id value Outside At. rewrite Other1 by exact Outside. exact At. }
  assert (TargetUInt : forall x, uint (Z.of_nat (model_target source p x))).
  { apply model_target_uint, SourceUInt. }
  destruct (@fixed_pass_agrees true layout frame initial (S d) source (model_target source p)
    bd bt bp bu trace output Size DP DU (not_eq_sym PT) TU PU CD CT CP CU SourceUInt TargetUInt
    (Name "if.end29"%string) (Some (empty_varargs_pointer (fst caller))) c1 llvm1 machine1
    (model_destination p) ltac:(lia) Related1 D1 T1 P1
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact N])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Data])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Target])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Perm])
    ltac:(apply Registers; [unfold check_unmodified, prefix_unmodified, entry_unmodified,
      initialize_unmodified, validation_modified; simpl; intuition discriminate|exact Used])
    Code1 Present1 Arguments1 Stack1 PC1)
    as (c' & llvm' & machine' & steps & RelatedFinal & ArraysFinal & LLVMFixed & MachineFixed &
      StepsBound & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal &
      CounterFinal & OtherFinal & FrameFinal).
  exists c', llvm', machine', (18 + 18 * S d + steps)%nat.
  split; [exact RelatedFinal|]. split.
  - destruct ArraysFinal as [D T P U]. exact (conj D (conj T (conj P U))).
  - split.
    + eapply block_steps_append; eassumption.
    + split.
      * eapply instruction_steps_append; eassumption.
      * split; [lia|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
        split; [exact PCFinal|]. split; [exact CounterFinal|]. split.
        -- intros id [Before Fixed]. rewrite OtherFinal by exact Fixed. apply Other1, Before.
        -- split.
           ++ intros other values NotOutput NotUsed NotTarget NotPerm A.
              apply FrameFinal; try assumption. apply Frame1; assumption.
           ++ split.
              ** destruct Fields1. constructor; rewrite OtherFinal by
                   (unfold fixed_unmodified, fixed_modified; simpl; intuition discriminate); assumption.
              ** intros NotUsed NotTarget NotPerm. apply FrameFinal; try assumption.
                 apply Zeros1; assumption.
Qed.
End FixedPrefixAgreement.

Print Assumptions fixed_prefix_agrees.
