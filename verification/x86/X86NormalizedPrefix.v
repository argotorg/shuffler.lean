(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks CheckedPrefix FixedBlocks Fixed FixedPrefix
  SearchBlocks FillBlocks Fill FillLoop NormalizedPrefix CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Prefix X86FixedPrefix
  X86FillAgreement X86ModelTypes X86NormalizationModel.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section NormalizedPrefixAgreement.
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

Theorem normalized_prefix_agrees c caller initial :
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat (S d)))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd (words source) -> array_at c bp (words (model_destination p)) ->
  exists q c' llvm' machine' steps,
    model_normalize source p = Some q /\
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    array_at c' bd (words source) /\ array_at c' bp (words (model_destination q)) /\
    block_steps (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry"%string) (Name "entry"%string)
      (llvm_entry_state layout (S d) bd bp bt bu trace output caller)
      (Name "if.end103"%string) (Name "while.end105"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps initial machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 262)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (S d))) /\
    (forall id, normalized_prefix_unmodified id -> Maps.lookup id (locals llvm') =
      Maps.lookup id (locals (llvm_entry_state layout (S d) bd bp bt bu trace output caller))) /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values) /\
    output_registers (cell_layout layout) output llvm' /\
    (output <> bu -> output <> bt -> output <> bp -> array_at c' output [0; 0; 0]).
Proof.
  intros Entry Related AD AP.
  destruct (model_normalization_fill (S d) source p) as (q & result & Normalized & Raw & Result).
  destruct (@fixed_prefix_agrees layout frame d source p bd bp bt bu trace output Size SourceUInt
    DP DU DT PU PT TU DO PO CD CP CT CU CO c caller initial Entry Related AD AP)
    as (c1 & llvm1 & machine1 & count1 & Related1 & Arrays1 & LLVMFixed & MachineFixed &
      Bound1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1 & Other1 & Frame1 & Fields1 & Zeros1).
  pose proof (model_fixed_fill_arrays d source p bd bp bt bu c1 Arrays1) as FillArrays.
  destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat (S d))))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output))
    as (N & Data & Perm & Target & Used & Trace & Output).
  assert (Registers : forall id value, fixed_prefix_unmodified id ->
      Maps.lookup id (locals (llvm_entry_state layout (S d) bd bp bt bu trace output caller)) = Some value ->
      Maps.lookup id (locals llvm1) = Some value).
  { intros id value Outside At. rewrite Other1 by exact Outside. exact At. }
  assert (TargetUInt : forall x, uint (Z.of_nat (model_target source p x))).
  { apply model_target_uint, SourceUInt. }
  destruct (@fill_pass_agrees true layout frame initial (S d) source (model_target source p)
    bd bt bp bu trace output Size DP DU (not_eq_sym PT) TU PU CD CT CP CU SourceUInt TargetUInt
    (Name "if.end57"%string) (Some (empty_varargs_pointer (fst caller))) c1 llvm1 machine1
    (model_fixed_assignment source p) (model_fixed_reserved source p) result
    ltac:(lia) Related1 FillArrays Raw
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact N])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Data])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Target])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Perm])
    ltac:(apply Registers; [unfold fixed_prefix_unmodified, check_unmodified, prefix_unmodified,
      entry_unmodified, initialize_unmodified, validation_modified, fixed_unmodified,
      fixed_modified; simpl; intuition discriminate|exact Used])
    Code1 Present1 Arguments1 Stack1 PC1)
    as (reserved & c' & llvm' & machine' & count2 & RelatedFinal & ArraysFinal & LLVMFill & MachineFill &
      OtherFinal & FrameFinal & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & CounterFinal).
  destruct ArraysFinal as [D T P U].
  exists q, c', llvm', machine', (count1 + count2)%nat.
  split; [exact Normalized|]. split; [exact RelatedFinal|]. split; [exact D|]. split.
  - assert (Same : words (fun x => fintype.nat_of_ord (result x)) = words (model_destination q)).
    { apply words_ext. intro x. rewrite Result. reflexivity. }
    rewrite <- Same. exact P.
  - split.
    + eapply block_steps_append; eassumption.
    + split.
      * eapply instruction_steps_append; eassumption.
      * split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
        split; [exact PCFinal|]. split; [exact CounterFinal|]. split.
        -- intros id [Before Fill]. rewrite OtherFinal by exact Fill. apply Other1, Before.
        -- split.
           ++ intros other values NotOutput NotUsed NotTarget NotPerm A.
              apply FrameFinal; try assumption. apply Frame1; assumption.
           ++ split.
              ** destruct Fields1. constructor; rewrite OtherFinal by
                   (unfold fill_unmodified, fill_body_unmodified, fill_modified, search_modified;
                    simpl; intuition discriminate); assumption.
              ** intros NotUsed NotTarget NotPerm. apply FrameFinal; try assumption.
                 apply Zeros1; assumption.
Qed.
End NormalizedPrefixAgreement.

Print Assumptions normalized_prefix_agrees.
