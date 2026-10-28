(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks CheckedPrefix FixedBlocks Fixed FixedPrefix
  SearchBlocks FillBlocks Fill FillLoop NormalizedPrefix MainSetup MainPrefix CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Prefix X86ModelTypes
  X86NormalizationModel X86NormalizedPrefix X86MainSetup.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section MainPrefixAgreement.
Context (layout : finite_layout) (frame : call_frame layout program_bytes)
    (d : nat) (source : fintype.ordinal (S d) -> nat) (p : model_permutation (S d))
    (bd bp bt bu trace output : Values.block).
Hypothesis Size : (S d <= 1024)%nat.
Hypothesis SourceUInt : forall x, uint (Z.of_nat (source x)).
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (DT : bd <> bt)
    (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu)
    (DO : bd <> output) (PO : bp <> output) (OU : output <> bu) (OT : output <> bt).
Hypotheses (CD : (S d <= block_words (cell_layout layout) bd)%nat)
    (CP : (S d <= block_words (cell_layout layout) bp)%nat)
    (CT : (S d <= block_words (cell_layout layout) bt)%nat)
    (CU : (S d <= block_words (cell_layout layout) bu)%nat)
    (CR : (2 * S d <= block_words (cell_layout layout) trace)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).

Theorem main_prefix_agrees c caller initial :
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat (S d)))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd (words source) -> array_at c bp (words (model_destination p)) ->
  exists q c' llvm' machine' steps,
    model_normalize source p = Some q /\
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @ClightMain.loop_arrays d bd bp trace output c' source q [] /\
    main_registers (cell_layout layout) d bd bp trace output llvm' /\
    block_steps (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry"%string) (Name "entry"%string)
      (llvm_entry_state layout (S d) bd bp bt bu trace output caller)
      (Name "while.end105"%string) (Name "while.cond106"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps initial machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 275)) /\
    read_reg_seq_state r12 machine' = Some (machine_address (Z.of_nat d)) /\
    read_reg_seq_state r15 machine' = Some (machine_address (2 * Z.of_nat (S d))) /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Entry Related AD AP.
  destruct (@normalized_prefix_agrees layout frame d source p bd bp bt bu trace output Size SourceUInt
    DP DU DT PU PT TU DO PO CD CP CT CU CO c caller initial Entry Related AD AP)
    as (q & c' & llvm1 & machine1 & count1 & Normalized & Related1 & D1 & P1 & LLVM1 & Machine1 &
      Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1 & Other1 & Frame1 & Fields1 & Zeros1).
  destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat (S d))))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output))
    as (N & Data & Perm & Target & Used & Trace & Output).
  assert (Registers : forall id value, normalized_prefix_unmodified id ->
      Maps.lookup id (locals (llvm_entry_state layout (S d) bd bp bt bu trace output caller)) = Some value ->
      Maps.lookup id (locals llvm1) = Some value).
  { intros id value Outside At. rewrite Other1 by exact Outside. exact At. }
  pose (llvm2 := main_preheader_state llvm1 (Z.of_nat (S d))
    (block_address (cell_layout layout) bp) (block_provenance (cell_layout layout) bp)
    (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)).
  assert (Setup : runs (denote_block (proj1_sig main_preheader) (Name "if.end103"%string)
      (Some (empty_varargs_pointer (fst caller)))) llvm1 llvm2 (inl (Name "while.cond106"%string))).
  { apply main_preheader_runs; [lia| | |]; apply Registers;
      try normalized_unchanged; assumption. }
  assert (MemoryLLVM : fst llvm2 = fst llvm1) by apply main_preheader_memory.
  pose proof (main_preheader_bindings llvm1 (Z.of_nat (S d))
    (block_address (cell_layout layout) bp) (block_provenance (cell_layout layout) bp)
    (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)) as Bindings.
  replace (Z.of_nat (S d) - 1) with (Z.of_nat d) in Bindings by lia.
  destruct Bindings as (Top & PermTop & DataTop & TraceCapacity).
  destruct (main_setup_path true layout frame initial machine1 (S d) bd bp bt bu trace output
    ltac:(lia) Code1 Present1 Arguments1 Stack1 PC1)
    as (machine2 & Machine2 & MemoryMachine & Code2 & Present2 & Arguments2 & Stack2 & PC2 & Top2 & Capacity2).
  replace (Z.of_nat (S d) - 1) with (Z.of_nat d) in Top2 by lia.
  exists q, c', llvm2, machine2, (count1 + 4)%nat.
  split; [exact Normalized|]. split.
  - split.
    + change (cells_related (cell_layout layout) c' (fst llvm2)).
      rewrite MemoryLLVM. exact (proj1 Related1).
    + rewrite MemoryMachine. exact (proj2 Related1).
  - split.
    + constructor; try assumption.
      * intros k value At. destruct k; discriminate.
      * apply Zeros1; congruence.
      * intros k K. change (k < 2 * S d)%nat in K.
        exact (proj1 (proj1 Related1 trace k ltac:(lia))).
    + split.
      * constructor; try assumption.
        all: try (unfold llvm2; rewrite main_preheader_other by
          (unfold main_preheader_modified; simpl; intuition discriminate);
          apply Registers; [normalized_unchanged|assumption]).
        destruct Fields1. constructor; unfold llvm2; rewrite main_preheader_other by
          (unfold main_preheader_modified; simpl; intuition discriminate); assumption.
      * split.
        -- eapply block_steps_append; [exact LLVM1|].
           eapply steps_next; [exact (proj2_sig main_preheader)|exact Setup|constructor].
        -- split.
           ++ eapply instruction_steps_append; eassumption.
           ++ split; [exact Code2|]. split; [exact Present2|]. split; [exact Arguments2|].
              split; [exact Stack2|]. split; [exact PC2|]. split; [exact Top2|].
              split; assumption.
Qed.
End MainPrefixAgreement.

Print Assumptions main_prefix_agrees.
