(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightValidation.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks CheckedPrefix CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Prefix X86ValidationPass.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section CheckedPrefixAgreement.
Context (layout : finite_layout) (frame : call_frame layout program_bytes)
    (size : nat) (xs destinations : list Z) (destination : nat -> nat)
    (bd bp bt bu trace output : Values.block).
Hypothesis Size : (0 < size <= 1024)%nat.
Hypothesis Length : List.length xs = size.
Hypothesis Destinations : forall k, (k < size)%nat ->
  nth_error destinations k = Some (Z.of_nat (destination k)).
Hypothesis Bounded : forall k, (k < size)%nat -> (destination k < size)%nat.
Hypothesis Injective : forall k q, (k < size)%nat -> (q < size)%nat ->
  destination k = destination q -> k = q.
Hypotheses (DU : bd <> bu) (DT : bd <> bt) (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu)
    (DO : bd <> output) (PO : bp <> output).
Hypotheses (CD : (size <= block_words (cell_layout layout) bd)%nat)
    (CP : (size <= block_words (cell_layout layout) bp)%nat)
    (CT : (size <= block_words (cell_layout layout) bt)%nat)
    (CU : (size <= block_words (cell_layout layout) bu)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).

Theorem checked_prefix_agrees c caller initial :
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat size))
    bd bp bt bu trace output initial ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  array_at c bd xs -> array_at c bp destinations ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    ClightValidation.validation_memory size xs destinations destination bd bp bt bu size c' /\
    block_steps (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry"%string) (Name "entry"%string)
      (llvm_entry_state layout size bd bp bt bu trace output caller)
      (Name "if.end29"%string) (Name "if.end43.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame)))
      (18 + 18 * size) initial machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout size bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 147)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat size)) /\
    (forall id, check_unmodified id -> Maps.lookup id (locals llvm') =
      Maps.lookup id (locals (llvm_entry_state layout size bd bp bt bu trace output caller))) /\
    (forall other values, other <> output -> other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values) /\
    output_registers (cell_layout layout) output llvm' /\
    (output <> bu -> output <> bt -> array_at c' output [0; 0; 0]).
Proof.
  intros Entry Related AD AP.
  destruct (initialized_prefix_agrees layout frame size bd bp bt bu trace output c caller initial
    Size Entry CO CU Related)
    as (c1 & c2 & llvm2 & machine2 & Stores & Zeros & Related2 & LLVMInit & MachineInit &
      Code2 & Present2 & PC2 & Arguments2 & Stack2 & Locals2 & Fields2).
  assert (Initial : ClightValidation.validation_memory size xs destinations destination bd bp bt bu 0 c2).
  { constructor.
    - eapply zero_stores_array; [exact Zeros|exact DU|].
      eapply output_stores_array; eassumption.
    - eapply zero_stores_array; [exact Zeros|exact PU|].
      eapply output_stores_array; eassumption.
    - intros k K. exact (proj1 (proj1 Related2 bt k ltac:(lia))).
    - intros k K. exact (proj1 (proj1 Related2 bu k ltac:(lia))).
    - intros q value Q. lia.
    - intros q Q Fresh. eapply zero_stores_values; [exact Zeros|lia]. }
  destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat size)))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output))
    as [N [D [P [T [U [R O]]]]]].
  assert (N2 : Maps.lookup (Name "v1"%string) (locals llvm2) =
      Some (word_value (Int.repr (Z.of_nat size)))).
  { rewrite Locals2 by (repeat split; discriminate). exact N. }
  assert (D2 : Maps.lookup (Name "v2"%string) (locals llvm2) =
      Some (mapped_pointer (cell_layout layout) bd)).
  { rewrite Locals2 by (repeat split; discriminate). exact D. }
  assert (P2 : Maps.lookup (Name "v3"%string) (locals llvm2) =
      Some (mapped_pointer (cell_layout layout) bp)).
  { rewrite Locals2 by (repeat split; discriminate). exact P. }
  assert (T2 : Maps.lookup (Name "v4"%string) (locals llvm2) =
      Some (mapped_pointer (cell_layout layout) bt)).
  { rewrite Locals2 by (repeat split; discriminate). exact T. }
  assert (U2 : Maps.lookup (Name "v5"%string) (locals llvm2) =
      Some (mapped_pointer (cell_layout layout) bu)).
  { rewrite Locals2 by (repeat split; discriminate). exact U. }
  destruct (@validation_pass_agrees true layout frame initial size xs destinations destination
    bd bp bt bu trace output (proj2 Size) Length Destinations Bounded Injective
    DU DT PU PT TU CD CP CT CU (Name "if.end10"%string)
    (Some (empty_varargs_pointer (fst caller))) c2 llvm2 machine2
    (proj1 Size) Related2 Initial N2 D2 P2 T2 U2 Code2 Present2 Arguments2 Stack2 PC2)
    as (c' & llvm' & machine' & RelatedFinal & InvFinal & LLVMValidation & MachineValidation &
      CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal &
      CounterFinal & LocalsFinal & FrameFinal).
  exists c', llvm', machine'. split; [exact RelatedFinal|]. split; [exact InvFinal|]. split.
  - eapply block_steps_append; eassumption.
  - split.
    + replace (18 + 18 * size)%nat with ((16 + 4 * size) + (14 * size + 2))%nat by lia.
      eapply instruction_steps_append; eassumption.
    + split; [exact CodeFinal|]. split; [exact PresentFinal|].
      split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
      split; [exact PCFinal|]. split; [exact CounterFinal|]. split.
      * intros id [Prefix [Count Modified]]. rewrite LocalsFinal by assumption.
        apply Locals2, Prefix.
      * split.
        -- intros other values NotOutput NotUsed NotTarget A.
           apply FrameFinal; try assumption.
           eapply zero_stores_array; [exact Zeros|exact NotUsed|].
           eapply output_stores_array; eassumption.
        -- split.
           ++ destruct Fields2. constructor; rewrite LocalsFinal by
                (unfold validation_modified; simpl; intuition discriminate); assumption.
           ++ intros NotUsed NotTarget. apply FrameFinal; try assumption.
              eapply zero_stores_array; [exact Zeros|exact NotUsed|].
              exact (output_stores_zero c output c1 Stores).
Qed.
End CheckedPrefixAgreement.

Print Assumptions checked_prefix_agrees.
