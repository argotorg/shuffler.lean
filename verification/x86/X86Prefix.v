(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers Values Memory.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry
  Initialize Prefix CallBoundary FullCall.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Control X86Instructions
  X86Compare X86Program X86Execution X86Prologue X86Initialize X86Call
  X86Arguments X86Size X86UsedZero.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition llvm_entry_state layout size bd bp bt bu trace output caller :=
  call_state caller (word_value (Int.repr (Z.of_nat size)))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output).

Lemma arguments_after_size layout size bd bp bt bu trace output before after base :
  core_arguments layout size bd bp bt bu trace output before ->
  nonempty_size_result base before after ->
  core_arguments layout size bd bp bt bu trace output after.
Proof.
  intros Arguments Result. apply (core_arguments_frame _ _ _ _ _ _ _ _ before after Arguments).
  intros reg At. cbn in At.
  destruct At as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    apply (nonempty_size_other base before after Result); discriminate.
Qed.

Lemma arguments_after_zero layout size bd bp bt bu trace output
    (frame : call_frame layout program_bytes) before after :
  core_arguments layout size bd bp bt bu trace output before ->
  used_zero_frame layout frame before after ->
  core_arguments layout size bd bp bt bu trace output after.
Proof.
  intros Arguments Result. apply (core_arguments_frame _ _ _ _ _ _ _ _ before after Arguments).
  intros reg At. cbn in At.
  destruct At as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    apply (used_zero_other layout frame before after Result); discriminate.
Qed.

Theorem initialized_machine_prefix layout (frame : call_frame layout program_bytes)
    size bd bp bt bu trace output c c1 c' initial :
  (0 < size <= 1024)%nat ->
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat size)) bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  machine_cells_related layout c (archState.memory (sst initial)) ->
  output_stores c output c1 -> zero_stores bu 0 size c1 c' ->
  exists final,
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) (16 + 4 * size) initial final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 87)) /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final.
Proof.
  intros Range Entry OutputCapacity UsedCapacity Related [c01 [c02 [W0 [W1 W2]]]] Zeros.
  destruct (enter_call true layout frame (Int.repr (Z.of_nat size)) bd bp bt bu trace output
    c c01 c02 c1 initial Entry OutputCapacity Related W0 W1 W2)
    as [Enter [RelatedBody [Code [Present [PC Stack]]]]].
  pose (body := call_body_state layout frame output initial).
  pose proof (call_body_arguments layout frame size bd bp bt bu trace output initial Entry) as Arguments.
  destruct (core_size _ _ _ _ _ _ _ _ _ Arguments) as [old [Old Low]].
  assert (LowSize : low_register32 7 old = Z_to_bv 32 (Z.of_nat size)).
  { change (bv_extract 0 32 old = Z_to_bv 32 (Z.of_nat size)).
    unfold machine_word in Low. rewrite Int.unsigned_repr in Low;
      [exact Low|change Int.max_unsigned with 4294967295; lia]. }
  destruct (nonempty_size_path true layout frame body old (Z.of_nat size)
    ltac:(lia) Code Present PC Old LowSize) as [sized [SizeSteps SizeResult]].
  assert (SizeArguments : core_arguments layout size bd bp bt bu trace output sized).
  { eapply arguments_after_size; eassumption. }
  assert (SizeStack : call_stack layout frame initial sized).
  { apply (call_stack_same_memory layout frame initial body sized Stack).
    - apply (nonempty_size_other _ _ _ SizeResult); discriminate.
    - apply (nonempty_size_other _ _ _ SizeResult); discriminate.
    - exact (nonempty_size_memory _ _ _ SizeResult). }
  assert (SizeRelated : machine_cells_related layout c1 (archState.memory (sst sized))).
  { rewrite (nonempty_size_memory _ _ _ SizeResult). exact RelatedBody. }
  assert (SizeOld : read_reg_seq_state rdi sized = Some old).
  { rewrite (nonempty_size_other _ _ _ SizeResult) by discriminate. exact Old. }
  destruct (used_zero_preheader true layout frame bu size old sized c1 c'
    Range UsedCapacity Zeros (nonempty_size_code _ _ _ SizeResult)
    (nonempty_size_present _ _ _ SizeResult) (nonempty_size_pc _ _ _ SizeResult)
    (core_used _ _ _ _ _ _ _ _ _ SizeArguments) SizeOld LowSize SizeRelated)
    as [final [ZeroSteps [RelatedFinal [CodeFinal [PresentFinal [PCFinal [Counter Frame]]]]]]].
  exists final. split.
  - replace (16 + 4 * size)%nat with (9 + (6 + (1 + 4 * size)))%nat by lia.
    eapply instruction_steps_append; [exact Enter|].
    eapply instruction_steps_append; [exact SizeSteps|exact ZeroSteps].
  - split; [exact RelatedFinal|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact PCFinal|]. split.
    + eapply arguments_after_zero; eassumption.
    + apply (call_stack_preserved layout frame initial sized final SizeStack).
      * apply (used_zero_other _ _ _ _ Frame); discriminate.
      * apply (used_zero_other _ _ _ _ Frame); discriminate.
      * exact (used_zero_stack _ _ _ _ Frame).
Qed.

Theorem initialized_prefix_agrees layout (frame : call_frame layout program_bytes)
    size bd bp bt bu trace output c caller initial :
  (0 < size <= 1024)%nat ->
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat size)) bd bp bt bu trace output initial ->
  (3 <= block_words (cell_layout layout) output)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  llvm_machine_related layout c (fst caller) (archState.memory (sst initial)) ->
  exists c1 c' llvm_final machine_final,
    output_stores c output c1 /\ zero_stores bu 0 size c1 c' /\
    llvm_machine_related layout c' (fst llvm_final) (archState.memory (sst machine_final)) /\
    block_steps (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry"%string) (Name "entry"%string)
      (llvm_entry_state layout size bd bp bt bu trace output caller)
      (Name "if.end10"%string) (Name "if.end17.preheader"%string) llvm_final /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) (16 + 4 * size) initial machine_final /\
    code_at machine_final (entry_pc frame) program_bytes /\ registers_present machine_final /\
    read_reg_seq_state rip machine_final = Some (machine_address (entry_pc frame + 87)) /\
    core_arguments layout size bd bp bt bu trace output machine_final /\
    call_stack layout frame initial machine_final /\
    (forall id, prefix_unmodified id ->
      Maps.lookup id (locals llvm_final) =
      Maps.lookup id (locals (llvm_entry_state layout size bd bp bt bu trace output caller))) /\
    output_registers (cell_layout layout) output llvm_final.
Proof.
  intros Size Entry OutputCapacity UsedCapacity [LLVM Machine].
  pose (llvm_initial := call_state caller (word_value (Int.repr (Z.of_nat size)))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output)).
  assert (LLVMInitial : cells_related (cell_layout layout) c (fst llvm_initial))
    by (apply call_state_related, LLVM).
  destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat size)))
    (mapped_pointer (cell_layout layout) bd) (mapped_pointer (cell_layout layout) bp)
    (mapped_pointer (cell_layout layout) bt) (mapped_pointer (cell_layout layout) bu)
    (mapped_pointer (cell_layout layout) trace) (mapped_pointer (cell_layout layout) output))
    as [N [D [P [T [U [R O]]]]]].
  destruct (@initialized_prefix (cell_layout layout) output bu size
    (Some (empty_varargs_pointer (fst caller))) c llvm_initial
    Size OutputCapacity UsedCapacity LLVMInitial N O U)
    as [c1 [c' [llvm_final [Stores [Zeros [LLVMFinal [LLVMRun Rest]]]]]]].
  destruct (initialized_machine_prefix layout frame size bd bp bt bu trace output
    c c1 c' initial Size Entry OutputCapacity UsedCapacity Machine Stores Zeros)
    as [machine_final [MachineRun [MachineFinal [Code [Present [PC [Arguments Stack]]]]]]].
  exists c1, c', llvm_final, machine_final.
  split; [exact Stores|]. split; [exact Zeros|].
  split; [split; assumption|]. split; [exact LLVMRun|]. split; [exact MachineRun|].
  split; [exact Code|]. split; [exact Present|]. split; [exact PC|].
  split; [exact Arguments|]. split; [exact Stack|]. exact Rest.
Qed.

Print Assumptions initialized_machine_prefix.
Print Assumptions initialized_prefix_agrees.
