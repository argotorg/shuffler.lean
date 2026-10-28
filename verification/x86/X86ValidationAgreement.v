(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightValidation.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  ValidationBlocks Validation.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Validation X86LLVMValidation.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section ValidationAgreement.
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

Theorem validation_iteration_agrees from varargs c llvm machine index :
  (index < size)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  invariant index c -> validation_locals (cell_layout layout) size bd bp bt bu llvm ->
  validation_input from llvm (Z.of_nat index) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout size bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 89)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat index)) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    invariant (S index) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17"%string) llvm
      (Name "if.end29"%string)
      (if Z.of_nat (S index) =? Z.of_nat size
       then Name "if.end43.preheader"%string else Name "if.end17"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if Z.of_nat (S index) =? Z.of_nat size then 15%nat else 14%nat) machine machine' /\
    validation_locals (cell_layout layout) size bd bp bt bu llvm' /\
    validation_input (Name "if.end29"%string) llvm' (Z.of_nat (S index)) /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout size bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 147 else 89))) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (S index))) /\
    (forall id, ~ In id validation_modified ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Index [LLVM Machine] Inv Locals Input Code Present Arguments Stack PC Counter.
  destruct Inv as [AD AP WT WU Target Unused].
  assert (Destination : (destination index < size)%nat) by (apply Bounded, Index).
  assert (Fresh : forall k, (k < index)%nat -> destination k <> destination index).
  { intros k K Same. assert (k = index) by (apply Injective; auto; lia). lia. }
  destruct (nth_error xs index) as [value|] eqn:Source.
  2: { apply nth_error_None in Source. lia. }
  pose proof (proj1 (AP index _ (Destinations index Index))) as LoadPerm.
  pose proof (Unused (destination index) Destination Fresh) as LoadUsed.
  destruct (Mem.valid_access_store c Mint32 bu (4 * Z.of_nat (destination index))
    (Vint Int.one) (WU _ Destination)) as [c1 StoreUsed].
  assert (WritableTarget : Mem.valid_access c1 Mint32 bt
      (4 * Z.of_nat (destination index)) Writable).
  { eapply Mem.store_valid_access_1; [exact StoreUsed|exact (WT _ Destination)]. }
  destruct (Mem.valid_access_store c1 Mint32 bt (4 * Z.of_nat (destination index))
    (Vint (Int.repr value)) WritableTarget) as [c2 StoreTarget].
  assert (LoadData : Mem.load Mint32 c1 bd (4 * Z.of_nat index) = Some (Vint (Int.repr value))).
  { rewrite (Mem.load_store_other Mint32 c bu _ _ c1 StoreUsed) by (left; exact DU).
    exact (proj1 (AD index value Source)). }
  destruct (@llvm_validation_step (cell_layout layout) size bd bp bt bu from varargs
    index (destination index) (Int.repr value) c c1 c2 llvm
    ltac:(lia) Destination CD CP CT CU LLVM Locals Input LoadPerm LoadUsed StoreUsed LoadData StoreTarget)
    as [llvm' [LLVMFinal [LLVMSteps [LocalsFinal [InputFinal Other]]]]].
  destruct (@X86Validation.validation_iteration nondet layout frame initial machine
    size index (destination index) bd bp bt bu trace output (Int.repr value) c c1 c2
    ltac:(lia) Destination CD CP CT CU Code Present Arguments Stack PC Counter
    Machine LoadPerm LoadUsed StoreUsed LoadData StoreTarget)
    as [machine' [MachineSteps [MachineFinal [CodeFinal [PresentFinal
      [ArgumentsFinal [StackFinal [PCFinal CounterFinal]]]]]]]].
  exists c2, llvm', machine'. split; [split; assumption|]. split.
  - eapply ClightValidation.validation_memory_step; try eassumption.
    constructor; assumption.
  - split; [exact LLVMSteps|]. split; [exact MachineSteps|].
    split; [exact LocalsFinal|]. split; [exact InputFinal|].
    split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
    split; [exact PCFinal|]. split; [exact CounterFinal|]. split; [exact Other|].
    intros other values NotUsed NotTarget A.
    eapply array_store_disjoint; [|exact NotTarget|exact StoreTarget].
    eapply array_store_disjoint; [exact A|exact NotUsed|exact StoreUsed].
Qed.

Theorem validation_loop_agrees varargs : forall remaining start from c llvm machine,
  (0 < remaining)%nat -> (start + remaining = size)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  invariant start c -> validation_locals (cell_layout layout) size bd bp bt bu llvm ->
  validation_input from llvm (Z.of_nat start) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout size bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 89)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat start)) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    invariant size c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end17"%string) llvm
      (Name "if.end29"%string) (Name "if.end43.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (14 * remaining + 1) machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout size bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 147)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat size)) /\
    (forall id, ~ In id validation_modified ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    (forall other values, other <> bu -> other <> bt ->
      array_at c other values -> array_at c' other values).
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from c llvm machine Positive Sum Related Inv Locals Input
      Code Present Arguments Stack PC Counter; [lia|].
  destruct (validation_iteration_agrees from varargs c llvm machine start ltac:(lia)
    Related Inv Locals Input Code Present Arguments Stack PC Counter)
    as [c1 [llvm1 [machine1 [Related1 [Inv1 [LLVMStep [MachineStep [Locals1 [Input1
      [Code1 [Present1 [Arguments1 [Stack1 [PC1 [Counter1 [Other1 Frame1]]]]]]]]]]]]]]]].
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat (S start) =? Z.of_nat size) = true)
      by (apply Z.eqb_eq; lia).
    rewrite Last in LLVMStep, MachineStep, PC1.
    exists c1, llvm1, machine1. split; [exact Related1|].
    split; [replace size with (S start) by lia; exact Inv1|].
    split; [exact LLVMStep|]. split; [exact MachineStep|].
    split; [exact Code1|]. split; [exact Present1|].
    split; [exact Arguments1|]. split; [exact Stack1|].
    split; [exact PC1|]. split.
    + replace size with (S start) by lia. exact Counter1.
    + split; assumption.
  - assert (More : (Z.of_nat (S start) =? Z.of_nat size) = false)
      by (apply Z.eqb_neq; lia).
    rewrite More in LLVMStep, MachineStep, PC1.
    destruct (IH (S start) (Name "if.end29"%string) c1 llvm1 machine1 ltac:(lia) ltac:(lia)
      Related1 Inv1 Locals1 Input1 Code1 Present1 Arguments1 Stack1 PC1 Counter1)
      as [c' [llvm' [machine' [RelatedFinal [InvFinal [LLVMSteps [MachineSteps
        [CodeFinal [PresentFinal [ArgumentsFinal [StackFinal [PCFinal
          [CounterFinal [OtherFinal FrameFinal]]]]]]]]]]]]]].
    exists c', llvm', machine'. split; [exact RelatedFinal|]. split; [exact InvFinal|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * replace (14 * S (S remaining) + 1)%nat with (14 + (14 * S remaining + 1))%nat by lia.
        eapply instruction_steps_append; eassumption.
      * split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
        split; [exact PCFinal|]. split; [exact CounterFinal|]. split.
        -- intros id Outside. rewrite OtherFinal by exact Outside. apply Other1, Outside.
        -- intros other values NotUsed NotTarget A. apply FrameFinal; try assumption.
           apply Frame1; assumption.
Qed.
End ValidationAgreement.

Print Assumptions validation_iteration_agrees.
Print Assumptions validation_loop_agrees.
