(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightNormalize ModelArrays.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index FixedBlocks Fixed.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86Normalize X86FixedMemory.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Local Notation nat_of_ord := fintype.nat_of_ord.

Section FixedAgreement.
Context (nondet : bool) (layout : finite_layout)
    (frame : call_frame layout program_bytes) (initial : seq_state)
    (count : nat) (source desired : fintype.ordinal count -> nat)
    (bd bt bp bu trace output : Values.block).
Hypothesis Bound : (count <= 1024)%nat.
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (TP : bt <> bp) (TU : bt <> bu) (PU : bp <> bu).
Hypotheses (CD : (count <= block_words (cell_layout layout) bd)%nat)
    (CT : (count <= block_words (cell_layout layout) bt)%nat)
    (CP : (count <= block_words (cell_layout layout) bp)%nat)
    (CU : (count <= block_words (cell_layout layout) bu)%nat).
Hypotheses (SourceUInt : forall x, uint (Z.of_nat (source x)))
    (TargetUInt : forall x, uint (Z.of_nat (desired x))).

Let invariant := @Fixed.fixed_invariant count source desired bd bt bp bu.

Theorem fixed_iteration_agrees from varargs c llvm machine (index : fintype.ordinal count) original :
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  invariant original (nat_of_ord index) c ->
  fixed_registers (cell_layout layout) count bd bt bp bu llvm ->
  fixed_input from llvm (Z.of_nat (nat_of_ord index)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 149)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat (nat_of_ord index))) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    invariant original (S (nat_of_ord index)) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43"%string) llvm
      (Name "if.end57"%string)
      (if Z.of_nat (S (nat_of_ord index)) =? Z.of_nat count
       then Name "if.end65.preheader"%string else Name "if.end43"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if Nat.eqb (source index) (desired index) then 11%nat else 9%nat) machine machine' /\
    fixed_registers (cell_layout layout) count bd bt bp bu llvm' /\
    fixed_input (Name "if.end57"%string) llvm' (Z.of_nat (S (nat_of_ord index))) /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S (nat_of_ord index)) =? Z.of_nat count then 185 else 149))) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (S (nat_of_ord index)))) /\
    (forall id, ~ In id fixed_modified ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    Fixed.fixed_frame bp bu c c'.
Proof.
  intros Related Inv Locals Input Code Present Arguments Stack PC Counter.
  assert (K : (nat_of_ord index < count)%nat)
    by exact (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord index)).
  destruct (@fixed_store_step (cell_layout layout) count source desired bd bt bp bu
    Bound DP DU TP TU PU CD CT CP CU SourceUInt TargetUInt index original c (fst llvm)
    (proj1 Related) Inv) as (c' & Stores & InvFinal & FrameFinal).
  destruct Inv as [AD AT AP AU].
  pose proof (proj1 (AD _ _ (words_nth_error source index))) as LoadData.
  pose proof (proj1 (AT _ _ (words_nth_error desired index))) as LoadTarget.
  destruct Locals as [N Count Data Target Perm Used].
  destruct (@normalize_llvm_iteration (cell_layout layout) bd bt bp bu count
    (nat_of_ord index) from varargs c c' llvm
    (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index)))
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 Related)
    LoadData LoadTarget Input Data Target Perm Used Count Stores)
    as (llvm' & LLVMFinal & LLVMSteps & InputFinal & Other).
  destruct (@normalize_machine_iteration nondet layout frame initial machine count (nat_of_ord index)
    bd bp bt bu trace output (Int.repr (Z.of_nat (source index)))
    (Int.repr (Z.of_nat (desired index))) c c'
    ltac:(lia) CD CP CT CU Code Present Arguments Stack PC Counter
    (proj2 Related) LoadData LoadTarget Stores)
    as (machine' & MachineSteps & MachineFinal & CodeFinal & PresentFinal &
      ArgumentsFinal & StackFinal & PCFinal & CounterFinal).
  rewrite -> natural_word_equal in MachineSteps by auto.
  exists c', llvm', machine'. split; [split; assumption|]. split; [exact InvFinal|].
  split; [exact LLVMSteps|]. split; [exact MachineSteps|]. split.
  - constructor; rewrite -> Other by (unfold fixed_modified; simpl; intuition discriminate); assumption.
  - split; [exact InputFinal|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
    split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
    split; [exact PCFinal|]. split; [exact CounterFinal|]. split; assumption.
Qed.

Theorem fixed_loop_agrees varargs original : forall remaining start from c llvm machine,
  (0 < remaining)%nat -> (start + remaining = count)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  invariant original start c -> fixed_registers (cell_layout layout) count bd bt bp bu llvm ->
  fixed_input from llvm (Z.of_nat start) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 149)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat start)) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    invariant original count c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43"%string) llvm
      (Name "if.end57"%string) (Name "if.end65.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    (9 * remaining <= steps <= 11 * remaining)%nat /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 185)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat count)) /\
    (forall id, ~ In id fixed_modified ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    Fixed.fixed_frame bp bu c c'.
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from c llvm machine Positive Sum Related Inv Locals Input
      Code Present Arguments Stack PC Counter; [lia|].
  assert (K : (start < count)%nat) by lia.
  pose (index := (fintype.Ordinal (ssrbool.introT ssrnat.ltP K) : fintype.ordinal count)).
  destruct (fixed_iteration_agrees from varargs c llvm machine index original Related Inv
    Locals Input Code Present Arguments Stack PC Counter)
    as (c1 & llvm1 & machine1 & Related1 & Inv1 & LLVMStep & MachineStep & Locals1 & Input1 &
      Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1 & Other1 & Frame1).
  change (nat_of_ord index) with start in Inv1, LLVMStep, Input1, PC1, Counter1.
  pose (iteration_steps := if Nat.eqb (source index) (desired index) then 11%nat else 9%nat).
  assert (IterationBound : (9 <= iteration_steps <= 11)%nat).
  { unfold iteration_steps. destruct (Nat.eqb (source index) (desired index)); lia. }
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat (S start) =? Z.of_nat count) = true)
      by (apply Z.eqb_eq; lia).
    rewrite -> Last in LLVMStep, PC1.
    exists c1, llvm1, machine1, iteration_steps. split; [exact Related1|].
    split; [replace count with (S start) by lia; exact Inv1|].
    split; [exact LLVMStep|]. split; [exact MachineStep|]. split; [lia|].
    split; [exact Code1|]. split; [exact Present1|].
    split; [exact Arguments1|]. split; [exact Stack1|]. split; [exact PC1|]. split.
    + replace count with (S start) by lia. exact Counter1.
    + split; assumption.
  - assert (More : (Z.of_nat (S start) =? Z.of_nat count) = false)
      by (apply Z.eqb_neq; lia).
    rewrite -> More in LLVMStep, PC1.
    destruct (IH (S start) (Name "if.end57"%string) c1 llvm1 machine1 ltac:(lia) ltac:(lia)
      Related1 Inv1 Locals1 Input1 Code1 Present1 Arguments1 Stack1 PC1 Counter1)
      as (c' & llvm' & machine' & rest & RelatedFinal & InvFinal & LLVMSteps & MachineSteps &
        StepsBound & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal &
        CounterFinal & OtherFinal & FrameFinal).
    exists c', llvm', machine', (iteration_steps + rest)%nat.
    split; [exact RelatedFinal|]. split; [exact InvFinal|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * eapply instruction_steps_append; eassumption.
      * split; [lia|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
        split; [exact PCFinal|]. split; [exact CounterFinal|]. split.
        -- intros id Outside. rewrite -> OtherFinal by exact Outside. apply Other1, Outside.
        -- intros other values NotPerm NotUsed A. apply FrameFinal; try assumption.
           apply Frame1; assumption.
Qed.
Theorem fixed_pass_agrees from varargs c llvm machine original :
  (0 < count)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  array_at c bd (words source) -> array_at c bt (words desired) -> array_at c bp (words original) ->
  Maps.lookup (Name "v1"%string) (locals llvm) = Some (word_value (Int.repr (Z.of_nat count))) ->
  Maps.lookup (Name "v2"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)) ->
  Maps.lookup (Name "v4"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bt) (block_provenance (cell_layout layout) bt)) ->
  Maps.lookup (Name "v3"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bp) (block_provenance (cell_layout layout) bp)) ->
  Maps.lookup (Name "v5"%string) (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bu) (block_provenance (cell_layout layout) bu)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 147)) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @Fixed.fixed_arrays count source desired bd bt bp bu
      (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)
      (words (fixed_flags source desired)) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43.preheader"%string) llvm
      (Name "if.end57"%string) (Name "if.end65.preheader"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    (1 + 9 * count <= steps <= 1 + 11 * count)%nat /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 185)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat count)) /\
    (forall id, fixed_unmodified id ->
      Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    Fixed.fixed_frame bp bu c c'.
Proof.
  intros Positive Related AD AT AP N Data Target Perm Used Code Present Arguments Stack PC.
  assert (Inv : invariant original 0 c).
  { constructor; try assumption. intros k v H. destruct k; discriminate. }
  pose (llvm1 := set_local llvm (Name "wide.trip.count304"%string) (index_value (Z.of_nat count))).
  assert (Locals1 : fixed_registers (cell_layout layout) count bd bt bp bu llvm1).
  { constructor; unfold llvm1;
      first [apply lookup_local_same | rewrite -> lookup_local_other by discriminate; assumption]. }
  destruct (@normalize_preheader nondet layout frame initial machine count bd bp bt bu trace output
    Code Present Arguments Stack PC)
    as (machine1 & MachineEntry & Memory1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1).
  assert (Related1 : llvm_machine_related layout c (fst llvm1) (archState.memory (sst machine1))).
  { destruct Related as [LLVM Machine]. split.
    - unfold llvm1. rewrite -> memory_set_local. exact LLVM.
    - rewrite -> Memory1. exact Machine. }
  destruct (@fixed_loop_agrees varargs original count 0 (Name "if.end43.preheader"%string)
    c llvm1 machine1 Positive Logic.eq_refl Related1 Inv Locals1
    (or_introl (conj Logic.eq_refl Logic.eq_refl)) Code1 Present1 Arguments1 Stack1 PC1 Counter1)
    as (c' & llvm' & machine' & steps & RelatedFinal & InvFinal & LLVMLoop & MachineLoop &
      StepsBound & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal &
      CounterFinal & Other & FrameFinal).
  exists c', llvm', machine', (1 + steps)%nat. split; [exact RelatedFinal|]. split.
  - destruct InvFinal as [D T P U]. constructor; try assumption.
    + assert (Same : words (fixed_assignment source desired original count) =
        words (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)).
      { apply words_ext. intro x. unfold fixed_assignment.
        assert (Within : Nat.ltb (nat_of_ord x) count = true).
        { apply Nat.ltb_lt. exact (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord x)). }
        rewrite -> Within. reflexivity. }
      rewrite <- Same. exact P.
    + rewrite -> List.firstn_all2 in U by (rewrite -> words_length; lia). exact U.
  - split.
    + eapply steps_next; [exact (proj2_sig FullCFG.fixed_preheader)| |exact LLVMLoop].
      exact (@fixed_preheader_runs (cell_layout layout) count bd bt bp bu
        Bound DP DU TP TU PU CD CT CP CU from varargs llvm N).
    + split.
      * eapply instruction_steps_append; [exact MachineEntry|exact MachineLoop].
      * split; [lia|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|].
        split; [exact PCFinal|]. split; [exact CounterFinal|]. split; [|exact FrameFinal].
        intros id [Different Outside]. rewrite -> Other by exact Outside. unfold llvm1.
        rewrite -> lookup_local_other by exact Different. reflexivity.
Qed.
End FixedAgreement.

Print Assumptions fixed_iteration_agrees.
Print Assumptions fixed_loop_agrees.
Print Assumptions fixed_pass_agrees.
