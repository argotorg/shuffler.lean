(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ClightFillLoop
  ClightNormalization ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index
  FixedBlocks Fixed SearchBlocks Search SearchModel FillBlocks Fill FillLoop.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From mathcomp Require Import ssrbool eqtype fintype finset.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Compare X86Call X86Arguments X86CellAddress X86Fill
  X86LLVMFill X86Search X86SearchModel.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.
Local Notation nat_of_ord := fintype.nat_of_ord.
Local Notation "'ordinals' n" := (fintype.enum (fintype.ordinal n)) (at level 10).

Section FillAgreement.
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
Hypotheses (SourceUInt : forall x, ClightScalar.uint (Z.of_nat (source x)))
    (TargetUInt : forall x, ClightScalar.uint (Z.of_nat (desired x))).
Local Notation arrays := (fill_arrays count source desired bd bt bp bu).
Local Notation registers := (fill_registers (cell_layout layout) count bd bt bp bu).

Theorem fill_branch_agrees from varargs c llvm machine (index : fintype.ordinal count)
    tail assignment reserved final :
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays assignment reserved c -> registers llvm ->
  fill_input from llvm (Z.of_nat (nat_of_ord index)) ->
  raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired (index :: tail) assignment reserved = Some final ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 187)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat (nat_of_ord index))) ->
  exists assignment' reserved' c' llvm' previous machine' steps,
    raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired tail assignment' reserved' = Some final /\
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays assignment' reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") llvm
      previous (Name "if.end103") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    Maps.lookup (Name "indvars.iv311") (locals llvm') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    registers llvm' /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    fill_frame bp bu c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 255)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (nat_of_ord index))).
Proof.
  intros Related Arrays Registers Input Model Code Present Arguments Stack PC Counter.
  destruct Arrays as [AD AT AP AU].
  destruct Registers as [N Count SearchCount Data Target Perm Used].
  assert (K : (nat_of_ord index < count)%nat)
    by exact (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord index)).
  pose (s1 := fill_compare_state llvm (Z.of_nat (nat_of_ord index))
    (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)
    (block_address (cell_layout layout) bt) (block_provenance (cell_layout layout) bt)
    (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index)))).
  assert (Comparison : runs (denote_block (proj1_sig FillBlocks.fill_compare) from varargs) llvm s1
    (inl (if Nat.eqb (source index) (desired index) then Name "if.end103" else Name "if.end77"))).
  { rewrite <- natural_word_equal by auto.
    apply fill_compare_runs; try assumption; try lia.
    - eapply related_load; [exact (proj1 Related)|lia|].
      exact (proj1 (AD _ _ (words_nth_error source index))).
    - eapply related_load; [exact (proj1 Related)|lia|].
      exact (proj1 (AT _ _ (words_nth_error desired index))). }
  assert (Memory1 : fst s1 = fst llvm) by apply fill_compare_memory.
  assert (Related1 : cells_related (cell_layout layout) c (fst s1)).
  { rewrite Memory1. exact (proj1 Related). }
  assert (Other1 : forall id, ~ In id fill_modified ->
    Maps.lookup id (locals s1) = Maps.lookup id (locals llvm)).
  { intros id Outside. apply fill_compare_other, Outside. }
  assert (Index1 : Maps.lookup (Name "indvars.iv311") (locals s1) =
    Some (index_value (Z.of_nat (nat_of_ord index)))) by apply fill_compare_index.
  assert (Registers1 : registers s1).
  { constructor; rewrite Other1 by (unfold fill_modified; simpl; intuition discriminate); assumption. }
  destruct (fill_machine_probe nondet layout frame initial machine count (nat_of_ord index)
    bd bp bt bu trace output (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index))) c
    ltac:(lia) CD CT Code Present Arguments Stack PC Counter (proj2 Related)
    (proj1 (AD _ _ (words_nth_error source index))) (proj1 (AT _ _ (words_nth_error desired index))))
    as (m1 & Probe & MemoryM1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1 & Value1).
  rewrite natural_word_equal in Probe, PC1 by auto.
  assert (RelatedM1 : machine_cells_related layout c (archState.memory (sst m1))).
  { rewrite MemoryM1. exact (proj2 Related). }
  rewrite raw_fill_step_nat in Model.
  destruct (Nat.eqb (source index) (desired index)) eqn:Equal.
  - exists assignment, reserved, c, s1, (Name "if.end65"), m1, 5%nat.
    split; [exact Model|]. split; [split; assumption|]. split; [constructor; assumption|].
    split.
    + eapply steps_next; [exact (proj2_sig FillBlocks.fill_compare)|exact Comparison|constructor].
    + split; [exact Probe|]. split; [exact Index1|]. split; [exact Registers1|]. split.
      * intros id [Outside _]. apply Other1, Outside.
      * split; [intros other values NotPerm NotUsed A; exact A|].
        split; [exact Code1|]. split; [exact Present1|]. split; [exact Arguments1|].
        split; [exact Stack1|]. split; assumption.
  - destruct (first_free (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) desired (source index) reserved (ordinals count)) as [chosen|] eqn:Choice;
      [|discriminate].
    assert (SearchRegisters : search_registers (cell_layout layout) count (source index) bt bu s1).
    { constructor.
      - exact (fill_size_local _ _ _ _ _ _ _ Registers1).
      - exact (fill_search_count_local _ _ _ _ _ _ _ Registers1).
      - exact (fill_target_local _ _ _ _ _ _ _ Registers1).
      - exact (fill_used_local _ _ _ _ _ _ _ Registers1).
      - apply fill_compare_value. }
    destruct (@first_free_search (cell_layout layout) count (source index) desired reserved bt bu varargs c s1 chosen
      Bound CT CU (SourceUInt index) TargetUInt Choice Related1 AT AU SearchRegisters)
      as (s2 & Memory2 & Search & Chosen & SearchRegisters2 & Other2).
    assert (Related2 : cells_related (cell_layout layout) c (fst s2)) by (rewrite Memory2; exact Related1).
    assert (Registers2 : registers s2).
    { destruct Registers1. constructor;
        rewrite Other2 by (unfold search_modified; simpl; intuition discriminate); assumption. }
    assert (Index2 : Maps.lookup (Name "indvars.iv311") (locals s2) =
      Some (index_value (Z.of_nat (nat_of_ord index)))).
    { rewrite Other2 by (unfold search_modified; simpl; intuition discriminate). exact Index1. }
    destruct (core_size _ _ _ _ _ _ _ _ _ Arguments1) as [size_old [SizeRead SizeLow]].
    assert (SizeLow32 : low_register32 7 size_old = Z_to_bv 32 (Z.of_nat count)).
    { change (bv_extract 0 32 size_old = Z_to_bv 32 (Z.of_nat count)).
      rewrite SizeLow. unfold machine_word. rewrite Int.unsigned_repr; [reflexivity|].
      change Int.max_unsigned with 4294967295. lia. }
    destruct (@first_free_machine_search nondet layout frame count (source index) desired reserved
      bt bu c m1 chosen (@zero_extend 32 (machine_word (Int.repr (Z.of_nat (source index)))) 64) size_old
      Bound CT CU (SourceUInt index) TargetUInt Choice AT AU RelatedM1 Code1 Present1 PC1 Value1
      ltac:(apply low32_zero_extend)
      (core_target _ _ _ _ _ _ _ _ _ Arguments1) (core_used _ _ _ _ _ _ _ _ _ Arguments1)
      SizeRead SizeLow32)
      as (search_steps & m2 & MachineSearch & SearchFrame & Code2 & Present2 & PC2 & Chosen2).
    assert (RelatedM2 : machine_cells_related layout c (archState.memory (sst m2))).
    { rewrite (proj1 SearchFrame). exact RelatedM1. }
    assert (Arguments2 : core_arguments layout count bd bp bt bu trace output m2).
    { eapply search_frame_arguments; eassumption. }
    assert (Stack2 : call_stack layout frame initial m2).
    { eapply search_frame_stack; eassumption. }
    assert (Counter2 : read_reg_seq_state rax m2 = Some (machine_address (Z.of_nat (nat_of_ord index)))).
    { rewrite (proj2 SearchFrame) by (unfold search_clobbered; cbn; intuition discriminate). exact Counter1. }
    destruct (@llvm_fill_assignment_stores (cell_layout layout) count source desired bd bt bp bu
      Bound DP DU TP TU PU CD CT CP CU (Name "while.end93") varargs c s2 index chosen assignment reserved
      Related2 ltac:(constructor; assumption) Registers2 Index2 Chosen)
      as (c1 & c3 & s3 & StorePerm & StoreUsed & Related3 & Arrays3 & Assign & Index3 & Registers3 & Other3 & Frame3).
    destruct (fill_machine_assign nondet layout frame initial m2 count (nat_of_ord index)
      (nat_of_ord chosen) bd bp bt bu trace output c c1 c3 ltac:(lia)
      (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord chosen)) CP CU Code2 Present2 Arguments2 Stack2
      PC2 Counter2 Chosen2 RelatedM2 StorePerm StoreUsed)
      as (m3 & MachineAssign & RelatedM3 & Code3 & Present3 & Arguments3 & Stack3 & PC3 & Counter3).
    exists (write_index assignment index chosen). eexists. exists c3, s3,
      (Name "if.end97"), m3, (4 + search_steps + 2)%nat.
    split; [exact Model|]. split; [split; assumption|]. split; [exact Arrays3|]. split.
    + eapply steps_next; [exact (proj2_sig FillBlocks.fill_compare)|exact Comparison|].
      eapply block_steps_append; [exact Search|].
      eapply steps_next; [exact (proj2_sig FillBlocks.fill_assign)|exact Assign|constructor].
    + split.
      * replace (4 + search_steps + 2)%nat with (4 + (search_steps + 2))%nat by lia.
        eapply instruction_steps_append; [exact Probe|].
        eapply instruction_steps_append; [exact MachineSearch|exact MachineAssign].
      * split; [exact Index3|]. split; [exact Registers3|]. split.
        -- intros id [OutsideFill OutsideSearch].
           rewrite Other3 by exact OutsideFill. rewrite Other2 by exact OutsideSearch. apply Other1, OutsideFill.
        -- split; [exact Frame3|]. split; [exact Code3|]. split; [exact Present3|].
           split; [exact Arguments3|]. split; [exact Stack3|]. split; assumption.
Qed.

Theorem fill_iteration_agrees from varargs c llvm machine (index : fintype.ordinal count)
    assignment reserved final :
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays assignment reserved c -> registers llvm ->
  fill_input from llvm (Z.of_nat (nat_of_ord index)) ->
  raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired (List.skipn (nat_of_ord index) (ordinals count)) assignment reserved = Some final ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 187)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat (nat_of_ord index))) ->
  exists assignment' reserved' c' llvm' machine' steps,
    raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired (List.skipn (S (nat_of_ord index)) (ordinals count)) assignment' reserved' = Some final /\
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays assignment' reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") llvm
      (Name "if.end103") (if Z.of_nat (S (nat_of_ord index)) =? Z.of_nat count
        then Name "while.end105" else Name "if.end65") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    registers llvm' /\ fill_input (Name "if.end103") llvm' (Z.of_nat (S (nat_of_ord index))) /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    fill_frame bp bu c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S (nat_of_ord index)) =? Z.of_nat count then 262 else 187))) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat (S (nat_of_ord index)))).
Proof.
  intros Related Arrays Registers Input Model Code Present Arguments Stack PC Counter.
  assert (EnumStep : List.skipn (nat_of_ord index) (ordinals count) =
    index :: List.skipn (S (nat_of_ord index)) (ordinals count)).
  { exact (ClightFillLoop.ordinal_enum_step index). }
  rewrite EnumStep in Model.
  destruct (fill_branch_agrees from varargs c llvm machine index
    (List.skipn (S (nat_of_ord index)) (ordinals count)) assignment reserved final
    Related Arrays Registers Input Model Code Present Arguments Stack PC Counter)
    as (assignment1 & reserved1 & c1 & s1 & previous & m1 & steps & Model1 & Related1 & Arrays1 & Branch &
      MachineBranch & Index1 & Registers1 & Other1 & Frame1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1).
  assert (K : (nat_of_ord index < count)%nat)
    by exact (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord index)).
  pose (s2 := fill_next_state s1 (Z.of_nat (nat_of_ord index)) (Z.of_nat count)).
  assert (Next : runs (denote_block (proj1_sig FillBlocks.fill_next) previous varargs) s1 s2
    (inl (if Z.of_nat (S (nat_of_ord index)) =? Z.of_nat count
      then Name "while.end105" else Name "if.end65"))).
  { replace (Z.of_nat (S (nat_of_ord index))) with (Z.of_nat (nat_of_ord index) + 1) by lia.
    apply fill_next_runs; try lia; [exact Index1|exact (fill_count_local _ _ _ _ _ _ _ Registers1)]. }
  destruct (fill_machine_next nondet layout frame initial m1 count (nat_of_ord index)
    bd bp bt bu trace output ltac:(lia) Code1 Present1 Arguments1 Stack1 PC1 Counter1)
    as (m2 & MachineNext & MemoryM2 & Code2 & Present2 & Arguments2 & Stack2 & PC2 & Counter2).
  exists assignment1, reserved1, c1, s2, m2, (steps + 3)%nat.
  split; [exact Model1|]. split.
  - split.
    + unfold s2. rewrite fill_next_memory. exact (proj1 Related1).
    + rewrite MemoryM2. exact (proj2 Related1).
  - split; [exact Arrays1|]. split.
    + eapply block_steps_append; [exact Branch|].
      eapply steps_next; [exact (proj2_sig FillBlocks.fill_next)|exact Next|constructor].
    + split.
      * eapply instruction_steps_append; [exact MachineBranch|exact MachineNext].
      * split.
        -- destruct Registers1. constructor; unfold s2; rewrite fill_next_other by
             (unfold fill_modified; simpl; intuition discriminate); assumption.
        -- split.
           ++ replace (Z.of_nat (S (nat_of_ord index))) with (Z.of_nat (nat_of_ord index) + 1) by lia.
              apply fill_next_input.
           ++ split.
              ** intros id Outside. unfold s2. rewrite fill_next_other by exact (proj1 Outside).
                 apply Other1, Outside.
              ** split; [exact Frame1|]. split; [exact Code2|]. split; [exact Present2|].
                 split; [exact Arguments2|]. split; [exact Stack2|]. split; assumption.
Qed.

Theorem fill_loop_agrees varargs final : forall remaining start from assignment reserved c llvm machine,
  (0 < remaining)%nat -> (start + remaining = count)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays assignment reserved c -> registers llvm -> fill_input from llvm (Z.of_nat start) ->
  raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired (List.skipn start (ordinals count)) assignment reserved = Some final ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 187)) ->
  read_reg_seq_state rax machine = Some (machine_address (Z.of_nat start)) ->
  exists reserved' c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays final reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65") llvm
      (Name "if.end103") (Name "while.end105") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    (forall id, fill_body_unmodified id -> Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    fill_frame bp bu c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 262)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat count)).
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from assignment reserved c llvm machine Positive Sum Related Arrays Registers Input Model
      Code Present Arguments Stack PC Counter; [lia|].
  assert (K : (start < count)%nat) by lia.
  pose (index := (fintype.Ordinal (ssrbool.introT ssrnat.ltP K) : fintype.ordinal count)).
  destruct (fill_iteration_agrees from varargs c llvm machine index assignment reserved final
    Related Arrays Registers Input Model Code Present Arguments Stack PC Counter)
    as (assignment1 & reserved1 & c1 & llvm1 & machine1 & steps & Model1 & Related1 & Arrays1 & LLVMStep &
      MachineStep & Registers1 & Input1 & Other1 & Frame1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1).
  change (nat_of_ord index) with start in Model1, LLVMStep, Input1, PC1, Counter1.
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat (S start) =? Z.of_nat count) = true) by (apply Z.eqb_eq; lia).
    rewrite Last in LLVMStep, PC1.
    replace (S start) with count in Model1 by lia.
    rewrite ordinal_enum_end in Model1. cbn [raw_fill] in Model1.
    injection Model1 as E. subst assignment1.
    exists reserved1, c1, llvm1, machine1, steps.
    split; [exact Related1|]. split; [exact Arrays1|]. split; [exact LLVMStep|].
    split; [exact MachineStep|]. split; [exact Other1|]. split; [exact Frame1|].
    split; [exact Code1|]. split; [exact Present1|]. split; [exact Arguments1|].
    split; [exact Stack1|]. split; [exact PC1|]. replace count with (S start) by lia. exact Counter1.
  - assert (More : (Z.of_nat (S start) =? Z.of_nat count) = false) by (apply Z.eqb_neq; lia).
    rewrite More in LLVMStep, PC1.
    destruct (IH (S start) (Name "if.end103") assignment1 reserved1 c1 llvm1 machine1
      ltac:(lia) ltac:(lia) Related1 Arrays1 Registers1 Input1 Model1 Code1 Present1 Arguments1 Stack1 PC1 Counter1)
      as (reserved' & c' & llvm' & machine' & rest & RelatedFinal & ArraysFinal & LLVMSteps & MachineSteps &
        OtherFinal & FrameFinal & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & CounterFinal).
    exists reserved', c', llvm', machine', (steps + rest)%nat.
    split; [exact RelatedFinal|]. split; [exact ArraysFinal|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * eapply instruction_steps_append; eassumption.
      * split.
        -- intros id Outside. rewrite OtherFinal by exact Outside. apply Other1, Outside.
        -- split.
           ++ intros other values NotPerm NotUsed A. apply FrameFinal; try assumption. apply Frame1; assumption.
           ++ split; [exact CodeFinal|]. split; [exact PresentFinal|]. split; [exact ArgumentsFinal|].
              split; [exact StackFinal|]. split; assumption.
Qed.

Theorem fill_pass_agrees from varargs c llvm machine assignment reserved final :
  (0 < count)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays assignment reserved c ->
  raw_fill (A := ssrnat.Datatypes_nat__canonical__eqtype_Equality) source desired (ordinals count) assignment reserved = Some final ->
  Maps.lookup (Name "v1") (locals llvm) = Some (word_value (Int.repr (Z.of_nat count))) ->
  Maps.lookup (Name "v2") (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bd) (block_provenance (cell_layout layout) bd)) ->
  Maps.lookup (Name "v4") (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bt) (block_provenance (cell_layout layout) bt)) ->
  Maps.lookup (Name "v3") (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bp) (block_provenance (cell_layout layout) bp)) ->
  Maps.lookup (Name "v5") (locals llvm) = Some
    (pointer_value (block_address (cell_layout layout) bu) (block_provenance (cell_layout layout) bu)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout count bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 185)) ->
  exists reserved' c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays final reserved' c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end65.preheader") llvm
      (Name "if.end103") (Name "while.end105") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    (forall id, fill_unmodified id -> Maps.lookup id (locals llvm') = Maps.lookup id (locals llvm)) /\
    fill_frame bp bu c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout count bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 262)) /\
    read_reg_seq_state rax machine' = Some (machine_address (Z.of_nat count)).
Proof.
  intros Positive Related Arrays Model N Data Target Perm Used Code Present Arguments Stack PC.
  pose (llvm1 := fill_preheader_state llvm (Z.of_nat count)).
  assert (Registers1 : registers llvm1).
  { constructor; unfold llvm1, fill_preheader_state;
      repeat first [apply lookup_local_same | rewrite lookup_local_other by discriminate]; assumption. }
  destruct (X86Fill.fill_preheader nondet layout frame initial machine count bd bp bt bu trace output
    Code Present Arguments Stack PC)
    as (machine1 & MachineEntry & Memory1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Counter1).
  assert (Related1 : llvm_machine_related layout c (fst llvm1) (archState.memory (sst machine1))).
  { split.
    - unfold llvm1, fill_preheader_state. rewrite !memory_set_local. exact (proj1 Related).
    - rewrite Memory1. exact (proj2 Related). }
  destruct (fill_loop_agrees varargs final count 0 (Name "if.end65.preheader") assignment reserved c llvm1 machine1
    Positive Logic.eq_refl Related1 Arrays Registers1 (or_introl (conj Logic.eq_refl Logic.eq_refl)) Model
    Code1 Present1 Arguments1 Stack1 PC1 Counter1)
    as (reserved' & c' & llvm' & machine' & steps & RelatedFinal & ArraysFinal & LLVMLoop & MachineLoop &
      Other & Frame & CodeFinal & PresentFinal & ArgumentsFinal & StackFinal & PCFinal & CounterFinal).
  exists reserved', c', llvm', machine', (1 + steps)%nat.
  split; [exact RelatedFinal|]. split; [exact ArraysFinal|]. split.
  - eapply steps_next; [exact (proj2_sig FillBlocks.fill_preheader)| |exact LLVMLoop].
    apply fill_preheader_runs; [lia|exact N].
  - split.
    + eapply instruction_steps_append; [exact MachineEntry|exact MachineLoop].
    + split.
      * intros id [Outside [Different1 Different2]]. rewrite Other by exact Outside.
        unfold llvm1, fill_preheader_state. rewrite !lookup_local_other by assumption. reflexivity.
      * split; [exact Frame|]. split; [exact CodeFinal|]. split; [exact PresentFinal|].
        split; [exact ArgumentsFinal|]. split; [exact StackFinal|]. split; assumption.
Qed.
End FillAgreement.

Print Assumptions fill_branch_agrees.
Print Assumptions fill_iteration_agrees.
Print Assumptions fill_loop_agrees.
Print Assumptions fill_pass_agrees.
