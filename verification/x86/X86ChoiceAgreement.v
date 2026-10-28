(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix MainInvariant Choose.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86ModelTypes X86Search X86ChoiceModel.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition main_choice_selection {d} (p : model_permutation (S d)) : option nat :=
  option_map (@fintype.nat_of_ord (S d)) (Legacy.Permute.choose p (@fintype.ord_max d)).

Section ChoiceAgreement.
Context (nondet : bool) (layout : finite_layout)
    (frame : call_frame layout program_bytes) (initial : seq_state)
    (d : nat) (bd bp bt bu trace output : Values.block).
Hypothesis Size : (S d <= 1024)%nat.
Hypothesis CP : (S d <= block_words (cell_layout layout) bp)%nat.

Theorem main_choose_agrees source (p : model_permutation (S d)) depths c llvm machine from varargs :
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout (S d) bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 275)) ->
  read_reg_seq_state r12 machine = Some (machine_address (Z.of_nat d)) ->
  read_reg_seq_state r15 machine = Some (machine_address (2 * Z.of_nat (S d))) ->
  exists previous llvm' machine' count,
    llvm_machine_related layout c (fst llvm') (archState.memory (sst machine')) /\
    main_registers (cell_layout layout) d bd bp trace output llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "while.cond106"%string) llvm previous
      (choose_target (main_choice_selection p)) llvm' /\
    choose_binding previous llvm' (main_choice_selection p) /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address
      (entry_pc frame + choice_machine_target (main_choice_selection p))) /\
    choice_machine_binding machine' (main_choice_selection p) /\
    read_reg_seq_state r12 machine' = Some (machine_address (Z.of_nat d)) /\
    read_reg_seq_state r15 machine' = Some (machine_address (2 * Z.of_nat (S d))) /\
    search_frame machine machine'.
Proof.
  intros Related Arrays Registers Code Present Arguments Stack PC Top Capacity.
  destruct (@main_choose (cell_layout layout) d bd bp trace output source p depths c llvm from varargs
    Size CP (proj1 Related) Arrays Registers)
    as [previous [llvm' [RelatedLLVM [RegistersFinal [LLVM Binding]]]]].
  destruct (choose_machine_permutation nondet layout frame d p bp c machine Size CP
    (proj2 Related) (ClightMain.loop_destinations Arrays) Code Present PC
    (core_permutation _ _ _ _ _ _ _ _ _ Arguments) Top)
    as [count [machine' [Machine [Frame [FinalCode [FinalPresent [FinalPC FinalBinding]]]]]]].
  exists previous, llvm', machine', count. split.
  - split; [exact RelatedLLVM|]. rewrite (proj1 Frame). exact (proj2 Related).
  - split; [exact RegistersFinal|]. split; [exact LLVM|]. split; [exact Binding|].
    split; [exact Machine|]. split; [exact FinalCode|]. split; [exact FinalPresent|]. split.
    + eapply search_frame_arguments; [exact Frame|exact Arguments].
    + split.
      * eapply search_frame_stack; [exact Frame|exact Stack].
      * split; [exact FinalPC|]. split; [exact FinalBinding|]. split.
        -- rewrite (proj2 Frame r12) by (unfold search_clobbered; cbn; intuition discriminate). exact Top.
        -- split; [|exact Frame].
           rewrite (proj2 Frame r15) by (unfold search_clobbered; cbn; intuition discriminate). exact Capacity.
Qed.
End ChoiceAgreement.

Print Assumptions main_choose_agrees.
