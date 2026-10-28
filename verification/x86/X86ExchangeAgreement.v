(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
From Legacy Require Import Permute.
Require Import ClightMemory ClightScalar ClightMain ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks Fixed Choose ExchangeBlocks ExchangeSuccess MainPrefix MainInvariant.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86ModelTypes X86PermuteSwap X86Exchange
  X86LLVMExchangePermutation X86LLVMExchangeBlocked X86LLVMExchangeSuccess.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.
Local Notation nat_of_ord := fintype.nat_of_ord.

Lemma exchange_swap_frame first middle final :
  exchange_register_frame first middle ->
  (forall reg : Arch.reg, reg <> rip -> reg <> rax -> reg <> rbx ->
    read_reg_seq_state reg final = read_reg_seq_state reg middle) ->
  exchange_register_frame first final.
Proof.
  intros First Last reg Outside.
  rewrite Last by (unfold exchange_clobbered in Outside; cbn in Outside; intuition congruence).
  apply First, Outside.
Qed.

Section ExchangeAgreement.
Context (nondet : bool) (layout : finite_layout)
    (frame : call_frame layout program_bytes) (initial : seq_state)
    (d : nat) (bd bp bt bu trace output : Values.block).
Hypotheses (DP : bd <> bp) (DT : bd <> trace) (DO : bd <> output)
    (PT : bp <> trace) (PO : bp <> output) (TO : trace <> output).
Hypothesis Bound : (S d <= 1024)%nat.
Hypotheses (CD : (S d <= block_words (cell_layout layout) bd)%nat)
    (CP : (S d <= block_words (cell_layout layout) bp)%nat)
    (CT : (2 * S d <= block_words (cell_layout layout) trace)%nat)
    (CO : (3 <= block_words (cell_layout layout) output)%nat).
Local Notation model_top := (@fintype.ord_max d).
Local Notation arrays := (@ClightMain.loop_arrays d bd bp trace output).
Local Notation registers := (main_registers (cell_layout layout) d bd bp trace output).

Theorem equal_exchange_agrees (source : fintype.ordinal (S d) -> nat)
    (p : model_permutation (S d)) depths (position : fintype.ordinal (S d)) c llvm machine from varargs :
  (nat_of_ord position < d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays c source p depths -> registers llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  source model_top = source position ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout (S d) bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r12 machine = Some (machine_address (Z.of_nat d)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  read_reg_seq_state r15 machine = Some (machine_address (2 * Z.of_nat (S d))) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays c' source (Legacy.Permute.exchange p model_top position) depths /\
    registers llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") llvm
      (Name "if.end169") (Name "while.cond106") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 10 machine machine' /\
    @ClightMain.main_frame bd bp trace output c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 275)) /\
    read_reg_seq_state r12 machine' = Some (machine_address (Z.of_nat d)) /\
    read_reg_seq_state r15 machine' = Some (machine_address (2 * Z.of_nat (S d))).
Proof.
  intros Position Related Arrays Registers Binding Equal Code Present Arguments Stack PC Top Selected Capacity.
  destruct (@llvm_exchange_equal_choice_stores (cell_layout layout) d bd bp trace output source p depths
    position c llvm from varargs Bound CD CP DP (not_eq_sym PT) (not_eq_sym PO)
    (proj1 Related) Arrays Registers Binding Equal)
    as (middle & c' & llvm' & DataSelected & DataTop & PermSelected & PermTop &
      StoreSelected & StoreTop & LLVMFinal & ArraysFinal & RegistersFinal & LLVMSteps & Frame).
  assert (Same : word_equal (Int.repr (Z.of_nat (source position)))
    (Int.repr (Z.of_nat (source model_top))) = true).
  { unfold word_equal. rewrite Equal, Z.eqb_refl. reflexivity. }
  destruct (exchange_equal nondet layout frame initial machine bd (nat_of_ord position) d
    (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source model_top))) c
    ltac:(lia) ltac:(lia) Code Present Stack PC (core_data _ _ _ _ _ _ _ _ _ Arguments)
    Selected Top (proj2 Related) DataSelected DataTop Same)
    as (m1 & Compare & Related1 & Memory1 & Code1 & Present1 & Stack1 & PC1 & Frame1).
  assert (Perm1 : read_reg_seq_state rdx m1 = Some (pointer_to_block layout bp)).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate).
    exact (core_permutation _ _ _ _ _ _ _ _ _ Arguments). }
  assert (Top1 : read_reg_seq_state r12 m1 = Some (machine_address (Z.of_nat d))).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate). exact Top. }
  assert (Selected1 : read_reg_seq_state r13 m1 = Some (machine_address (Z.of_nat (nat_of_ord position)))).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate). exact Selected. }
  destruct (permute_swap_block nondet layout frame initial m1 bp (nat_of_ord position) d
    (Int.repr (Z.of_nat (model_destination p position))) (Int.repr (Z.of_nat (model_destination p model_top)))
    c middle c' ltac:(lia) ltac:(lia) Code1 Present1 Stack1 PC1 Perm1 Selected1 Top1
    Related1 PermSelected PermTop StoreSelected StoreTop)
    as (m2 & Swap & MachineFinal & CodeFinal & PresentFinal & StackFinal & PCFinal & AX & BX & Frame2).
  assert (FinalFrame : exchange_register_frame machine m2).
  { eapply exchange_swap_frame; eassumption. }
  exists c', llvm', m2. split; [split; assumption|]. split; [exact ArraysFinal|].
  split; [exact RegistersFinal|]. split; [exact LLVMSteps|]. split.
  - eapply instruction_steps_append with (count := 5%nat) (rest := 5%nat); eassumption.
  - split; [intros other values ND NP NT NO A; apply Frame; assumption|].
    split; [exact CodeFinal|]. split; [exact PresentFinal|]. split.
    + eapply exchange_frame_arguments; eassumption.
    + split; [exact StackFinal|]. split; [exact PCFinal|]. split;
        rewrite FinalFrame by (unfold exchange_clobbered; cbn; intuition discriminate); assumption.
Qed.

Theorem blocked_exchange_agrees (source : fintype.ordinal (S d) -> nat)
    (p : model_permutation (S d)) depths (position : fintype.ordinal (S d)) c llvm machine from varargs :
  (forall i, ClightScalar.uint (Z.of_nat (source i))) ->
  source model_top <> source position ->
  (nat_of_ord position + 16 < d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays c source p depths -> registers llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout (S d) bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r12 machine = Some (machine_address (Z.of_nat d)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  read_reg_seq_state r15 machine = Some (machine_address (2 * Z.of_nat (S d))) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @result_arrays d bd bp trace output
      (SolcBlocked source p depths position (Legacy.Permute.depth position - 16)%nat) c'
      (Out_return (Some (Vint (Int.repr 1), Permute.u32))) /\
    registers llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") llvm
      (Name "if.then142") (Name "cleanup") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 13 machine machine' /\
    @ClightMain.main_frame bd bp trace output c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax machine' = Some (machine_address 1) /\
    read_reg_seq_state r12 machine' = Some (machine_address (Z.of_nat d)) /\
    read_reg_seq_state r15 machine' = Some (machine_address (2 * Z.of_nat (S d))).
Proof.
  intros Values Different Far Related Arrays Registers Binding Code Present Arguments Stack PC Top Selected Capacity.
  destruct Arrays as [DataArray PermArray TraceArray OutputArray Writable].
  assert (Unequal : Z.of_nat (source position) <> Z.of_nat (source model_top)).
  { intro Same. apply Nat2Z.inj in Same. apply Different. symmetry; exact Same. }
  destruct (@llvm_exchange_blocked_choice_stores (cell_layout layout) bd output (words source)
    (nat_of_ord position) d (Z.of_nat (List.length depths)) 0 0
    (Z.of_nat (source position)) (Z.of_nat (source model_top)) from varargs c llvm
    ltac:(rewrite words_length; exact Bound) ltac:(rewrite words_length; exact CD) CO
    (words_nth_error source position) (words_nth_error source model_top)
    (Values position) (Values model_top) Unequal Far (proj1 Related) DataArray OutputArray Binding
    (main_data _ _ _ _ _ _ _ Registers) (main_data_top _ _ _ _ _ _ _ Registers)
    (main_top _ _ _ _ _ _ _ Registers) (main_output_fields _ _ _ _ _ _ _ Registers))
    as (middle & c' & llvm' & DataSelected & DataTop & StorePosition & StoreExcess & LLVMFinal &
      OutputFinal & LLVMSteps & Frame & Other).
  assert (WordDifferent : word_equal (Int.repr (Z.of_nat (source position)))
    (Int.repr (Z.of_nat (source model_top))) = false).
  { rewrite natural_word_equal by auto. apply Nat.eqb_neq. congruence. }
  destruct (exchange_exhausted nondet layout frame initial machine bd output (nat_of_ord position) d
    (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source model_top))) c middle c'
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CO Code Present Stack PC
    (core_data _ _ _ _ _ _ _ _ _ Arguments) (core_output _ _ _ _ _ _ _ _ _ Arguments)
    Selected Top (proj2 Related) DataSelected DataTop WordDifferent StorePosition StoreExcess)
    as (machine' & MachineSteps & MachineFinal & CodeFinal & PresentFinal & StackFinal & PCFinal & Return & FinalFrame).
  exists c', llvm', machine'. split; [split; assumption|]. split.
  - cbn [result_arrays]. split; [reflexivity|]. split; [apply Frame; assumption|].
    split; [apply Frame; assumption|]. split; [apply Frame; assumption|].
    assert (Excess : Z.of_nat (Legacy.Permute.depth position - 16)%nat =
      Z.of_nat d - Z.of_nat (nat_of_ord position) - 16).
    { change (Z.of_nat ((d - nat_of_ord position) - 16)%nat =
        Z.of_nat d - Z.of_nat (nat_of_ord position) - 16).
      rewrite !Nat2Z.inj_sub by lia. reflexivity. }
    rewrite Excess. exact OutputFinal.
  - split.
    + eapply exchange_main_registers; eassumption.
    + split; [exact LLVMSteps|]. split; [exact MachineSteps|].
      split; [intros other values ND NP NT NO A; apply Frame; assumption|].
      split; [exact CodeFinal|]. split; [exact PresentFinal|]. split.
      * eapply exchange_frame_arguments; eassumption.
      * split; [exact StackFinal|]. split; [exact PCFinal|]. split; [exact Return|]. split;
          rewrite FinalFrame by (unfold exchange_clobbered; cbn; intuition discriminate); assumption.
Qed.

Theorem successful_exchange_agrees (source : fintype.ordinal (S d) -> nat)
    (p : model_permutation (S d)) depths (position : fintype.ordinal (S d)) c llvm machine from varargs :
  (forall i, ClightScalar.uint (Z.of_nat (source i))) ->
  (nat_of_ord position < d)%nat ->
  source model_top <> source position ->
  (d <= nat_of_ord position + 16)%nat ->
  (List.length depths < 2 * S d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  arrays c source p depths -> registers llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  core_arguments layout (S d) bd bp bt bu trace output machine ->
  call_stack layout frame initial machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r12 machine = Some (machine_address (Z.of_nat d)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  read_reg_seq_state r15 machine = Some (machine_address (2 * Z.of_nat (S d))) ->
  exists c' llvm' machine',
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    arrays c' (Legacy.Permute.swap_stack source position)
      (Legacy.Permute.exchange p model_top position) (depths ++ [Legacy.Permute.depth position]) /\
    registers llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") llvm
      (Name "if.end169") (Name "while.cond106") llvm' /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 22 machine machine' /\
    @ClightMain.main_frame bd bp trace output c c' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    core_arguments layout (S d) bd bp bt bu trace output machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 275)) /\
    read_reg_seq_state r12 machine' = Some (machine_address (Z.of_nat d)) /\
    read_reg_seq_state r15 machine' = Some (machine_address (2 * Z.of_nat (S d))).
Proof.
  intros Values Position Different Near Space Related Arrays Registers Binding Code Present Arguments Stack PC Top Selected Capacity.
  destruct (@llvm_successful_exchange_stores (cell_layout layout) d bd bp trace output
    DP DT DO PT PO TO Bound CD CP CT CO source p position depths c llvm from varargs
    Values Position (not_eq_sym Different) Near Space (proj1 Related) Arrays Registers Binding)
    as (c1 & c2 & c3 & c4 & c5 & c' & llvm' & DataSelected & DataTop & CountLoad &
      StoreSelected & StoreTop & StoreTrace & StoreCount & PermSelected & PermTop &
      PermStoreSelected & PermStoreTop & LLVMFinal & ArraysFinal & RegistersFinal & LLVMSteps & Other & Frame).
  assert (WordDifferent : word_equal (Int.repr (Z.of_nat (source position)))
    (Int.repr (Z.of_nat (source model_top))) = false).
  { rewrite natural_word_equal by auto. apply Nat.eqb_neq. congruence. }
  assert (CapacityNat : read_reg_seq_state r15 machine =
    Some (machine_address (Z.of_nat (2 * S d)))).
  { rewrite Nat2Z.inj_mul. exact Capacity. }
  destruct (exchange_success nondet layout frame initial machine bd trace output
    (nat_of_ord position) d (List.length depths) (2 * S d)%nat
    (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source model_top))) c c1 c2 c3 c4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Code Present Stack PC (core_data _ _ _ _ _ _ _ _ _ Arguments)
    (core_trace _ _ _ _ _ _ _ _ _ Arguments) (core_output _ _ _ _ _ _ _ _ _ Arguments)
    Selected Top CapacityNat (proj2 Related) DataSelected DataTop WordDifferent
    CountLoad StoreSelected StoreTop StoreTrace StoreCount)
    as (m1 & Exchange & Related1 & Code1 & Present1 & Stack1 & PC1 & Frame1).
  assert (Perm1 : read_reg_seq_state rdx m1 = Some (pointer_to_block layout bp)).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate).
    exact (core_permutation _ _ _ _ _ _ _ _ _ Arguments). }
  assert (Top1 : read_reg_seq_state r12 m1 = Some (machine_address (Z.of_nat d))).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate). exact Top. }
  assert (Selected1 : read_reg_seq_state r13 m1 = Some (machine_address (Z.of_nat (nat_of_ord position)))).
  { rewrite Frame1 by (unfold exchange_clobbered; cbn; intuition discriminate). exact Selected. }
  destruct (permute_swap_block nondet layout frame initial m1 bp (nat_of_ord position) d
    (Int.repr (Z.of_nat (model_destination p position))) (Int.repr (Z.of_nat (model_destination p model_top)))
    c4 c5 c' ltac:(lia) ltac:(lia) Code1 Present1 Stack1 PC1 Perm1 Selected1 Top1
    Related1 PermSelected PermTop PermStoreSelected PermStoreTop)
    as (m2 & Swap & MachineFinal & CodeFinal & PresentFinal & StackFinal & PCFinal & AX & BX & Frame2).
  assert (FinalFrame : exchange_register_frame machine m2).
  { eapply exchange_swap_frame; eassumption. }
  exists c', llvm', m2. split; [split; assumption|]. split; [exact ArraysFinal|].
  split; [exact RegistersFinal|]. split; [exact LLVMSteps|]. split.
  - eapply instruction_steps_append with (count := 17%nat) (rest := 5%nat); eassumption.
  - split; [exact Frame|]. split; [exact CodeFinal|]. split; [exact PresentFinal|]. split.
    + eapply exchange_frame_arguments; eassumption.
    + split; [exact StackFinal|]. split; [exact PCFinal|]. split;
        rewrite FinalFrame by (unfold exchange_clobbered; cbn; intuition discriminate); assumption.
Qed.
End ExchangeAgreement.

Print Assumptions equal_exchange_agrees.
Print Assumptions blocked_exchange_agrees.
Print Assumptions successful_exchange_agrees.
