(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix MainInvariant Choose Cleanup.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Call X86Arguments X86ModelTypes X86LoopModel
  X86ChoiceModel X86ChoiceAgreement X86Done.
Import ListNotations.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.
Local Notation nat_of_ord := fintype.nat_of_ord.

Definition main_machine_state layout (frame : call_frame layout program_bytes) initial
    d bd bp bt bu trace output machine : Prop :=
  code_at machine (entry_pc frame) program_bytes /\ registers_present machine /\
  core_arguments layout (S d) bd bp bt bu trace output machine /\
  call_stack layout frame initial machine /\
  read_reg_seq_state r12 machine = Some (machine_address (Z.of_nat d)) /\
  read_reg_seq_state r15 machine = Some (machine_address (2 * Z.of_nat (S d))).

Section MainLoop.
Context (layout : finite_layout) (frame : call_frame layout program_bytes) (initial : seq_state)
    (d : nat) (bd bp bt bu trace output : Values.block).
Hypothesis Size : (S d <= 1024)%nat.
Hypothesis CP : (S d <= block_words (cell_layout layout) bp)%nat.
Local Notation MachineState := (main_machine_state layout frame initial d bd bp bt bu trace output).

(* The final main-loop theorem supplies these branch proofs. *)
Hypothesis EqualExchange : forall source (p : model_permutation (S d)) depths position
    c llvm machine from varargs,
  (nat_of_ord position < d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  source (model_top d) = source position ->
  MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @ClightMain.loop_arrays d bd bp trace output c' source (model_exchange p position) depths /\
    main_registers (cell_layout layout) d bd bp trace output llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133"%string) llvm
      (Name "if.end169"%string) (Name "while.cond106"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    MachineState machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 275)) /\
    @ClightMain.main_frame bd bp trace output c c'.

Hypothesis SuccessfulExchange : forall source (p : model_permutation (S d)) depths position
    c llvm machine from varargs,
  (nat_of_ord position < d)%nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  source (model_top d) <> source position ->
  (d <= nat_of_ord position + 16)%nat -> (List.length depths < 2 * S d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @ClightMain.loop_arrays d bd bp trace output c' (model_swap source position)
      (model_exchange p position) (depths ++ [model_depth position]) /\
    main_registers (cell_layout layout) d bd bp trace output llvm' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133"%string) llvm
      (Name "if.end169"%string) (Name "while.cond106"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    MachineState machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 275)) /\
    @ClightMain.main_frame bd bp trace output c c'.

Hypothesis BlockedExchange : forall source (p : model_permutation (S d)) depths position
    c llvm machine from varargs,
  (forall i, uint (Z.of_nat (source i))) -> source (model_top d) <> source position ->
  (nat_of_ord position + 16 < d)%nat ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm ->
  choose_binding from llvm (Some (nat_of_ord position)) ->
  MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 322)) ->
  read_reg_seq_state r13 machine = Some (machine_address (Z.of_nat (nat_of_ord position))) ->
  exists c' llvm' machine' steps,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    @result_arrays d bd bp trace output
      (SolcBlocked source p depths position (Nat.sub (model_depth position) 16)) c'
      (Out_return (Some (Vint (Int.repr 1), Permute.u32))) /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133"%string) llvm
      (Name "if.then142"%string) (Name "cleanup"%string) llvm' /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax machine' = Some (machine_address 1) /\
    @ClightMain.main_frame bd bp trace output c c'.

Theorem main_loop_from_exchange_agreements fuel source (p : model_permutation (S d))
    depths c llvm machine from varargs :
  (model_rank p < fuel)%nat -> (List.length depths + fuel <= 2 * S d)%nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  llvm_machine_related layout c (fst llvm) (archState.memory (sst machine)) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers (cell_layout layout) d bd bp trace output llvm -> MachineState machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 275)) ->
  exists c' llvm' machine' steps code,
    llvm_machine_related layout c' (fst llvm') (archState.memory (sst machine')) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output (model_run fuel source p depths) c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs from (Name "while.cond106"%string) llvm llvm'
      (word_value (Int.repr code)) /\
    instruction_steps (sail_tiny_x86_sem true)
      (return_condition (machine_address (return_pc frame))) steps machine machine' /\
    code_at machine' (entry_pc frame) program_bytes /\ registers_present machine' /\
    call_stack layout frame initial machine' /\
    read_reg_seq_state rip machine' = Some (machine_address (entry_pc frame + 428)) /\
    read_reg_seq_state rax machine' = Some (machine_address code) /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  revert source p depths c llvm machine from.
  induction fuel as [|fuel IH]; intros source p depths c llvm machine from
    Rank Capacity Values Related Arrays Registers State PC; [lia|].
  destruct State as (Code & Present & Arguments & Stack & Top & TraceCapacity).
  destruct (@main_choose_agrees true layout frame initial d bd bp bt bu trace output Size CP
    source p depths c llvm machine from varargs Related Arrays Registers Code Present Arguments Stack PC Top TraceCapacity)
    as (previous & llvm1 & machine1 & count1 & Related1 & Registers1 & Choose & Binding &
      Machine1 & Code1 & Present1 & Arguments1 & Stack1 & PC1 & Selected1 & Top1 & TraceCapacity1 & Frame1).
  assert (State1 : MachineState machine1).
  { exact (conj Code1 (conj Present1 (conj Arguments1 (conj Stack1 (conj Top1 TraceCapacity1))))). }
  unfold main_choice_selection in Choose, Binding, PC1, Selected1.
  change (Legacy.Permute.choose p (@fintype.ord_max d)) with (model_choice p)
    in Choose, Binding, PC1, Selected1.
  destruct (model_choice p) as [position|] eqn:Choice.
  - cbn [option_map choose_target choice_machine_target choice_machine_binding] in Choose, Binding, PC1, Selected1.
    destruct (@model_chosen_bounds d p position fuel Choice Rank) as (Position & NextRank).
    destruct (Nat.eq_dec (source (model_top d)) (source position)) as [Equal|Different].
    + destruct (EqualExchange source p depths position c llvm1 machine1 previous varargs
        Position Related1 Arrays Registers1 Binding Equal State1 PC1 Selected1)
        as (c2 & llvm2 & machine2 & count2 & Related2 & Arrays2 & Registers2 & Exchange &
          Machine2 & State2 & PC2 & Frame2).
      destruct (IH source (model_exchange p position) depths c2 llvm2 machine2 (Name "if.end169"%string)
        NextRank ltac:(lia) Values Related2 Arrays2 Registers2 State2 PC2)
        as (c' & llvm' & machine' & count3 & code & RelatedFinal & ResultCode & Result & LLVMRest &
          MachineRest & CodeFinal & PresentFinal & StackFinal & PCFinal & Return & FrameFinal).
      exists c', llvm', machine', (count1 + (count2 + count3))%nat, code.
      split; [exact RelatedFinal|]. split; [exact ResultCode|]. split.
      * rewrite (@model_run_equal d fuel source p depths position Choice Equal). exact Result.
      * split.
        -- eapply block_steps_return; [exact Choose|]. eapply block_steps_return; eassumption.
        -- split.
           ++ eapply instruction_steps_append; [exact Machine1|].
              eapply instruction_steps_append; eassumption.
           ++ split; [exact CodeFinal|]. split; [exact PresentFinal|]. split; [exact StackFinal|].
              split; [exact PCFinal|]. split; [exact Return|].
              intros other xs ND NP NT NO A. apply FrameFinal; try assumption. apply Frame2; assumption.
    + destruct (le_dec d (nat_of_ord position + 16)) as [Near|Far].
      * destruct (SuccessfulExchange source p depths position c llvm1 machine1 previous varargs
          Position Values Different Near ltac:(lia) Related1 Arrays Registers1 Binding State1 PC1 Selected1)
          as (c2 & llvm2 & machine2 & count2 & Related2 & Arrays2 & Registers2 & Exchange &
            Machine2 & State2 & PC2 & Frame2).
        destruct (IH (model_swap source position) (model_exchange p position)
          (List.app depths [model_depth position]) c2 llvm2 machine2 (Name "if.end169"%string)
          NextRank ltac:(rewrite List.length_app; cbn; lia)
          (model_swap_uint d source position Values) Related2 Arrays2 Registers2 State2 PC2)
          as (c' & llvm' & machine' & count3 & code & RelatedFinal & ResultCode & Result & LLVMRest &
            MachineRest & CodeFinal & PresentFinal & StackFinal & PCFinal & Return & FrameFinal).
        exists c', llvm', machine', (count1 + (count2 + count3))%nat, code.
        split; [exact RelatedFinal|]. split; [exact ResultCode|]. split.
        -- rewrite (@model_run_near d fuel source p depths position Choice Different Near). exact Result.
        -- split.
           ++ eapply block_steps_return; [exact Choose|]. eapply block_steps_return; eassumption.
           ++ split.
              ** eapply instruction_steps_append; [exact Machine1|].
                 eapply instruction_steps_append; eassumption.
              ** split; [exact CodeFinal|]. split; [exact PresentFinal|]. split; [exact StackFinal|].
                 split; [exact PCFinal|]. split; [exact Return|].
                 intros other xs ND NP NT NO A. apply FrameFinal; try assumption. apply Frame2; assumption.
      * assert (FarBound : (nat_of_ord position + 16 < d)%nat) by lia.
        destruct (BlockedExchange source p depths position c llvm1 machine1 previous varargs
          Values Different FarBound Related1 Arrays Registers1 Binding State1 PC1 Selected1)
          as (c2 & llvm2 & machine2 & count2 & Related2 & Result & Exchange & Machine2 &
            Code2 & Present2 & Stack2 & PC2 & Return2 & Frame2).
        exists c2, (cleanup_state llvm2 1), machine2, (count1 + count2)%nat, 1.
        split.
        -- split; [rewrite cleanup_memory; exact (proj1 Related2)|exact (proj2 Related2)].
        -- split; [right; reflexivity|]. split.
           ++ rewrite (@model_run_blocked d fuel source p depths position Choice Different FarBound). exact Result.
           ++ split.
              ** eapply block_steps_return; [exact Choose|].
                 eapply cleanup_after_steps; [exact Exchange|constructor].
              ** split; [eapply instruction_steps_append; eassumption|].
                 split; [exact Code2|]. split; [exact Present2|]. split; [exact Stack2|].
                 split; [exact PC2|]. split; assumption.
  - cbn [option_map choose_target choice_machine_target choice_machine_binding choose_binding]
      in Choose, Binding, PC1, Selected1. subst previous.
    destruct (done_path true layout frame initial machine1 Code1 Present1 Stack1 PC1)
      as (machine2 & Machine2 & Memory2 & Code2 & Present2 & Stack2 & PC2 & Return2).
    exists c, (cleanup_state llvm1 0), machine2, (count1 + 2)%nat, 0.
    split.
    + split; [rewrite cleanup_memory; exact (proj1 Related1)|].
      rewrite Memory2. exact (proj2 Related1).
    + split; [left; reflexivity|]. split.
      * rewrite (@model_run_done d fuel source p depths Choice). cbn [result_arrays].
        destruct Arrays as [Data Perm Trace Output Writable].
        split; [reflexivity|]. split; [exact Data|]. split; [exact Perm|]. split; assumption.
      * split.
        -- eapply cleanup_after_steps; [exact Choose|constructor].
        -- split; [eapply instruction_steps_append; eassumption|].
           split; [exact Code2|]. split; [exact Present2|]. split; [exact Stack2|].
           split; [exact PC2|]. split; [exact Return2|].
           intros other xs ND NP NT NO A. exact A.
Qed.
End MainLoop.

Print Assumptions main_loop_from_exchange_agreements.
