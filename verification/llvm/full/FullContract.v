(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
Require Import Permute ClightMemory ClightScalar ClightCall ClightCorrect
  ModelArrays SolcModel ModelSpec PermuteSpec.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory IntMaps TypToDtyp.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG
  BodyEquivalence FullCall ModuleCall FullEquivalence Normalize FullProgram.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* The contract is parameterized by the AST that the printer consumes. It
   includes all three complete-call statements and the single-function shape.
   The memory observations are the same as in FullEquivalence. *)
Definition module_function_table (program : Normalize.llvm_module) (address : ptr)
    : IntMap function_denotation :=
  IntMaps.add_all
    (List.map (fun f => (ptr_to_int address, denote_function f))
      (m_definitions (convert_types (mcfg_of_tle program)))) IntMaps.empty.

Definition nonempty_equivalence (program : Normalize.llvm_module) (function : definition dtyp (cfg dtyp)) : Prop :=
  forall layout d bd bp bt bu trace output ge function_address
    (source : 'I_(S d) -> nat) (p : 'S_(S d)) c caller,
  separate_arrays bd bp bt bu trace output -> (S d <= 1024)%coq_nat ->
  (S d <= block_words layout bd)%coq_nat -> (S d <= block_words layout bp)%coq_nat ->
  (S d <= block_words layout bt)%coq_nat -> (S d <= block_words layout bu)%coq_nat ->
  (2 * S d <= block_words layout trace)%coq_nat -> (3 <= block_words layout output)%coq_nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst caller) ->
  array_at c bd (words source) -> array_at c bp (words (fun i => nat_of_ord (p i))) ->
  exists result clight_final llvm_cells llvm_final code,
    solc_permute source p = Some result /\ solc_result_spec source p result /\
    (code = 0 \/ code = 1) /\
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments (Int.repr (Z.of_nat (S d))) (Vptr bd Ptrofs.zero)
        (Vptr bp Ptrofs.zero) (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
        (Vptr trace Ptrofs.zero) (Vptr output Ptrofs.zero)) E0 clight_final (Vint (Int.repr code)) /\
    runs (denote_function function
      (permute_arguments layout (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr code))) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (module_function_table program function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value (Int.repr code)))) /\
    snd llvm_final = snd caller /\
    cells_related layout llvm_cells (fst llvm_final) /\
    @result_arrays d bd bp trace output result clight_final
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    @result_arrays d bd bp trace output result llvm_cells
      (Out_return (Some (Vint (Int.repr code), Permute.u32))).

Definition empty_equivalence (program : Normalize.llvm_module) : Prop :=
  forall layout bd bp bt bu trace output ge function_address c caller,
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists clight_final llvm_cells llvm_final,
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments Int.zero (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
        (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero)
        (Vptr output Ptrofs.zero)) E0 clight_final (Vint Int.zero) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (module_function_table program function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout Int.zero bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value Int.zero))) /\
    cells_related layout llvm_cells (fst llvm_final) /\
    array_at clight_final output (0 :: 0 :: 0 :: nil) /\
    array_at llvm_cells output (0 :: 0 :: 0 :: nil) /\ snd llvm_final = snd caller.

Definition oversized_equivalence (program : Normalize.llvm_module) : Prop :=
  forall layout bd bp bt bu trace output ge function_address n c caller,
  1024 < Int.unsigned n ->
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists clight_final llvm_cells llvm_final,
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments n (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
        (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero)
        (Vptr output Ptrofs.zero)) E0 clight_final (Vint (Int.repr 2)) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (module_function_table program function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout n bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value (Int.repr 2)))) /\
    cells_related layout llvm_cells (fst llvm_final) /\
    array_at clight_final output (0 :: 0 :: 0 :: nil) /\
    array_at llvm_cells output (0 :: 0 :: 0 :: nil) /\ snd llvm_final = snd caller.

Definition module_equivalence (program : Normalize.llvm_module) : Prop :=
  exists function,
    m_definitions (convert_types (mcfg_of_tle program)) = function :: nil /\
    dc_name (df_prototype function) = Name "permute"%string /\
    nonempty_equivalence program function /\
    empty_equivalence program /\ oversized_equivalence program.

Theorem full_module_equivalence : module_equivalence FullProgram.program.
Proof.
  exists FullCFG.function. split; [exact (proj2_sig FullCFG.single_function)|].
  split; [exact FullCFG.function_name|].
  split; [exact permute_calls_agree|].
  split; [exact empty_calls_agree|exact oversized_calls_agree].
Qed.

Definition certified_module :
    {program : Normalize.llvm_module | module_equivalence program} :=
  exist _ FullProgram.program full_module_equivalence.

Print Assumptions full_module_equivalence.
