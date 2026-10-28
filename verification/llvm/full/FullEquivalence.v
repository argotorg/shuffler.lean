(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
Require Import Permute ClightMemory ClightScalar ClightCall ClightCorrect
  ModelArrays SolcModel ModelSpec PermuteSpec.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG
  BodyEquivalence FullCall ModuleCall.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* Both complete calls return the same code and model result. result_arrays
   describes data, permutation, trace prefix, and the three output fields.
   It does not assert equality of the scratch buffers or unused trace cells. *)
Theorem permute_calls_agree layout d bd bp bt bu trace output ge function_address
    (source : 'I_(S d) -> nat) (p : 'S_(S d)) c caller :
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
    runs (denote_function FullCFG.function
      (permute_arguments layout (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output))
      caller llvm_final (inr (word_value (Int.repr code))) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (permute_function_table function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value (Int.repr code)))) /\
    snd llvm_final = snd caller /\
    cells_related layout llvm_cells (fst llvm_final) /\
    @result_arrays d bd bp trace output result clight_final
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    @result_arrays d bd bp trace output result llvm_cells
      (Out_return (Some (Vint (Int.repr code), Permute.u32))).
Proof.
  intros Separate Size CD CP CT CU CR CO Values Related Data Perm.
  destruct (@ClightCorrect.permute_call_correct d ge c bd bp bt bu trace output source p
    Size Separate Values Data Perm
    (@related_writable layout c (fst caller) bt (S d) Related CT)
    (@related_writable layout c (fst caller) bu (S d) Related CU)
    (@related_writable layout c (fst caller) trace (2 * S d) Related CR)
    (@related_writable layout c (fst caller) output 3 Related CO))
    as [clight_final [clight_code [result [Clight [Model [ClightArrays [Spec ClightCode]]]]]]].
  destruct (@FullCall.permute_call_refines layout d bd bp bt bu trace output
    Separate Size CD CP CT CU CR CO source p c caller Values Related Data Perm)
    as [llvm_result [llvm_cells [llvm_final [code
      [LLVMModel [Related' [Code [LLVMArrays [LLVM [Caller Frame]]]]]]]]]].
  assert (Same : result = llvm_result) by congruence. subst llvm_result.
  pose proof (@result_return_equal d bd bp trace output result clight_final llvm_cells
    (Int.repr clight_code) (Int.repr code) ClightArrays LLVMArrays) as Return.
  rewrite -> Return in Clight, ClightArrays.
  exists result, clight_final, llvm_cells, llvm_final, code.
  split; [exact Model|]. split; [exact Spec|]. split; [exact Code|].
  split; [exact Clight|]. split; [exact LLVM|].
  split; [apply permute_module_call, LLVM|]. split; [exact Caller|].
  split; [exact Related'|]. split; assumption.
Qed.

Theorem empty_calls_agree layout bd bp bt bu trace output ge function_address c caller :
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists clight_final llvm_cells llvm_final,
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments Int.zero (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
        (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero)
        (Vptr output Ptrofs.zero)) E0 clight_final (Vint Int.zero) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (permute_function_table function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout Int.zero bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value Int.zero))) /\
    cells_related layout llvm_cells (fst llvm_final) /\
    array_at clight_final output (0 :: 0 :: 0 :: nil) /\
    array_at llvm_cells output (0 :: 0 :: 0 :: nil) /\ snd llvm_final = snd caller.
Proof.
  intros Related CO.
  destruct (@ClightCall.permute_empty_call ge c (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
    (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero) output
    (@related_writable layout c (fst caller) output 3 Related CO))
    as [clight_final [Clight ClightOutput]].
  destruct (@FullCall.empty_call_refines layout output c caller
    (mapped_pointer layout bd) (mapped_pointer layout bp) (mapped_pointer layout bt)
    (mapped_pointer layout bu) (mapped_pointer layout trace) Related CO)
    as [llvm_cells [llvm_final [Related' [LLVMOutput [LLVM [Caller Frame]]]]]].
  exists clight_final, llvm_cells, llvm_final. split; [exact Clight|].
  split; [apply permute_module_call, LLVM|]. split; [exact Related'|].
  split; [exact ClightOutput|]. split; assumption.
Qed.

Theorem oversized_calls_agree layout bd bp bt bu trace output ge function_address n c caller :
  1024 < Int.unsigned n ->
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists clight_final llvm_cells llvm_final,
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments n (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
        (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero)
        (Vptr output Ptrofs.zero)) E0 clight_final (Vint (Int.repr 2)) /\
    eutt Logic.eq (interp_mcfg (denote_mcfg (permute_function_table function_address) (DTYPE_I 32)
      (DVALUE_Base (DVALUE_Pointer function_address))
      (permute_arguments layout n bd bp bt bu trace output)) caller)
      (Ret (llvm_final, inr (word_value (Int.repr 2)))) /\
    cells_related layout llvm_cells (fst llvm_final) /\
    array_at clight_final output (0 :: 0 :: 0 :: nil) /\
    array_at llvm_cells output (0 :: 0 :: 0 :: nil) /\ snd llvm_final = snd caller.
Proof.
  intros Large Related CO.
  destruct (@ClightCall.permute_oversized_call ge c (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
    (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero) (Vptr trace Ptrofs.zero) output (Int.unsigned n)
    ltac:(pose proof (Int.unsigned_range_2 n); lia)
    (@related_writable layout c (fst caller) output 3 Related CO))
    as [clight_final [Clight ClightOutput]].
  rewrite -> Int.repr_unsigned in Clight.
  destruct (@FullCall.oversized_call_refines layout output n c caller
    (mapped_pointer layout bd) (mapped_pointer layout bp) (mapped_pointer layout bt)
    (mapped_pointer layout bu) (mapped_pointer layout trace) Large Related CO)
    as [llvm_cells [llvm_final [Related' [LLVMOutput [LLVM [Caller Frame]]]]]].
  exists clight_final, llvm_cells, llvm_final. split; [exact Clight|].
  split; [apply permute_module_call, LLVM|]. split; [exact Related'|].
  split; [exact ClightOutput|]. split; assumption.
Qed.

Print Assumptions permute_calls_agree.
