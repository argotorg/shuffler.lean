(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
Require Import Permute ClightMemory ClightScalar ClightCall ClightCorrect
  ModelArrays SolcModel ModelSpec PermuteSpec.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG MainBody.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma result_return_equal d bd bp trace output (result : SolcResult nat (S d)) c1 c2 x y :
  @result_arrays d bd bp trace output result c1 (Out_return (Some (Vint x, Permute.u32))) ->
  @result_arrays d bd bp trace output result c2 (Out_return (Some (Vint y, Permute.u32))) ->
  x = y.
Proof. destruct result; cbn [result_arrays]; intros; intuition congruence. Qed.

Lemma related_writable layout c memory b count :
  cells_related layout c memory -> (count <= block_words layout b)%coq_nat ->
  writable_array c b count.
Proof. intros Related Capacity k K. exact (proj1 (Related b k ltac:(lia))). Qed.

(* This theorem compares the full Clight call with the LLVM body. Function
   argument binding and frame operations are proved separately. Both sides
   have the same model result, including partial results on a blocked swap. *)
Theorem permute_body_clight layout d bd bp bt bu trace output ge
    (source : 'I_(S d) -> nat) (p : 'S_(S d)) c s varargs :
  separate_arrays bd bp bt bu trace output -> (S d <= 1024)%coq_nat ->
  (S d <= block_words layout bd)%coq_nat -> (S d <= block_words layout bp)%coq_nat ->
  (S d <= block_words layout bt)%coq_nat -> (S d <= block_words layout bu)%coq_nat ->
  (2 * S d <= block_words layout trace)%coq_nat -> (3 <= block_words layout output)%coq_nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun i => nat_of_ord (p i))) ->
  permute_registers layout d bd bp bt bu trace output s ->
  exists result clight_final llvm_cells llvm_final code,
    solc_permute source p = Some result /\ solc_result_spec source p result /\
    (code = 0 \/ code = 1) /\
    eval_funcall function_entry2 ge c (Internal Permute.permute)
      (call_arguments (Int.repr (Z.of_nat (S d))) (Vptr bd Ptrofs.zero)
        (Vptr bp Ptrofs.zero) (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
        (Vptr trace Ptrofs.zero) (Vptr output Ptrofs.zero)) E0 clight_final (Vint (Int.repr code)) /\
    runs (denote_cfg FullCFG.body varargs) s llvm_final (word_value (Int.repr code)) /\
    cells_related layout llvm_cells (fst llvm_final) /\
    @result_arrays d bd bp trace output result clight_final
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    @result_arrays d bd bp trace output result llvm_cells
      (Out_return (Some (Vint (Int.repr code), Permute.u32))).
Proof.
  intros Separate Size CD CP CT CU CR CO Values Related Data Perm Registers.
  destruct (@ClightCorrect.permute_call_correct d ge c bd bp bt bu trace output source p
    Size Separate Values Data Perm
    (@related_writable layout c (fst s) bt (S d) Related CT)
    (@related_writable layout c (fst s) bu (S d) Related CU)
    (@related_writable layout c (fst s) trace (2 * S d) Related CR)
    (@related_writable layout c (fst s) output 3 Related CO))
    as [clight_final [clight_code [result [Clight [Model [ClightArrays [Spec ClightCode]]]]]]].
  destruct (@permute_body_refines layout d bd bp bt bu trace output Separate Size CD CP CT CU CR CO
    source p c s varargs Values Related Data Perm Registers)
    as [llvm_result [llvm_cells [llvm_final [code [LLVMModel [Related' [Code [LLVMArrays [LLVM Frame]]]]]]]]].
  assert (Same : result = llvm_result) by congruence. subst llvm_result.
  pose proof (@result_return_equal d bd bp trace output result clight_final llvm_cells
    (Int.repr clight_code) (Int.repr code) ClightArrays LLVMArrays) as Return.
  rewrite -> Return in Clight, ClightArrays.
  exists result, clight_final, llvm_cells, llvm_final, code.
  split; [exact Model|]. split; [exact Spec|]. split; [exact Code|].
  split; [exact Clight|]. split; [exact LLVM|]. split; [exact Related'|].
  split; assumption.
Qed.
