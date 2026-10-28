(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory IntMaps.
Require Import MemoryRelation Control FullCFG.
Import ListNotations.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma runs_module_call definitions dt function_value args caller final value :
  lookup_defn function_value definitions = Some (denote_function FullCFG.function) ->
  runs (denote_function FullCFG.function args) caller final value ->
  eutt eq (interp_mcfg (denote_mcfg definitions dt function_value args) caller)
    (Ret (final, value)).
Proof.
  intros Lookup Run. unfold denote_mcfg, mrec. rewrite Lookup. apply Run.
Qed.

(* The module has exactly one function. The caller supplies its registered
   address; the function denotation comes from the exact module AST. *)
Definition permute_function_table (address : ptr) : IntMap function_denotation :=
  IntMaps.add_all
    (List.map (fun f => (ptr_to_int address, denote_function f))
      (m_definitions FullCFG.llvm_module)) IntMaps.empty.

Lemma permute_function_lookup address :
  lookup_defn (DVALUE_Base (DVALUE_Pointer address)) (permute_function_table address) =
    Some (denote_function FullCFG.function).
Proof.
  unfold permute_function_table. rewrite (proj2_sig FullCFG.single_function).
  cbn [List.map IntMaps.add_all lookup_defn]. apply IntMaps.lookup_add_eq.
Qed.

Theorem permute_module_call address args caller final value :
  runs (denote_function FullCFG.function args) caller final value ->
  eutt eq (interp_mcfg (denote_mcfg (permute_function_table address) (DTYPE_I 32)
    (DVALUE_Base (DVALUE_Pointer address)) args) caller) (Ret (final, value)).
Proof.
  intro Run. eapply runs_module_call; [apply permute_function_lookup|exact Run].
Qed.

Print Assumptions permute_module_call.
