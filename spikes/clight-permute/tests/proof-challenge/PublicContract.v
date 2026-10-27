(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute SolcModel ModelProofs ModelArrays ClightMemory
  ClightScalar ClightCall ClightMain ClightCorrect PermuteSpec PermuteCorrect.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

(* Check the readable public theorem against the expanded call contract. *)
Definition public_call_contract d ge memory bd bp bt bu btrace bo
    (source : 'I_d.+1 -> nat) (p : 'S_d.+1) :
  (d.+1 <= 1024)%coq_nat -> separate_arrays bd bp bt bu btrace bo ->
  (forall x, uint (Z.of_nat (source x))) ->
  array_at memory bd (words source) ->
  array_at memory bp (words (fun x => val (p x))) ->
  writable_array memory bt d.+1 -> writable_array memory bu d.+1 ->
  writable_array memory btrace (2 * d.+1) -> writable_array memory bo 3 ->
  exists memory' code result,
    eval_funcall function_entry2 ge memory (Internal Permute.permute)
      (call_arguments (Int.repr (Z.of_nat d.+1)) (Vptr bd Ptrofs.zero)
        (Vptr bp Ptrofs.zero) (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
        (Vptr btrace Ptrofs.zero) (Vptr bo Ptrofs.zero)) E0 memory' (Vint (Int.repr code)) /\
    solc_permute source p = Some result /\
    result_arrays bd bp btrace bo result memory'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    solc_result_spec source p result /\ (code = 0%Z \/ code = 1%Z).
Proof.
intros Size Separate Values Data Permutation Target Used Trace Output.
exact (@PermuteCorrect.clight_refines_model d source p
  (Buffers bd bp bt bu btrace bo) ge memory
  (conj Size (conj Separate (conj Values (conj Data (conj Permutation
    (conj Target (conj Used (conj Trace Output))))))))).
Defined.
