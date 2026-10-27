(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute SolcModel ModelProofs ModelArrays ClightMemory
  ClightScalar ClightCall ClightMain ClightCorrect ClightReachability.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

(* State the value and depth condition directly, without values_reachable. *)
Definition permute_reachability_contract d ge memory bd bp bt bu btrace bo
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
    solc_result_spec source p result /\
    (code = 0%Z <->
      forall i, (16 < d - val i)%N -> source i = source (p^-1 i)) /\
    (code = 1%Z <->
      ~ (forall i, (16 < d - val i)%N -> source i = source (p^-1 i))) :=
  @ClightReachability.permute_call_reachability d ge memory bd bp bt bu btrace bo source p.
