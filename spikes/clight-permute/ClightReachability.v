(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute SolcModel ModelProofs Reachability ModelArrays ClightMemory
  ClightScalar ClightCall ClightMain ClightCorrect.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Lemma result_code_reachable d (source : 'I_d.+1 -> nat) (p : 'S_d.+1)
    result memory bd bp btrace bo code :
  solc_permute source p = Some result ->
  result_arrays bd bp btrace bo result memory
    (Out_return (Some (Vint (Int.repr code), Permute.u32))) ->
  (code = 0%Z \/ code = 1%Z) ->
  (code = 0%Z <-> values_reachable source p) /\
  (code = 1%Z <-> ~ values_reachable source p).
Proof.
move=> Model Arrays Codes.
case: result Model Arrays=> [data permutation trace|data permutation trace pos excess|]
  Model Arrays; last by [].
- have Reachable := success_requires_reachable Model.
  move: Arrays=> [Return _].
  case: Codes Return=> [->|->] Return; last discriminate.
  by split; split=> //.
- have Blocked : exists data permutation trace pos excess,
      solc_permute source p = Some (SolcBlocked data permutation trace pos excess).
  { by exists data, permutation, trace, pos, excess. }
  have Unreachable := (proj1 (solc_blocked_iff_unreachable source p)) Blocked.
  move: Arrays=> [Return _].
  case: Codes Return=> [->|->] Return; first discriminate.
  by split; split=> //.
Qed.

Theorem permute_call_reachability d ge memory bd bp bt bu btrace bo
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
    (code = 0%Z <-> values_reachable source p) /\
    (code = 1%Z <-> ~ values_reachable source p).
Proof.
move=> Size Separate Values Data Permutation Target Used Trace Output.
have [memory' [code [result [Run [Model [Arrays [Spec Codes]]]]]]] :=
  @permute_call_correct d ge memory bd bp bt bu btrace bo source p
    Size Separate Values Data Permutation Target Used Trace Output.
have Result := result_code_reachable Model Arrays Codes.
by exists memory', code, result; repeat split; tauto.
Qed.

Print Assumptions permute_call_reachability.
