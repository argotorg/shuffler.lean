(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List.
From compcert Require Import AST Ctypes Clight ClightBigstep.
Require Import Permute AssignmentCheck AssignmentSound AssignmentExec.

(* Review these types with recorded_exec and supported. The record retains
   concrete branch decisions and intermediate Clight states. *)
Definition erasure_contract :
  forall function_entry ge e le m s t le' m' out initial final safe,
    recorded_exec ge e le m s t le' m' out initial final safe ->
    exec_stmt function_entry ge e le m s t le' m' out := recorded_erases.

Definition execution_coverage_contract :
  forall function_entry ge e le m s t le' m' out,
    exec_stmt function_entry ge e le m s t le' m' out ->
    supported s -> forall initial,
    exists final safe, recorded_exec ge e le m s t le' m' out initial final safe :=
  execution_recorded.

Definition path_contract :
  forall ge e le m s t le' m' out initial final safe,
    recorded_exec ge e le m s t le' m' out initial final safe ->
    exists kind, outcome_kind out = Some kind /\
      assignment_path s initial final kind safe := recorded_path.

Definition execution_safety_contract :
  forall ge e le m s t le' m' out initial final safe paths,
    check initial s = Some paths ->
    recorded_exec ge e le m s t le' m' out initial final safe -> safe = true :=
  checked_execution_safe.

Definition permute_execution_contract :
  forall function_entry ge e le m t le' m' out,
    exec_stmt function_entry ge e le m (fn_body permute) t le' m' out ->
    exists final, recorded_exec ge e le m (fn_body permute) t le' m' out
      (map fst (fn_params permute)) final true := permute_execution_safe.

Print Assumptions erasure_contract.
Print Assumptions execution_coverage_contract.
Print Assumptions path_contract.
Print Assumptions execution_safety_contract.
Print Assumptions permute_execution_contract.
