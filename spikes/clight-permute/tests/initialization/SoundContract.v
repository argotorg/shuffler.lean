(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List.
From compcert Require Import AST Ctypes Clight.
Require Import Permute AssignmentCheck AssignmentSound.

(* Independent public type fixtures. They require human review together
   with the definitions of the control-path relations. *)
Definition complete_contract :
  forall s initial final kind safe,
    assignment_path s initial final kind safe ->
    forall known paths, check known s = Some paths -> incl known initial ->
      safe = true /\ guarantees paths kind final := complete_path_safe.

Definition prefix_contract :
  forall s initial safe,
    assignment_prefix s initial safe ->
    forall known paths, check known s = Some paths -> incl known initial -> safe = true :=
  prefix_safe.

Definition function_contract :
  forall fn safe,
    check_function fn = true ->
    assignment_prefix (fn_body fn) (map fst (fn_params fn)) safe -> safe = true :=
  checked_function_prefix.

Definition actual_permute_contract :
  forall safe,
    assignment_prefix (fn_body permute) (map fst (fn_params permute)) safe -> safe = true :=
  permute_prefix_safe.

Print Assumptions complete_contract.
Print Assumptions prefix_contract.
Print Assumptions function_contract.
Print Assumptions actual_permute_contract.
