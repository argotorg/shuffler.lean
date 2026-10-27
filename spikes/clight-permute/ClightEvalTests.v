(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Coq Require Import List ZArith.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs
  Ctypes Cop Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs.
Import ListNotations.
Open Scope Z_scope.

Definition empty_ge : genv :=
  {| genv_genv := Genv.empty_genv fundef type []; genv_cenv := PTree.empty _ |}.
Definition empty_le : temp_env := PTree.empty _.

Example literal_unsigned_max :
  expression empty_ge empty_le Mem.empty (lit 4294967295) =
  Some (Vint (Int.repr 4294967295)).
Proof. reflexivity. Qed.

Example missing_temp : expression empty_ge empty_le Mem.empty (reg i) = None.
Proof. reflexivity. Qed.

Example wrong_pointer_kind :
  expression empty_ge empty_le Mem.empty (Ederef (lit 0) u32) = None.
Proof. reflexivity. Qed.

Example unsupported_expression :
  expression empty_ge empty_le Mem.empty (Esizeof u32 u32) = None.
Proof. reflexivity. Qed.

Example unsupported_lvalue :
  store empty_ge empty_le Mem.empty (reg i) (lit 1) = None.
Proof. reflexivity. Qed.

Example no_fuel : execute 0 empty_ge empty_le Mem.empty (fn_body permute) = None.
Proof. reflexivity. Qed.

Example unsupported_call :
  execute 2 empty_ge empty_le Mem.empty (Scall None (lit 0) []) = None.
Proof. reflexivity. Qed.

Example unsupported_loop_tail :
  execute 2 empty_ge empty_le Mem.empty (Sloop Sbreak Sbreak) = None.
Proof. reflexivity. Qed.

Example stop_loop :
  execute 2 empty_ge empty_le Mem.empty (Sloop Sbreak Sskip) =
    Some (empty_le, Mem.empty, Out_normal).
Proof. reflexivity. Qed.

Example finite_fuel_bounds_loop :
  execute 3 empty_ge empty_le Mem.empty (Sloop Sskip Sskip) = None.
Proof. reflexivity. Qed.

Example return_stops_sequence :
  execute 2 empty_ge empty_le Mem.empty (Ssequence (ret 0) (Scall None (lit 0) [])) =
    Some (empty_le, Mem.empty, Out_return (Some (Vint (Int.repr 0), u32))).
Proof. reflexivity. Qed.

Example temporary_assignment_and_return :
  execute 3 empty_ge empty_le Mem.empty
    (Ssequence (set i (lit 42)) (Sreturn (Some (reg i)))) =
    Some (PTree.set i (Vint (Int.repr 42)) empty_le, Mem.empty,
      Out_return (Some (Vint (Int.repr 42), u32))).
Proof. reflexivity. Qed.

Example assignment_return_has_defined_execution :
  exec_stmt function_entry2 empty_ge (PTree.empty _) empty_le Mem.empty
    (Ssequence (set i (lit 42)) (Sreturn (Some (reg i)))) E0
    (PTree.set i (Vint (Int.repr 42)) empty_le) Mem.empty
    (Out_return (Some (Vint (Int.repr 42), u32))).
Proof. apply (execute_sound 3). exact temporary_assignment_and_return. Qed.
