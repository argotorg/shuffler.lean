(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Ctypes Cop Clight ClightBigstep.
Require Import Permute.
Import ListNotations.

(* The expression used to compute depth in Permute.exchange, in a function
   with the same unsigned arithmetic. The first proof has no memory accesses. *)
Definition depth_function : function := {|
  fn_return := u32;
  fn_callconv := cc_default;
  fn_params := [(top, u32); (pos, u32)];
  fn_vars := [];
  fn_temps := [];
  fn_body := Sreturn (Some (sub (reg top) (reg pos)))
|}.

Definition depth_temps (x y : Int.int) :=
  PTree.set pos (Vint y) (PTree.set top (Vint x) (PTree.empty val)).

Theorem depth_clight_call ge m x y :
  eval_funcall function_entry2 ge m (Internal depth_function)
    [Vint x; Vint y] E0 m (Vint (Int.sub x y)).
Proof.
  eapply eval_funcall_internal with
    (e := empty_env) (le1 := depth_temps x y) (le2 := depth_temps x y)
    (m1 := m) (m2 := m)
    (out := Out_return (Some (Vint (Int.sub x y), u32))).
  - constructor.
    + constructor.
    + repeat constructor; simpl; intuition discriminate.
    + unfold list_disjoint; simpl; intuition.
    + constructor.
    + reflexivity.
  - apply exec_Sreturn_some.
    eapply eval_Ebinop.
    + apply eval_Etempvar. reflexivity.
    + apply eval_Etempvar. reflexivity.
    + reflexivity.
  - split; [discriminate | reflexivity].
  - reflexivity.
Qed.
