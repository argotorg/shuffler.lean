(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Extraction ExtrOcamlBasic ExtrOcamlString DecimalString.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Ctypes Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs Driver.
Import ListNotations.
Open Scope Z_scope.

Definition execute_function fuel ge fn args m :=
  match bind_parameter_temps (fn_params fn) args
      (create_undef_temps (fn_temps fn)) with
  | Some le => execute fuel ge le m (fn_body fn)
  | None => None
  end.

(* The syntax premises are explicit. The printer checks these declaration
   conditions, but that OCaml check is not proved by this theorem. *)
Theorem generated_call fuel ge fn args initial le' final code :
  fn_vars fn = [] ->
  list_norepet (var_names (fn_params fn)) ->
  list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn)) ->
  fn_return fn = u32 ->
  execute_function fuel ge fn args initial =
    Some (le', final, Out_return (Some (Vint code, u32))) ->
  eval_funcall function_entry2 ge initial (Internal fn) args E0 final (Vint code).
Proof.
  intros Vars Params Separate Return H.
  unfold execute_function in H.
  destruct (bind_parameter_temps (fn_params fn) args
    (create_undef_temps (fn_temps fn))) as [le|] eqn:Bind; try discriminate.
  eapply eval_funcall_internal.
  - constructor.
    + rewrite Vars. constructor.
    + exact Params.
    + exact Separate.
    + rewrite Vars. constructor.
    + exact Bind.
  - apply (execute_sound fuel). exact H.
  - rewrite Return. split; [discriminate|reflexivity].
  - reflexivity.
Qed.

Definition run_generated (fuel : nat) (fn : function) (xs ys : list Z)
    : option (list Z) :=
  if (Nat.eqb (length xs) 8 && Nat.eqb (length ys) 8)%bool then
    let '(m1, bd) := Mem.alloc Mem.empty 0 32 in
    let '(m2, bp) := Mem.alloc m1 0 32 in
    let '(m3, bo) := Mem.alloc m2 0 12 in
    match write_words m3 bd 0 xs with
    | Some m4 =>
        match write_words m4 bp 0 ys with
        | Some m5 =>
            let args := [Vint (Int.repr 8); Vptr bd Ptrofs.zero;
                         Vptr bp Ptrofs.zero; Vzero; Vzero; Vzero;
                         Vptr bo Ptrofs.zero] in
            match execute_function fuel empty_ge fn args m5 with
            | Some (_, final, Out_return (Some (Vint status, ty))) =>
                if type_eq ty u32 then
                  match read_words final bo 0 3, read_words final bd 0 8,
                        read_words final bp 0 8 with
                  | Some (0 :: outputs), Some a, Some b =>
                      Some (Int.unsigned status :: 0 :: outputs ++ a ++ b)
                  | _, _, _ => None
                  end
                else None
            | _ => None
            end
        | None => None
        end
    | None => None
    end
  else None.

Definition decimal_int (v : Int.int) := decimal (Int.unsigned v).
Definition decimal_ident (v : positive) := decimal (Zpos v).
Extraction Language OCaml.
Extraction "extracted.ml" run_generated decimal decimal_int decimal_ident
  permute u32 i32 ptr lit reg cell add sub eq ne lt gt ge seq set put ret when loop inc.
Print Assumptions generated_call.
