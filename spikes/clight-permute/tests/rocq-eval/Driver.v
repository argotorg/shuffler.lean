(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Extraction ExtrOcamlBasic ExtrOcamlString DecimalString.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs
  Ctypes Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightCall.
Import ListNotations.
Open Scope Z_scope.

Definition empty_ge : genv :=
  {| genv_genv := Genv.empty_genv fundef type []; genv_cenv := PTree.empty _ |}.

Fixpoint write_words (m : mem) (b : block) (offset : Z) (xs : list Z)
    : option mem :=
  match xs with
  | [] => Some m
  | x :: rest =>
      match Mem.store Mint32 m b offset (Vint (Int.repr x)) with
      | Some next => write_words next b (offset + 4) rest
      | None => None
      end
  end.

Fixpoint read_words (m : mem) (b : block) (offset : Z) (count : nat)
    : option (list Z) :=
  match count with
  | O => Some []
  | S remaining =>
      match Mem.load Mint32 m b offset, read_words m b (offset + 4) remaining with
      | Some (Vint x), Some rest => Some (Int.unsigned x :: rest)
      | _, _ => None
      end
  end.

(* Return only initialized observations. An invalid count, unsupported
   execution, failed memory operation, or exhausted fuel gives None. *)
Definition observe fuel size m da pa ta ua tr oa bd bp bt bo count :=
  match execute fuel empty_ge (call_temps (Int.repr size) da pa ta ua tr oa)
      m (fn_body permute) with
  | Some (_, final, Out_return (Some (Vint status, ty))) =>
      if type_eq ty u32 then
        match read_words final bo 0 3, read_words final bd 0 count,
              read_words final bp 0 count with
        | Some [written; blocked; excess], Some xs, Some ps =>
            if Z.leb written (2 * Z.of_nat count) then
              match read_words final bt 0 (Z.to_nat written) with
              | Some swaps => Some (Int.unsigned status :: written :: blocked ::
                  excess :: xs ++ ps ++ swaps)
              | None => None
              end
            else None
        | _, _, _ => None
        end
      else None
  | _ => None
  end.

Definition run (fuel : nat) (size : Z) (xs ps : list Z) : option (list Z) :=
  if (Z.eqb size 0 || Z.ltb 1024 size)%bool then
    let '(m, bo) := Mem.alloc Mem.empty 0 12 in
    observe fuel size m Vzero Vzero Vzero Vzero Vzero (Vptr bo Ptrofs.zero)
      bo bo bo bo O
  else
    let count := List.length xs in
    if (Z.eqb size (Z.of_nat count) && Nat.eqb count (List.length ps))%bool then
      let bytes := 4 * size in
      let '(m1, bd) := Mem.alloc Mem.empty 0 bytes in
      let '(m2, bp) := Mem.alloc m1 0 bytes in
      let '(m3, bt) := Mem.alloc m2 0 bytes in
      let '(m4, bu) := Mem.alloc m3 0 bytes in
      let '(m5, br) := Mem.alloc m4 0 (2 * bytes) in
      let '(m6, bo) := Mem.alloc m5 0 12 in
      match write_words m6 bd 0 xs with
      | Some m7 =>
          match write_words m7 bp 0 ps with
          | Some m8 => observe fuel size m8
              (Vptr bd Ptrofs.zero) (Vptr bp Ptrofs.zero)
              (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
              (Vptr br Ptrofs.zero) (Vptr bo Ptrofs.zero) bd bp br bo count
          | None => None
          end
      | None => None
      end
    else None.

(* This theorem connects each interpreter return to a complete Clight call.
   Extraction and the text adapters remain trusted test infrastructure. *)
Theorem interpreted_call fuel ge m size da pa ta ua tr oa le' final status :
  execute fuel ge (call_temps size da pa ta ua tr oa) m (fn_body permute) =
    Some (le', final, Out_return (Some (Vint status, u32))) ->
  eval_funcall function_entry2 ge m (Internal permute)
    (call_arguments size da pa ta ua tr oa) E0 final (Vint status).
Proof.
  intro H. apply (permute_call ge m size da pa ta ua tr oa le' final status).
  apply (execute_sound fuel). exact H.
Qed.

Example undefined_memory_is_not_zero :
  let '(m, b) := Mem.alloc Mem.empty 0 4 in read_words m b 0 1 = None.
Proof.
  destruct (Mem.alloc Mem.empty 0 4) as [m b] eqn:A.
  cbn [read_words]. destruct (Mem.load Mint32 m b 0) as [v|] eqn:L.
  - assert (v = Vundef) by (eapply Mem.load_alloc_same; eauto).
    subst v. reflexivity.
  - reflexivity.
Qed.

Example missing_fuel_is_incomplete : run 0 0 [] [] = None.
Proof. reflexivity. Qed.

Example input_length_mismatch : run 100 2 [7] [0] = None.
Proof. reflexivity. Qed.

Definition decimal (z : Z) := DecimalString.NilZero.string_of_int (Z.to_int z).
Extraction Language OCaml.
Extraction "evaluation.ml" run decimal.
Print Assumptions interpreted_call.
