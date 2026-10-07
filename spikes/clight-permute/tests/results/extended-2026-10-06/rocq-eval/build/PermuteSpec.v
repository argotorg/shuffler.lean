(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Public Clight call contract. This file has definitions, not proof scripts.
   The input permutation type excludes malformed permutations. ISO C object
   conditions and the source-C++ relation are outside this Clight contract. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute SolcModel ModelArrays ClightMemory ClightScalar ClightCall.
Require Export ModelSpec.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

(* Each pointer denotes a separate live array, at offset zero. *)
Record separate_arrays (bd bp bt bu btrace bo : block) : Prop := {
  separate_data_permutation : bd <> bp;
  separate_data_target : bd <> bt;
  separate_data_used : bd <> bu;
  separate_data_trace : bd <> btrace;
  separate_data_out : bd <> bo;
  separate_permutation_target : bp <> bt;
  separate_permutation_used : bp <> bu;
  separate_permutation_trace : bp <> btrace;
  separate_permutation_out : bp <> bo;
  separate_target_used : bt <> bu;
  separate_target_trace : bt <> btrace;
  separate_target_out : bt <> bo;
  separate_used_trace : bu <> btrace;
  separate_used_out : bu <> bo;
  separate_trace_out : btrace <> bo
}.

Definition trace_words (depths : list nat) := List.map Z.of_nat depths.

Section ResultMemory.
Variable d : nat.
Variables bd bp bt bo : block.

Definition result_arrays (result : SolcResult nat d.+1) memory outcome :=
  match result with
  | SolcDone s p depths =>
      outcome = Out_return (Some (Vint Int.zero, Permute.u32)) /\
      array_at memory bd (words s) /\
      array_at memory bp (words (fun i => val (p i))) /\
      array_at memory bt (trace_words depths) /\
      array_at memory bo [:: Z.of_nat (List.length depths); 0%Z; 0%Z]
  | SolcBlocked s p depths position excess =>
      outcome = Out_return (Some (Vint (Int.repr 1), Permute.u32)) /\
      array_at memory bd (words s) /\
      array_at memory bp (words (fun i => val (p i))) /\
      array_at memory bt (trace_words depths) /\
      array_at memory bo
        [:: Z.of_nat (List.length depths); Z.of_nat (val position); Z.of_nat excess]
  | SolcExhausted => False
  end.

End ResultMemory.

(* Give the six memory blocks names at the public interface. *)
Record buffers := Buffers {
  data_block : block;
  permutation_block : block;
  target_block : block;
  used_block : block;
  trace_block : block;
  output_block : block
}.

(* A stack has d+1 positions. Only data and permutation are initialized.
   Scratch and output storage need capacity, not initial contents. *)
Definition valid_call {d} (source : 'I_d.+1 -> nat) (destinations : 'S_d.+1)
    (arrays : buffers) (initial : Mem.mem) : Prop :=
  (d.+1 <= 1024)%coq_nat /\
  separate_arrays (data_block arrays) (permutation_block arrays)
    (target_block arrays) (used_block arrays) (trace_block arrays) (output_block arrays) /\
  (forall i, uint (Z.of_nat (source i))) /\
  array_at initial (data_block arrays) (words source) /\
  array_at initial (permutation_block arrays) (words (fun i => val (destinations i))) /\
  writable_array initial (target_block arrays) d.+1 /\
  writable_array initial (used_block arrays) d.+1 /\
  writable_array initial (trace_block arrays) (2 * d.+1) /\
  writable_array initial (output_block arrays) 3.

(* This is the actual complete call, including entry and return semantics.
   Its existence is a conclusion of the theorem, never a precondition. *)
Definition clight_returns d (arrays : buffers) ge initial final code : Prop :=
  eval_funcall function_entry2 ge initial (Internal Permute.permute)
    (call_arguments (Int.repr (Z.of_nat d.+1))
      (Vptr (data_block arrays) Ptrofs.zero)
      (Vptr (permutation_block arrays) Ptrofs.zero)
      (Vptr (target_block arrays) Ptrofs.zero)
      (Vptr (used_block arrays) Ptrofs.zero)
      (Vptr (trace_block arrays) Ptrofs.zero)
      (Vptr (output_block arrays) Ptrofs.zero))
    E0 final (Vint (Int.repr code)).

(* Compare the exact model result, including partial data and trace.
   result_arrays states how each result is encoded in Clight memory. *)
Definition matches_model {d} (source : 'I_d.+1 -> nat) (destinations : 'S_d.+1)
    (arrays : buffers) final code result : Prop :=
  solc_permute source destinations = Some result /\
  result_arrays (data_block arrays) (permutation_block arrays)
    (trace_block arrays) (output_block arrays) result final
    (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
  solc_result_spec source destinations result /\ (code = 0%Z \/ code = 1%Z).
