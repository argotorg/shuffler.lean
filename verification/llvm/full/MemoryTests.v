(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith String.
From ITree Require Import ITree.
From compcert Require Import Integers.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  MemoryBytes LLVMEvents Interfaces.Memory Implementations.Memory.
Require Import MemoryRelation WordMemory.
Import ListNotations.
Open Scope string_scope.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition empty : Impl.State := Impl.mkState Impl.empty_memory_stack 8%N.
Definition owner : prov := Some [7%N].

Definition seed_word s address x :=
  put_four s address (word_byte x 0) (word_byte x 1)
    (word_byte x 2) (word_byte x 3) (Some 7%N) (Some 7%N) (Some 7%N) (Some 7%N).

(* Observe the production handler directly. These tests do not replace the
   handler with the memory_steps proof relation. *)
Definition returned {A} (c : memM A) s : option A :=
  match observe (run_memory c s) with
  | RetF (_, x) => Some x
  | _ => None
  end.

Definition store_then_load address x :=
  memS_bind (Impl.write_dvalue (address, owner) (DTYPE_I 32) (word_value x))
    (fun _ => Impl.read_dvalue (DTYPE_I 32) (address, owner)).

Example overwrite_all_four_bytes :
  returned (store_then_load 101 (Int.repr 305419896))
    (seed_word empty 101 (Int.repr 4294967295)) =
    Some (word_value (Int.repr 305419896)).
Proof. reflexivity. Qed.

Example write_zero :
  returned (store_then_load 101 Int.zero)
    (seed_word empty 101 (Int.repr 4294967295)) = Some (word_value Int.zero).
Proof. reflexivity. Qed.

Example write_unsigned_maximum :
  returned (store_then_load 101 (Int.repr 4294967295))
    (seed_word empty 101 Int.zero) = Some (word_value (Int.repr 4294967295)).
Proof. reflexivity. Qed.

Example adjacent_word_unchanged :
  returned
    (memS_bind (Impl.write_dvalue (101, owner) (DTYPE_I 32)
      (word_value (Int.repr 305419896)))
      (fun _ => Impl.read_dvalue (DTYPE_I 32) (105, owner)))
    (seed_word (seed_word empty 101 Int.zero) 105 (Int.repr 2864434397)) =
    Some (word_value (Int.repr 2864434397)).
Proof. reflexivity. Qed.

Example unallocated_read_is_ub :
  run_memory (Impl.read_dvalue (DTYPE_I 32) (101, owner)) empty =
    raiseUB "Reading from unallocated memory.".
Proof. reflexivity. Qed.

Example unallocated_write_is_ub :
  run_memory (Impl.write_dvalue (101, owner) (DTYPE_I 32)
    (word_value Int.zero)) empty = raiseUB "Writing to unallocated memory".
Proof. reflexivity. Qed.

Example wrong_provenance_read_is_ub :
  run_memory (Impl.read_dvalue (DTYPE_I 32) (101, Some [8%N]))
    (seed_word empty 101 Int.zero) =
    raiseUB "Read from memory with invalid provenance".
Proof. reflexivity. Qed.

Example wrong_provenance_write_is_ub :
  run_memory (Impl.write_dvalue (101, Some [8%N]) (DTYPE_I 32)
    (word_value Int.zero)) (seed_word empty 101 Int.zero) =
    raiseUB "Trying to write to memory with invalid provenance".
Proof. reflexivity. Qed.

Example access_past_last_byte_is_ub :
  run_memory (Impl.read_dvalue (DTYPE_I 32) (102, owner))
    (seed_word empty 101 Int.zero) = raiseUB "Reading from unallocated memory.".
Proof. reflexivity. Qed.
