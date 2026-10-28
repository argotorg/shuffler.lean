(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Functor.
From compcert Require Import Integers.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  MemoryBytes MemoryBytesFacts Interfaces.Memory Implementations.Memory.
Require Import MemoryRelation.
Import ListNotations.

Module LLVMInt := Vellvm.Numeric.Integers.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition word_value (x : Int.int) : dvalue :=
  DVALUE_Base (DVALUE_I 32 (LLVMInt.repr (Int.unsigned x))).

Definition word_byte (x : Int.int) (index : N) : memory_byte :=
  base_byte_gen (DVALUE_I 32 (LLVMInt.repr (Int.unsigned x))) index.

Definition word_bytes (x : Int.int) : list memory_byte :=
  [word_byte x 0; word_byte x 1; word_byte x 2; word_byte x 3].

Lemma encode_word x :
  dvalue_to_memory_bytes (DTYPE_I 32) (word_value x) None =
    EOU.raise_ret (word_bytes x).
Proof. reflexivity. Qed.

Lemma decode_word x :
  memory_bytes_to_dvalue (word_bytes x) (DTYPE_I 32) =
    EOU.raise_ret (word_value x).
Proof.
  (* The general aggregate round-trip theorem uses Eq_rect_eq. The integer
     theorem proves exactly the case needed here without that axiom. *)
  pose proof (@read_int_block_mult8 parameters 32
    (LLVMInt.repr (Int.unsigned x)) eq_refl) as Read.
  change (memory_bytes_to_dvalue_base (word_bytes x) (DTYPE_I 32) =
    EOU.raise_ret (DVALUE_I 32 (LLVMInt.repr (Int.unsigned x)))) in Read.
  change (fmap DVALUE_Base
    (memory_bytes_to_dvalue_base (word_bytes x) (DTYPE_I 32)) =
    EOU.raise_ret (word_value x)).
  now rewrite Read.
Qed.

Definition word_at s address provenance x : Prop :=
  four_bytes_at s address provenance
    (word_byte x 0) (word_byte x 1) (word_byte x 2) (word_byte x 3).

(* This permits poison and other unspecified initial contents in scratch
   storage. Only allocation and access permission are required. *)
Definition writable_word s address provenance : Prop :=
  exists b0 b1 b2 b3, four_bytes_at s address provenance b0 b1 b2 b3.

Lemma word_at_writable s address provenance x :
  word_at s address provenance x -> writable_word s address provenance.
Proof.
  intro H. exists (word_byte x 0), (word_byte x 1),
    (word_byte x 2), (word_byte x 3). exact H.
Qed.

Lemma byte_at_unchanged s final address provenance b :
  IntMaps.IM.find address (bytes final) = IntMaps.IM.find address (bytes s) ->
  byte_at s address provenance b -> byte_at final address provenance b.
Proof. intros E [aid [F A]]; exists aid; split; [now rewrite E|exact A]. Qed.

Lemma four_bytes_unchanged s final address provenance b0 b1 b2 b3 :
  (forall a, (address <= a < address + 4)%Z ->
    IntMaps.IM.find a (bytes final) = IntMaps.IM.find a (bytes s)) ->
  four_bytes_at s address provenance b0 b1 b2 b3 ->
  four_bytes_at final address provenance b0 b1 b2 b3.
Proof.
  intros Frame [B0 [B1 [B2 B3]]]. repeat split;
    (eapply byte_at_unchanged; [apply Frame; lia|eassumption]).
Qed.

Lemma word_at_unchanged s final address provenance x :
  (forall a, (address <= a < address + 4)%Z ->
    IntMaps.IM.find a (bytes final) = IntMaps.IM.find a (bytes s)) ->
  word_at s address provenance x -> word_at final address provenance x.
Proof. apply four_bytes_unchanged. Qed.

Lemma writable_word_unchanged s final address provenance :
  (forall a, (address <= a < address + 4)%Z ->
    IntMaps.IM.find a (bytes final) = IntMaps.IM.find a (bytes s)) ->
  writable_word s address provenance -> writable_word final address provenance.
Proof.
  intros Frame [b0 [b1 [b2 [b3 H]]]].
  exists b0, b1, b2, b3. eapply four_bytes_unchanged; eassumption.
Qed.

Lemma load_word_steps s address provenance x :
  word_at s address provenance x ->
  memory_steps (Impl.read_dvalue (DTYPE_I 32) (address, provenance)) s s
    (word_value x).
Proof.
  intro H. unfold Impl.read_dvalue.
  eapply memory_steps_bind.
  - apply read_four_steps, H.
  - change (memory_steps
      (lift (memory_bytes_to_dvalue (word_bytes x) (DTYPE_I 32)))
      s s (word_value x)).
    rewrite decode_word. constructor.
Qed.

Lemma load_word_correct s address provenance x :
  word_at s address provenance x ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (address, provenance)) s =
    Ret (s, word_value x).
Proof. intro H; apply memory_steps_sound, load_word_steps, H. Qed.

Lemma store_word_correct s address provenance x :
  writable_word s address provenance ->
  exists final,
    run_memory (Impl.write_dvalue (address, provenance) (DTYPE_I 32)
      (word_value x)) s = Ret (final, tt) /\
    word_at final address provenance x /\
    (forall other, (other < address \/ address + 4 <= other)%Z ->
      IntMaps.IM.find other (bytes final) = IntMaps.IM.find other (bytes s)) /\
    Impl.Memory_stack_frame_stack (Impl.state_memory_stack final) =
      Impl.Memory_stack_frame_stack (Impl.state_memory_stack s) /\
    Impl.Memory_stack_heap (Impl.state_memory_stack final) =
      Impl.Memory_stack_heap (Impl.state_memory_stack s) /\
    Impl.state_provenance final = Impl.state_provenance s.
Proof.
  intros [b0 [b1 [b2 [b3 H]]]].
  unfold Impl.write_dvalue. rewrite encode_word.
  exact (@write_four_correct s address provenance b0 b1 b2 b3
    (word_byte x 0) (word_byte x 1) (word_byte x 2) (word_byte x 3) H).
Qed.
