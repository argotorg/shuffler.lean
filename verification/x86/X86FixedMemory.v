(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightExchangeSuccess ModelArrays ClightNormalize.
Require Import CellRelation FixedBlocks Fixed.
From X86 Require Import X86NormalizeStores.
Import ListNotations.
Open Scope Z_scope.

Section FixedMemory.
Context (layout : allocation_layout) (count : nat)
    (source desired : 'I_count -> nat) (bd bt bp bu : Values.block).
Hypothesis Bound : (count <= 1024)%coq_nat.
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (TP : bt <> bp) (TU : bt <> bu) (PU : bp <> bu).
Hypotheses (CD : (count <= block_words layout bd)%coq_nat)
    (CT : (count <= block_words layout bt)%coq_nat)
    (CP : (count <= block_words layout bp)%coq_nat)
    (CU : (count <= block_words layout bu)%coq_nat).
Hypotheses (SourceUInt : forall x, uint (Z.of_nat (source x)))
    (TargetUInt : forall x, uint (Z.of_nat (desired x))).

Let invariant := @Fixed.fixed_invariant count source desired bd bt bp bu.

Theorem fixed_store_step (index : 'I_count) original c llvm :
  cells_related layout c llvm -> invariant original (nat_of_ord index) c ->
  exists final,
    normalize_stores bp bu (nat_of_ord index)
      (word_equal (Int.repr (Z.of_nat (source index)))
        (Int.repr (Z.of_nat (desired index)))) c final /\
    invariant original (S (nat_of_ord index)) final /\
    Fixed.fixed_frame bp bu c final.
Proof.
  intros Related Inv.
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  pose (choice := Nat.eqb (source index) (desired index)).
  pose (assignment := fixed_assignment source desired original (nat_of_ord index)).
  pose (flags := List.firstn (nat_of_ord index) (words (fixed_flags source desired))).
  destruct Inv as [AD AT AP AU].
  assert (UsedWritable : Mem.valid_access c Mint32 bu (4 * Z.of_nat (nat_of_ord index)) Writable).
  { exact (proj1 (Related bu (nat_of_ord index) ltac:(lia))). }
  assert (Branch : exists middle,
    (if choice then
       Mem.store Mint32 c bp (4 * Z.of_nat (nat_of_ord index))
         (Vint (Int.repr (Z.of_nat (nat_of_ord index)))) = Some middle
     else middle = c) /\
    @Fixed.fixed_arrays count source desired bd bt bp bu
      (if choice then update_value assignment index (nat_of_ord index) else assignment) flags middle /\
    Mem.valid_access middle Mint32 bu (4 * Z.of_nat (nat_of_ord index)) Writable /\
    Fixed.fixed_frame bp bu c middle).
  { destruct choice.
    - destruct (Mem.valid_access_store c Mint32 bp (4 * Z.of_nat (nat_of_ord index))
        (Vint (Int.repr (Z.of_nat (nat_of_ord index))))
        (proj1 (Related bp (nat_of_ord index) ltac:(lia)))) as [middle Store].
      exists middle. split; [exact Store|]. split.
      + constructor.
        * eapply array_store_disjoint; [exact AD|exact DP|exact Store].
        * eapply array_store_disjoint; [exact AT|exact TP|exact Store].
        * rewrite <- words_update. eapply array_store_same; [exact AP|exact Store].
        * eapply array_store_disjoint; [exact AU|exact (not_eq_sym PU)|exact Store].
      + split.
        * eapply Mem.store_valid_access_1; [exact Store|exact UsedWritable].
        * intros other values NotPerm NotUsed Array.
          eapply array_store_disjoint; [exact Array|exact NotPerm|exact Store].
    - exists c. split; [reflexivity|]. split; [constructor; assumption|].
      split; [exact UsedWritable|]. intros other values NotPerm NotUsed Array. exact Array. }
  destruct Branch as [middle [AssignmentStore [Arrays [Writable Frame]]]].
  destruct (Mem.valid_access_store middle Mint32 bu (4 * Z.of_nat (nat_of_ord index))
    (Vint (flag_word choice)) Writable) as [final UsedStore].
  exists final. split.
  - rewrite -> natural_word_equal by auto. fold choice.
    exists middle. split; assumption.
  - split.
    + destruct Arrays as [Data Target Perm Used]. constructor.
      * eapply array_store_disjoint; [exact Data|exact DU|exact UsedStore].
      * eapply array_store_disjoint; [exact Target|exact TU|exact UsedStore].
      * unfold assignment, choice in Perm. rewrite -> fixed_assignment_step in Perm.
        eapply array_store_disjoint; [exact Perm|exact PU|exact UsedStore].
      * rewrite -> (firstn_step _ (nat_of_ord index) (Z.of_nat (fixed_flags source desired index)))
          by exact (words_nth_error (fixed_flags source desired) index).
        eapply array_append_store; [exact Used|].
        unfold flags. rewrite -> List.firstn_length, words_length, Nat.min_l by lia.
        unfold flag_word, choice in UsedStore. unfold fixed_flags.
        destruct (Nat.eqb (source index) (desired index)); exact UsedStore.
    + intros other values NotPerm NotUsed Array.
      eapply array_store_disjoint; [apply Frame; eassumption|exact NotUsed|exact UsedStore].
Qed.
End FixedMemory.

Print Assumptions fixed_store_step.
