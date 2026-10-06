(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightScalar.
Import ListNotations.
Open Scope Z_scope.

Lemma counted_test ge le m counter size index :
  0 <= index <= 1024 -> 0 <= size <= 1024 ->
  PTree.get counter le = Some (Vint (Int.repr index)) ->
  PTree.get n le = Some (Vint (Int.repr size)) ->
  expression ge le m (lt (reg counter) (reg n)) =
    Some (Val.of_bool (if zlt index size then true else false)).
Proof.
  intros I N Ix Nx.
  change (expression ge le m (Ebinop (compare_op Clt) (reg counter) (reg n) i32) =
    Some (Val.of_bool (zcompare Clt index size))).
  apply expression_compare; try reflexivity; try assumption;
    unfold uint; change Int.max_unsigned with 4294967295; lia.
Qed.

(* The invariant gives register values as well as application-specific memory
   facts. The step premise is one iteration's actual Clight execution. *)
Theorem counted_loop ge e counter size step (I : nat -> temp_env -> mem -> Prop) :
  (size <= 1024)%nat ->
  (forall k le m, I k le m ->
    PTree.get counter le = Some (Vint (Int.repr (Z.of_nat k))) /\
    PTree.get n le = Some (Vint (Int.repr (Z.of_nat size)))) ->
  (forall k le m, (k < size)%nat -> I k le m ->
    exists le' m', exec_stmt function_entry2 ge e le m step E0 le' m' Out_normal /\
      I (S k) le' m') ->
  forall start le m, (start <= size)%nat -> I start le m ->
  exists le' m',
    exec_stmt function_entry2 ge e le m
      (loop (lt (reg counter) (reg n)) step) E0 le' m' Out_normal /\
    I size le' m'.
Proof.
  intros Size Registers Step start le m Bound Invariant.
  remember (size - start)%nat as remaining eqn:Count.
  revert start le m Bound Invariant Count.
  induction remaining as [|remaining IH]; intros start le m Bound Invariant Count;
    destruct (Registers start le m Invariant) as [Counter N].
  - assert (Start : start = size) by lia. subst start.
    exists le, m. split; [|exact Invariant].
    unfold loop. eapply exec_Sloop_stop1 with (out' := Out_break).
    + eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false).
      * apply expression_sound. rewrite (counted_test ge le m counter (Z.of_nat size)
          (Z.of_nat size)) by (try assumption; lia).
        destruct (zlt (Z.of_nat size) (Z.of_nat size)); [lia|reflexivity].
      * apply bool_comparison.
      * constructor.
    + constructor.
  - assert (Start : (start < size)%nat) by lia.
    destruct (Step start le m Start Invariant) as [le1 [m1 [Execute1 Invariant1]]].
    destruct (IH (S start) le1 m1) as [le' [m' [Execute Final]]];
      try assumption; try lia.
    exists le', m'. split; [|exact Final].
    unfold loop in *. eapply exec_Sloop_loop with (le1 := le1) (m1 := m1)
      (le2 := le1) (m2 := m1) (out1 := Out_normal)
      (t1 := E0) (t2 := E0) (t3 := E0).
    + eapply exec_Sseq_1 with (le1 := le) (m1 := m) (t1 := E0) (t2 := E0).
      * eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true).
        -- apply expression_sound. rewrite (counted_test ge le m counter (Z.of_nat size)
             (Z.of_nat start)) by (try assumption; lia).
           destruct (zlt (Z.of_nat start) (Z.of_nat size)); [reflexivity|lia].
        -- apply bool_comparison.
        -- constructor.
      * exact Execute1.
    + constructor.
    + constructor.
    + exact Execute.
Qed.

Theorem each_invariant ge e counter size body (I : nat -> temp_env -> mem -> Prop) :
  (size <= 1024)%nat ->
  (forall k le m, I k le m ->
    PTree.get counter le = Some (Vint (Int.repr (Z.of_nat k))) /\
    PTree.get n le = Some (Vint (Int.repr (Z.of_nat size)))) ->
  (forall k le m, (k < size)%nat -> I k le m ->
    exists le' m',
      exec_stmt function_entry2 ge e le m (seq [body; inc counter]) E0 le' m' Out_normal /\
      I (S k) le' m') ->
  forall le m, I 0%nat (PTree.set counter (Vint (Int.repr 0)) le) m ->
  exists le' m',
    exec_stmt function_entry2 ge e le m (each counter body) E0 le' m' Out_normal /\
    I size le' m'.
Proof.
  intros Size Registers Step le m Initial.
  destruct (counted_loop ge e counter size (seq [body; inc counter]) I
    Size Registers Step 0 (PTree.set counter (Vint (Int.repr 0)) le) m)
    as [le' [m' [Execute Final]]]; try assumption; try lia.
  exists le', m'. split; [|exact Final].
  cbn [each seq fold_right].
  eapply exec_Sseq_1 with (le1 := PTree.set counter (Vint (Int.repr 0)) le)
    (m1 := m) (t1 := E0) (t2 := E0).
  - apply exec_Sset. constructor.
  - eapply exec_Sseq_1 with (le1 := le') (m1 := m') (t1 := E0) (t2 := E0).
    + exact Execute.
    + constructor.
Qed.

Print Assumptions counted_loop.
Print Assumptions each_invariant.
