From Stdlib Require Import Lia PeanoNat.
(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute.

Set Implicit Arguments.
Open Scope group_scope.

Section Cycles.
Variable T : finType.

(* Unlike Mathlib's cycleFactorsFinset, porbits includes singleton orbits.
   This is the candidate Rocq form of arbitrarySwapCount. The equality to
   the Lean support-minus-nontrivial-cycles formula is not part of this spike. *)
Definition arbitrary_cost (p : {perm T}) := Nat.sub #|T| #|porbits p|.

(* MathComp already has the orbit-count change under a transposition.
   It supplies the main fact needed for the arbitrary-swap lower bound. *)
Lemma arbitrary_cost_step (p : {perm T}) a b :
  (arbitrary_cost p <= (arbitrary_cost (exchange p a b)).+1)%coq_nat.
Proof.
have H := porbits_mul_tperm p a b.
cbv zeta in H.
rewrite /arbitrary_cost /exchange.
set before := #|porbits p| in H *.
set after := #|porbits (tperm a b * p)| in H *.
case Hsame: (a \notin porbit p b) in H;
  case Hne: (a != b) in H;
  rewrite /addn /double /= in H; lia.
Qed.
End Cycles.

Print Assumptions arbitrary_cost_step.
