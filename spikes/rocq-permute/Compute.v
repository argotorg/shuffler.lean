(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute.
Set Implicit Arguments.
Open Scope group_scope.

(* Use library equations before reduction. MathComp locks its abstract
   definitions, so vm_compute alone does not execute permutations. *)
Lemma rank_enum (T : finType) (p : {perm T}) top :
 rank p top = (2 * count (fun i => (i != top) && (p i != i)) (enum T) +
 (if p top == top then 1 else 0))%N.
Proof.
rewrite /rank cardE /enum_mem -enumT -size_filter.
rewrite filter_predT. congr (_ * _ + _)%N. congr (size _). apply: eq_filter=> i.
by rewrite !inE.
Qed.

Lemma tperm_eval (T : finType) (a b x : T) :
 tperm a b x = if x == a then b else if x == b then a else x.
Proof.
case: eqP=> [->|Hxa]; first by rewrite tpermL.
case: eqP=> [->|Hxb]; first by rewrite tpermR.
by rewrite tpermD // eq_sym; apply/eqP.
Qed.

Ltac evaluate_perm :=
  rewrite /permute /permute_nonempty rank_enum;
  rewrite /run /choose /last_moved /exchange /swap_stack /depth /summary /comp;
  rewrite !enum_ordSl ?enum_ord0;
  repeat (progress (rewrite ?perm1 ?permM ?tperm_eval /= /bump));
  by vm_compute.
