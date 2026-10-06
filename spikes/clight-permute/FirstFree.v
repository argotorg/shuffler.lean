(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
Require Import SolcModel ModelProofs.

Set Implicit Arguments.
Unset Strict Implicit.

(* The model searches in sequence order. No earlier matching entry can
   precede the returned entry. *)
Lemma first_free_index (T : finType) (A : eqType)
    (target : T -> A) value used positions q :
  first_free target value used positions = Some q ->
  forall x, x \notin used -> target x = value ->
    index q positions <= index x positions.
Proof.
elim: positions=> [|head rest IH] //=.
case E: ((head \notin used) && (target head == value)).
- move=> [<-] x Xfree Xvalue. by rewrite eqxx.
- move=> Found x Xfree Xvalue.
  have [_ [Qfree Qvalue]] := first_free_some Found.
  have Qhead : (q == head) = false.
  { apply/negP=> /eqP H. subst q. by rewrite Qfree Qvalue eqxx in E. }
  have Xhead : (x == head) = false.
  { apply/negP=> /eqP H. subst x. by rewrite Xfree Xvalue eqxx in E. }
  rewrite (eq_sym head q) (eq_sym head x) Qhead Xhead ltnS. exact: IH Found x Xfree Xvalue.
Qed.

Lemma first_free_minimum n (A : eqType) (target : 'I_n -> A)
    value used q :
  first_free target value used (enum 'I_n) = Some q ->
  forall x, (val x < val q)%coq_nat ->
    (x \in used) \/ target x <> value.
Proof.
move=> Found x Before.
case Used: (x \in used); first by left.
right=> Same.
have Free : x \notin used by rewrite Used.
have Bound := first_free_index Found Free Same.
rewrite !index_enum_ord in Bound.
have Before' : (val x < val q)%N := introT ltP Before.
by move: Before'; rewrite ltnNge Bound.
Qed.

Print Assumptions first_free_minimum.
