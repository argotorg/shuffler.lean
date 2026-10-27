(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Integers Values ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute.
Require Import ClightChoose.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Definition moved_at (xs : list Z) k :=
  if Z.eq_dec (List.nth k xs 0%Z) (Z.of_nat k) then false else true.

Fixpoint last_at (xs : list Z) k : option nat :=
  if moved_at xs k then Some k else
    match k with O => None | S k' => last_at xs k' end.

Fixpoint last_match (test : nat -> bool) positions : option nat :=
  match positions with
  | [::] => None
  | i :: rest =>
      match last_match test rest with
      | Some j => Some j
      | None => if test i then Some i else None
      end
  end.

Definition descending_option xs k :=
  let selected := descending_position xs k in
  if moved_at xs selected then Some selected else None.

Lemma last_atE xs k : last_at xs k =
  if moved_at xs k then Some k else match k with O => None | S k' => last_at xs k' end.
Proof. by case: k. Qed.

Lemma last_match_rcons test positions k :
  last_match test (rcons positions k) =
    if test k then Some k else last_match test positions.
Proof.
elim: positions=> [|i rest IH] /=; first by case: (test k).
rewrite IH; case: (test k)=> //=.
Qed.

Lemma last_at_iota xs k : last_match (moved_at xs) (iota 0 k.+1) = last_at xs k.
Proof.
elim: k=> [|k IH]; first by rewrite /=; case: (moved_at xs 0%N).
rewrite -[k.+2]addn1 iotaD add0n.
change (last_match (moved_at xs) (iota 0 k.+1 ++ [:: k.+1]) = last_at xs k.+1).
rewrite cats1 last_match_rcons IH.
by rewrite /last_at -/last_at; case: (moved_at xs k.+1).
Qed.

Lemma descending_option_last xs k :
  moved_at xs k = false -> descending_option xs k = last_at xs k.
Proof.
elim: k=> [|k IH] Hfixed.
- by rewrite /descending_option /= /last_at Hfixed.
- rewrite /descending_option /= /last_at Hfixed -/last_at.
  case E: (Z.eq_dec (List.nth k xs 0%Z) (Z.of_nat k))=> [Hsame|Hdiff].
  + have Hk : moved_at xs k = false by rewrite /moved_at E.
    exact: IH Hk.
  + have Hk : moved_at xs k = true by rewrite /moved_at E.
    by rewrite Hk last_atE Hk.
Qed.

Section OrdinalArray.
Variable m : nat.
Variable p : 'S_m.+1.
Variable xs : list Z.
Hypothesis Represents : forall i : 'I_m.+1,
  List.nth (val i) xs 0%Z = Z.of_nat (val (p i)).

Lemma moved_at_ordinal (i : 'I_m.+1) : moved_at xs (val i) = (p i != i).
Proof.
rewrite /moved_at Represents.
case Hpi: (p i == i).
- move/eqP: Hpi=> Hsame; rewrite Hsame.
  case E: (Z.eq_dec (Z.of_nat (val i)) (Z.of_nat (val i)))=> [H|H];
    simpl; [reflexivity|contradiction].
- case Decision: (Z.eq_dec (Z.of_nat (val (p i))) (Z.of_nat (val i)))=> [E|E];
    simpl; last reflexivity.
  have Hsame : p i = i by apply: val_inj; exact: Nat2Z.inj E.
  by rewrite Hsame eqxx in Hpi.
Qed.

Lemma last_moved_array positions :
  option_map val (Legacy.Permute.last_moved p positions) =
    last_match (moved_at xs) (map val positions).
Proof.
elim: positions=> [|i rest IH] //=.
rewrite -IH; case: (Legacy.Permute.last_moved p rest)=> [j|] //=.
by rewrite moved_at_ordinal; case: (p i != i).
Qed.

Definition choose_observation :=
  match snd (choose_result xs m) with
  | Out_normal => Some (Z.to_nat (fst (choose_result xs m)))
  | _ => None
  end.

Theorem choose_matches_model :
  choose_observation = option_map val (Legacy.Permute.choose p ord_max).
Proof.
have Hrepr : List.nth m xs 0%Z = Z.of_nat (val (p ord_max)) := Represents ord_max.
have Hmoved : moved_at xs m = (p ord_max != ord_max) := moved_at_ordinal ord_max.
rewrite /choose_observation /Legacy.Permute.choose.
case Htop: (p ord_max == ord_max).
- have Hfixed : moved_at xs m = false by rewrite Hmoved Htop.
  have Hsame : List.nth m xs 0%Z = Z.of_nat m.
    move/eqP: Htop=> Htop; by rewrite Hrepr Htop.
  rewrite /choose_result; destruct (zeq (List.nth m xs 0%Z) (Z.of_nat m)) as [E|E]; last congruence.
  rewrite /= /selection_outcome.
  have Hlast : option_map val (Legacy.Permute.last_moved p (enum 'I_m.+1)) =
      descending_option xs m.
    rewrite last_moved_array val_enum_ord last_at_iota.
    symmetry; exact: descending_option_last Hfixed.
  rewrite Hlast.
  rewrite /descending_option /moved_at.
  destruct (zeq (List.nth (descending_position xs m) xs 0%Z)
    (Z.of_nat (descending_position xs m))) as [Eselected|Eselected];
  destruct (Z.eq_dec (List.nth (descending_position xs m) xs 0%Z)
    (Z.of_nat (descending_position xs m))); try congruence.
  all: try reflexivity.
  by rewrite Nat2Z.id.
- have Hdiff : List.nth m xs 0%Z <> Z.of_nat m.
    move=> E; have Hval : val (p ord_max) = m by apply Nat2Z.inj; rewrite -Hrepr E.
    have Hp : p ord_max = ord_max by apply: val_inj.
    by rewrite Hp eqxx in Htop.
  rewrite /choose_result; destruct (zeq (List.nth m xs 0%Z) (Z.of_nat m)); first congruence.
  by rewrite /= Hrepr Nat2Z.id.
Qed.

Lemma choose_result_range :
  (0 <= fst (choose_result xs m))%Z /\
  (snd (choose_result xs m) = Out_normal \/
   snd (choose_result xs m) = Out_return (Some (Vint Int.zero, Permute.u32))).
Proof.
rewrite /choose_result.
case: (zeq (List.nth m xs 0%Z) (Z.of_nat m))=> E /=.
- split; first exact: Nat2Z.is_nonneg.
  rewrite /selection_outcome; case: zeq=> E'; by [left|right].
- split; first by rewrite (Represents ord_max); exact: Nat2Z.is_nonneg.
  by left.
Qed.

Theorem choose_result_some (position : 'I_m.+1) :
  Legacy.Permute.choose p ord_max = Some position ->
  choose_result xs m = (Z.of_nat (val position), Out_normal).
Proof.
move=> Hchoice.
have H := choose_matches_model.
rewrite Hchoice /= /choose_observation in H.
have [Nonnegative Range] := choose_result_range.
case E: (choose_result xs m)=> [selected outcome].
rewrite E /= in H Nonnegative Range.
case: Range=> -> //= in H *.
have Hnat : Z.to_nat selected = val position by injection H.
have Hz : selected = Z.of_nat (val position).
  rewrite -Hnat; symmetry; exact: Z2Nat.id.
by rewrite Hz.
Qed.

Theorem choose_result_none :
  Legacy.Permute.choose p ord_max = None ->
  snd (choose_result xs m) = Out_return (Some (Vint Int.zero, Permute.u32)).
Proof.
move=> Hchoice.
have H := choose_matches_model.
rewrite Hchoice /= /choose_observation in H.
have [_ [Normal|Return]] := choose_result_range; last exact Return.
by rewrite Normal in H.
Qed.
End OrdinalArray.

Print Assumptions choose_matches_model.
