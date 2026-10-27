(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute.
Require Import ClightMemory ClightScalar.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Definition words {n} (f : 'I_n -> nat) : list Z :=
  [seq Z.of_nat (f i) | i <- enum 'I_n].

Definition update_value {n} (f : 'I_n -> nat) i value :=
  fun x => if x == i then value else f x.

Lemma nth_compat (A : Type) (xs : list A) k d : List.nth k xs d = nth d xs k.
Proof. by elim: xs k=> [|x xs IH] [|k] //=; rewrite IH. Qed.

Lemma words_length n (f : 'I_n -> nat) : List.length (words f) = n.
Proof. change (size (words f) = n). by rewrite /words size_map size_enum_ord. Qed.

Lemma words_nth n (f : 'I_n -> nat) (i : 'I_n) :
  List.nth (val i) (words f) 0%Z = Z.of_nat (f i).
Proof.
rewrite nth_compat.
by rewrite /words (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma words_nth_error n (f : 'I_n -> nat) (i : 'I_n) :
  List.nth_error (words f) (val i) = Some (Z.of_nat (f i)).
Proof.
rewrite -words_nth; apply List.nth_error_nth'.
rewrite words_length; exact (elimT ltP (ltn_ord i)).
Qed.

Lemma words_update n (f : 'I_n -> nat) (i : 'I_n) value :
  replace_nth (val i) (Z.of_nat value) (words f) = words (update_value f i value).
Proof.
apply List.nth_error_ext=> k.
case K: (k < n)%N.
- pose x : 'I_n := Ordinal K.
  change (List.nth_error (replace_nth (val i) (Z.of_nat value) (words f)) (val x) =
    List.nth_error (words (update_value f i value)) (val x)).
  rewrite words_nth_error /update_value.
  case E: (x == i).
  + move/eqP: E=> ->; apply nth_error_replace_same.
    rewrite words_length; exact (elimT ltP (ltn_ord i)).
  + rewrite nth_error_replace_other; first exact: words_nth_error.
    move=> H; have Hxi : x = i by apply: val_inj; symmetry.
    by rewrite Hxi eqxx in E.
- have K' : (n <= k)%coq_nat by apply/leP; rewrite leqNgt K.
  have L : List.nth_error (replace_nth (val i) (Z.of_nat value) (words f)) k = None.
    apply List.nth_error_None; by rewrite length_replace_nth words_length.
  have R : List.nth_error (words (update_value f i value)) k = None.
    apply List.nth_error_None; by rewrite words_length.
  by rewrite L R.
Qed.

Lemma words_swap n (f : 'I_n -> nat) (a b : 'I_n) :
  replace_nth (val b) (Z.of_nat (f a))
    (replace_nth (val a) (Z.of_nat (f b)) (words f)) =
  words (fun i => f (tperm a b i)).
Proof.
rewrite !words_update /words; apply: eq_map=> i; rewrite /update_value.
case Eib: (i == b).
- by move/eqP: Eib=> ->; rewrite tpermR.
case Eia: (i == a).
- by move/eqP: Eia=> ->; rewrite tpermL.
- rewrite tpermD //; by rewrite eq_sym ?Eia ?Eib.
Qed.

Lemma words_ext n (f g : 'I_n -> nat) :
  (forall i, f i = g i) -> words f = words g.
Proof. move=> H; rewrite /words; apply: eq_map=> i; by rewrite H. Qed.

Lemma words_uint n (f : 'I_n -> nat) :
  (forall i, uint (Z.of_nat (f i))) -> List.Forall uint (words f).
Proof.
move=> H; apply List.Forall_forall=> z.
rewrite /words=> /List.in_map_iff[i [<- _]]; exact: H.
Qed.

Lemma permutation_words_uint n (p : 'S_n) :
  (n <= 1024)%coq_nat -> List.Forall uint (words (fun i => val (p i))).
Proof.
move=> Hn; apply words_uint=> i.
have Hi : (val (p i) < n)%coq_nat := (elimT ltP (ltn_ord (p i))).
unfold uint; change (0 <= Z.of_nat (val (p i)) <= 4294967295)%Z; lia.
Qed.

Lemma words_stack_swap m (s : 'I_m.+1 -> nat) pos :
  replace_nth m (Z.of_nat (s pos))
    (replace_nth (val pos) (Z.of_nat (s ord_max)) (words s)) =
  words (Legacy.Permute.swap_stack s pos).
Proof.
change (replace_nth (val (ord_max : 'I_m.+1)) (Z.of_nat (s pos))
  (replace_nth (val pos) (Z.of_nat (s ord_max)) (words s)) =
  words (Legacy.Permute.swap_stack s pos)).
rewrite words_swap; apply: words_ext=> i.
by rewrite /Legacy.Permute.swap_stack /comp tpermC.
Qed.

Lemma words_permutation_swap m (p : 'S_m.+1) pos :
  replace_nth m (Z.of_nat (val (p pos)))
    (replace_nth (val pos) (Z.of_nat (val (p ord_max)))
      (words (fun i => val (p i)))) =
  words (fun i => val (Legacy.Permute.exchange p ord_max pos i)).
Proof.
change (replace_nth (val (ord_max : 'I_m.+1)) (Z.of_nat (val (p pos)))
  (replace_nth (val pos) (Z.of_nat (val (p ord_max)))
    (words (fun i => val (p i)))) =
  words (fun i => val (Legacy.Permute.exchange p ord_max pos i))).
rewrite (@words_swap m.+1 (fun i => val (p i)) pos ord_max).
apply: words_ext=> i.
by rewrite Legacy.Permute.exchangeE tpermC.
Qed.

Print Assumptions words_swap.
