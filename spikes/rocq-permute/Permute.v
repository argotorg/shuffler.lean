(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope group_scope.

(* A spike of the current Lean algorithm, including its equal-value behavior.
   MathComp composes permutations in the opposite order to Mathlib. *)

Section Permutations.
Variable T : finType.
Implicit Types p : {perm T}.

Definition moved p := [set i | p i != i].
Definition exchange p a b := (tperm a b * p)%g.

Fixpoint last_moved p (xs : seq T) : option T :=
  if xs is x :: rest then
    if last_moved p rest is Some y then Some y
    else if p x != x then Some x else None
  else None.

Definition choose p top :=
  if p top != top then Some (p top) else last_moved p (enum T).

Definition rank p top :=
  (2 * #|moved p :\ top| + (if p top == top then 1 else 0))%N.

Lemma exchangeE p a b i : exchange p a b i = p (tperm a b i).
Proof. exact: permM. Qed.

Lemma apply_exchange (A : Type) (s : T -> A) p a b i :
  (s \o tperm a b) ((exchange p a b)^-1 i) = s (p^-1 i).
Proof. by rewrite /exchange invMg tpermV permM /comp tpermK. Qed.

Lemma last_moved_some p xs x :
  last_moved p xs = Some x -> x \in xs /\ p x != x.
Proof.
elim: xs x => [|a xs IH] x //=.
case E: (last_moved p xs) => [y|].
- move=> [<-]; have [Hy Hmove] := IH y E.
  by split; [rewrite in_cons Hy orbT | exact: Hmove].
- case H: (p a != a) => // -[<-].
  by split; [rewrite in_cons eqxx | exact: H].
Qed.

Lemma last_moved_none p xs :
  last_moved p xs = None -> forall x, x \in xs -> p x = x.
Proof.
elim: xs => [|a xs IH] //=.
case E: (last_moved p xs) => [y|] //.
case H: (p a != a) => // _ x.
rewrite in_cons => /orP[/eqP ->|Hx]; first by move/negPn/eqP: H.
exact: IH E x Hx.
Qed.

Lemma choose_none p top : choose p top = None -> p = 1.
Proof.
rewrite /choose; case: ifP => // _ H.
apply/permP => i; rewrite perm1.
exact (last_moved_none H (x := i) ltac:(by rewrite mem_enum)).
Qed.

Lemma choose_some p top pos : choose p top = Some pos ->
  pos != top /\ p pos != pos.
Proof.
rewrite /choose; case: ifP => H.
- move=> [<-]; split=> //.
  by rewrite (inj_eq perm_inj).
- move/last_moved_some=> [_ Hpos]; split=> //.
  apply/eqP => E; subst pos.
  by rewrite H in Hpos.
Qed.
End Permutations.

Inductive Result (A : Type) (n : nat) : Type :=
  | Done : ('I_n -> A) -> seq nat -> Result A n
  | Blocked : nat -> Result A n
  | Exhausted : Result A n.
Arguments Done {A n}.
Arguments Blocked {A n}.
Arguments Exhausted {A n}.

Section Nonempty.
Variable A : Type.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.
Definition depth (pos : 'I_m.+1) := (m - val pos)%N.
Definition swap_stack (s : 'I_m.+1 -> A) pos := s \o tperm top pos.

Fixpoint run (fuel : nat) (s : 'I_m.+1 -> A) (p : 'S_m.+1)
    (trace : seq nat) : Result A m.+1 :=
  if fuel is fuel'.+1 then
    if choose p top is Some pos then
      if depth pos <= 16 then
        run fuel' (swap_stack s pos) (exchange p top pos)
          (trace ++ [:: depth pos])
      else Blocked (depth pos - 16)
    else Done s trace
  else Exhausted.

(* The finite fuel makes the spike executable before the termination proof.
   The proof below must show that this bound cannot be exhausted. *)
Definition permute_nonempty s p := run (rank p top).+1 s p [::].
End Nonempty.

Definition permute (A : Type) (n : nat) :
    ('I_n -> A) -> 'S_n -> Result A n :=
  match n as k return ('I_k -> A) -> 'S_k -> Result A k with
  | 0 => fun s _ => Done s [::]
  | m.+1 => fun s p => permute_nonempty s p
  end.

Inductive Summary (A : Type) : Type :=
  | Success : seq A -> seq nat -> Summary A
  | Failure : nat -> Summary A
  | Timeout : Summary A.
Arguments Success {A}.
Arguments Failure {A}.
Arguments Timeout {A}.

Definition summary A n (r : Result A n) : Summary A :=
  match r with
  | Done s trace => Success [seq s i | i <- enum 'I_n] trace
  | Blocked excess => Failure excess
  | Exhausted => Timeout
  end.
