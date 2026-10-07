(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope group_scope.

Section Normalization.
Variable T : finType.
Variable A : eqType.

Definition compatible (s target : T -> A) (p : {perm T}) :=
  forall i, s i = target (p i).

Definition target_of (s : T -> A) (p : {perm T}) := s \o p^-1.

(* Assign destination j to source i while retaining a permutation witness.
   The other changed entry is not yet committed by the greedy pass. *)
Definition set_destination (p : {perm T}) i j := exchange p i (p^-1 j).

Definition fixed_values (s target : T -> A) := [set i | s i == target i].

Definition fix_one (s target : T -> A) (p : {perm T}) i :=
  if i \in fixed_values s target then set_destination p i i else p.

Definition fix_values (s target : T -> A) (p : {perm T}) :=
  foldl (fix_one s target) p (enum T).

Fixpoint first_free (target : T -> A) (value : A) (used : {set T})
    (positions : seq T) : option T :=
  match positions with
  | [::] => None
  | j :: rest =>
      if (j \notin used) && (target j == value) then Some j
      else first_free target value used rest
  end.

(* The enumeration is ascending for ordinal indices. Positions whose value
   is already correct have been reserved before this pass. *)
Fixpoint fill_destinations (s target : T -> A) (positions : seq T)
    (p : {perm T}) (used : {set T}) : option {perm T} :=
  match positions with
  | [::] => Some p
  | i :: rest =>
      if i \in fixed_values s target then
        fill_destinations s target rest p used
      else
        match first_free target (s i) used (enum T) with
        | None => None
        | Some j => fill_destinations s target rest
            (set_destination p i j) (j |: used)
        end
  end.

Definition normalize (s : T -> A) (p : {perm T}) :=
  let target := target_of s p in
  fill_destinations s target (enum T) (fix_values s target p)
    (fixed_values s target).

Definition write_index (f : T -> T) i j :=
  fun x => if x == i then j else f x.

Fixpoint raw_fill (s target : T -> A) (positions : seq T)
    (assignment : T -> T) (used : {set T}) : option (T -> T) :=
  match positions with
  | [::] => Some assignment
  | i :: rest =>
      if i \in fixed_values s target then raw_fill s target rest assignment used
      else
        match first_free target (s i) used (enum T) with
        | None => None
        | Some j => raw_fill s target rest
            (write_index assignment i j) (j |: used)
        end
  end.

Definition raw_normalize (s : T -> A) (p : {perm T}) :=
  let target := target_of s p in
  let good := fixed_values s target in
  raw_fill s target (enum T) (fun i => if i \in good then i else p i) good.
End Normalization.

Inductive SolcResult (A : Type) (n : nat) : Type :=
  | SolcDone : ('I_n -> A) -> 'S_n -> seq nat -> SolcResult A n
  | SolcBlocked : ('I_n -> A) -> 'S_n -> seq nat -> 'I_n -> nat -> SolcResult A n
  | SolcExhausted : SolcResult A n.
Arguments SolcDone {A n}.
Arguments SolcBlocked {A n}.
Arguments SolcExhausted {A n}.

Section Runs.
Variable A : eqType.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.

(* The permutation changes even when the selected values are equal. Such a
   step emits no swap and must not fail the depth check. *)
Fixpoint solc_run (fuel : nat) (s : 'I_m.+1 -> A) (p : 'S_m.+1)
    (trace : seq nat) : SolcResult A m.+1 :=
  if fuel is fuel'.+1 then
    if choose p top is Some pos then
      let p' := exchange p top pos in
      if s top == s pos then solc_run fuel' s p' trace
      else if depth pos <= (8 + 8) then
        solc_run fuel' (swap_stack s pos) p' (trace ++ [:: depth pos])
      else SolcBlocked s p trace pos (depth pos - 16)
    else SolcDone s p trace
  else SolcExhausted.

Definition solc_nonempty s p := solc_run (rank p top).+1 s p [::].
End Runs.

Definition solc_permute (A : eqType) (n : nat)
    (s : 'I_n -> A) (p : 'S_n) : option (SolcResult A n) :=
  match normalize s p with
  | None => None
  | Some q =>
      Some (match n as k return ('I_k -> A) -> 'S_k -> SolcResult A k with
            | 0 => fun s p => SolcDone s p [::]
            | m.+1 => fun s p => solc_nonempty s p
            end s q)
  end.
