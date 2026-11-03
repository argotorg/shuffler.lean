(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Public model contract. Review these definitions, not the proof tactics. *)
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Proofs.
Require Import SolcModel.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Section ModelContract.
Variable A : eqType.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.

Definition values_reachable (s : 'I_m.+1 -> A) (p : 'S_m.+1) : Prop :=
  forall i, (16 < depth i)%N -> s i = target_of s p i.

Definition solc_result_spec (s : 'I_m.+1 -> A) (p : 'S_m.+1)
    (r : SolcResult A m.+1) : Prop :=
  match r with
  | SolcDone result finalp out =>
      finalp = 1 /\ (forall i, result i = target_of s p i) /\
      SwapTrace s result out /\ (size out <= 2 * m.+1)%N
  | SolcBlocked result finalp out pos excess =>
      SwapTrace s result out /\ choose finalp top = Some pos /\
      result top != result pos /\ (16 < depth pos)%N /\
      excess = (depth pos - 16)%N /\ (size out <= 2 * m.+1)%N /\
      (forall i, result (finalp^-1 i) = target_of s p i)
  | SolcExhausted => False
  end.

End ModelContract.
