(* SPDX-License-Identifier: GPL-3.0-or-later *)
From ITree Require Import ITree ITreeFacts.

(* A finite sequence of silent steps can certify termination. Any visible
   event, including UB, failure, or an external call, makes this check fail. *)
Fixpoint pure_result {E R} (fuel : nat) (t : itree E R) : option R :=
  match fuel with
  | O => None
  | S n => match observe t with
           | RetF r => Some r
           | TauF t' => pure_result n t'
           | VisF _ _ => None
           end
  end.

Lemma pure_result_sound {E R} fuel (t : itree E R) r :
  pure_result fuel t = Some r -> eutt eq t (Ret r).
Proof.
  revert t; induction fuel as [|n IH]; intros t H; [discriminate |].
  cbn [pure_result] in H.
  destruct (observe t) eqn:Ht.
  - inversion H; subst.
    rewrite (itree_eta t), Ht; reflexivity.
  - rewrite (itree_eta t), Ht; cbn.
    rewrite tau_eutt. exact (IH _ H).
  - discriminate.
Qed.
