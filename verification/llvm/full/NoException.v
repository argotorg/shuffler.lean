(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String Morphisms.
From Paco Require Import paco.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Utils Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation Control.
Import ITreeNotations.
Open Scope itree_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Inductive exception_freeF {A} (P : CFGtop A -> Prop) : itree' CFGEtop A -> Prop :=
| exception_free_ret x : exception_freeF P (RetF x)
| exception_free_tau u : P u -> exception_freeF P (TauF u)
| exception_free_vis X (e : CFGEtop X) k :
    exc_of_event e = None -> (forall x, P (k x)) -> exception_freeF P (VisF e k).

CoInductive exception_free {A} (t : CFGtop A) : Prop :=
| exception_free_step : exception_freeF exception_free (observe t) -> exception_free t.

Lemma run_exc_unfold A (t : CFGtop A) :
  eq_itree eq (run_exc t)
    (match observe t with
     | RetF x => Ret (inr x)
     | TauF u => Tau (run_exc u)
     | VisF _ e k =>
         match exc_of_event e with
         | Some x => Ret (inl x)
         | None => Vis e (fun x => Tau (run_exc (k x)))
         end
     end).
Proof.
  unfold run_exc. rewrite unfold_iter.
  desobs t ot; cbn; auto.
  - rewrite Eqit.bind_ret_l; reflexivity.
  - rewrite Eqit.bind_ret_l; reflexivity.
  - destruct (exc_of_event e); rewrite ?Eqit.bind_ret_l; [reflexivity|].
    rewrite bind_vis. apply eqit_Vis. intro x.
    rewrite Eqit.bind_ret_l; reflexivity.
Qed.

Lemma exception_free_view A (t : CFGtop A) : exception_free t ->
  match observe t with
  | RetF _ => True
  | TauF u => exception_free u
  | VisF _ e k => exc_of_event e = None /\ forall x, exception_free (k x)
  end.
Proof. intros [Free]. destruct Free; cbn; auto. Qed.

Lemma exception_free_eqit A (t u : CFGtop A) :
  eq_itree eq t u -> exception_free t -> exception_free u.
Proof.
  revert t u. cofix CIH. intros t u Equal Free. constructor.
  pose proof (@exception_free_view A t Free) as View.
  punfold Equal. red in Equal.
  destruct Equal; cbn in View; try discriminate.
  - constructor.
  - constructor. pclearbot. eapply CIH; eassumption.
  - destruct View as [Event Next]. constructor; [exact Event|].
    intro x. specialize (REL x). pclearbot. eapply CIH; [exact REL|apply Next].
Qed.

#[export] Instance exception_free_proper A :
  Proper (eq_itree eq ==> iff) (@exception_free A).
Proof.
  intros t u Equal. split; intro Free.
  - eapply exception_free_eqit; eassumption.
  - eapply exception_free_eqit; [symmetry; exact Equal|exact Free].
Qed.

Theorem run_exc_free A (t : CFGtop A) : exception_free t ->
  eutt eq (run_exc t) (ITree.map (@inr exc A) t).
Proof.
  revert t. einit. ecofix CIH. intros t Free.
  rewrite run_exc_unfold.
  rewrite (itree_eta t) at 2.
  destruct Free as [Free]. destruct Free; cbn.
  - rewrite map_ret. estep.
  - rewrite map_tau. estep.
  - rewrite H. unfold ITree.map at 1. rewrite bind_vis.
    estep. intro x. rewrite tau_eutt. ebase.
Qed.

Corollary runs_run_exc A (t : CFGtop A) s final value :
  exception_free t -> runs t s final value ->
  runs (run_exc t) s final (inr value).
Proof.
  intros Free Run. eapply runs_eutt; [apply run_exc_free, Free|].
  unfold ITree.map. eapply runs_bind; [exact Run|apply runs_ret].
Qed.

Lemma exception_free_return A (x : A) : exception_free (Ret x).
Proof. constructor; constructor. Qed.

Lemma exception_free_trigger X (e : CFGEtop X) : exc_of_event e = None ->
  exception_free (trigger e).
Proof.
  intro Safe. constructor. constructor; [exact Safe|].
  intro x. apply exception_free_return.
Qed.

Lemma exception_free_bind A B (t : CFGtop A) (k : A -> CFGtop B) :
  exception_free t -> (forall x, exception_free (k x)) -> exception_free (ITree.bind t k).
Proof.
  revert t. cofix CIH. intros t Free Next. constructor.
  rewrite observe_bind. destruct Free as [Free]. destruct Free; cbn.
  - destruct (Next x) as [Result]. exact Result.
  - constructor. apply CIH; assumption.
  - constructor; [exact H|]. intro x. apply CIH; [apply H0|exact Next].
Qed.

Lemma exception_free_coind A (R : CFGtop A -> Prop) :
  (forall t, R t -> exception_freeF (fun u => exception_free u \/ R u) (observe t)) ->
  forall t, R t -> exception_free t.
Proof.
  intro Step. cofix CIH. intros t Related. constructor.
  destruct (Step t Related).
  - constructor.
  - constructor. destruct H; [exact H|apply CIH, H].
  - constructor; [exact H|]. intro x. destruct (H0 x); [exact H1|apply CIH, H1].
Qed.

Lemma exception_free_iter I A (body : I -> CFGtop (I + A)) :
  (forall i, exception_free (body i)) -> forall i, exception_free (ITree.iter body i).
Proof.
  intro Body.
  pose (next := fun r : I + A => match r with
    | inl i => Tau (ITree.iter body i) | inr x => Ret x end).
  pose (R := fun u : CFGtop A =>
    (exists i, u = ITree.iter body i) \/
    (exists t, exception_free t /\ u = ITree.bind t next)).
  assert (Bind : forall t, exception_free t ->
      exception_freeF (fun u => exception_free u \/ R u) (observe (ITree.bind t next))).
  { intros t [Free]. rewrite observe_bind. destruct Free; cbn.
    - destruct x as [i|x]; cbn [next].
      + constructor. right. left. exists i; reflexivity.
      + constructor.
    - constructor. right. right. exists u; split; [exact H|reflexivity].
    - constructor; [exact H|]. intro x. right. right.
      exists (k x); split; [apply H0|reflexivity]. }
  intro i. apply (@exception_free_coind A R).
  - intros u [[j Same]|[t [Free Same]]]; subst u.
    + change (exception_freeF (fun u => exception_free u \/ R u)
        (observe (ITree.bind (body j) next))). apply Bind, Body.
    + apply Bind, Free.
  - left. exists i; reflexivity.
Qed.

Lemma exception_free_rejects_raise A value :
  ~ exception_free (raiseLLVM value : CFGtop A).
Proof.
  intro Free. pose proof (@exception_free_view A (raiseLLVM value) Free) as View.
  cbn in View. destruct View as [Impossible _]. discriminate.
Qed.

Print Assumptions run_exc_free.
Print Assumptions exception_free_eqit.
Print Assumptions exception_free_iter.
