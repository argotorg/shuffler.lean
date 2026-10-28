(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Utils Syntax ScopeTheory Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation Control FullCFG BodySyntax BodyFrame NoException.
Import ListNotations.
Import ITreeNotations.
Open Scope itree_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma free_with_call_return A (x : A) : exception_free (withCall (Ret x)).
Proof. unfold withCall. rewrite translate_ret. apply exception_free_return. Qed.

Lemma free_with_call_bind A B (t : MCFGtop A) (k : A -> MCFGtop B) :
  exception_free (withCall t) -> (forall x, exception_free (withCall (k x))) ->
  exception_free (withCall (ITree.bind t k)).
Proof.
  intros First Next. unfold withCall. rewrite translate_bind.
  apply exception_free_bind; assumption.
Qed.

Lemma free_abort A (e : CFGEtop void) : exc_of_event e = None ->
  exception_free (@trigger_cast' CFGEtop A e).
Proof.
  intro Safe. unfold trigger_cast'. apply exception_free_bind.
  - apply exception_free_trigger, Safe.
  - intros [].
Qed.

Lemma free_with_call_abort A (e : MCFGEtop void) : exc_of_event (inr1 e) = None ->
  exception_free (withCall (@trigger_cast' MCFGEtop A e)).
Proof.
  intro Safe. unfold withCall, trigger_cast'. rewrite translate_bind.
  apply exception_free_bind.
  - unfold ITree.trigger. rewrite translate_vis.
    constructor. constructor; [exact Safe|intros []].
  - intros [].
Qed.

Lemma free_eou A (c : EOU A) : exception_free (withCall (EOU_to_itree c)).
Proof.
  destruct c; try apply free_with_call_return; apply free_with_call_abort; reflexivity.
Qed.

Lemma free_local_read id : exception_free (lread id).
Proof. apply exception_free_trigger. reflexivity. Qed.

Lemma free_local_write id value : exception_free (lwrite id value).
Proof. apply exception_free_trigger. reflexivity. Qed.

Lemma free_load dt address : exception_free (LLVMEvents.load dt address).
Proof. apply exception_free_trigger. reflexivity. Qed.

Lemma free_store dt address value : exception_free (LLVMEvents.store dt address value).
Proof. apply exception_free_trigger. reflexivity. Qed.

Lemma free_expression e : plain_expression e -> forall top, exception_free (denote_exp' top e).
Proof.
  intro Plain. induction Plain; intro top; unfold denote_exp'; cbn [denote_exp].
  - unfold lookup_id, withCall, lread, ITree.trigger. rewrite translate_vis.
    constructor. constructor; [reflexivity|]. intro x.
    rewrite translate_ret. apply exception_free_return.
  - destruct top; [apply free_eou|apply free_with_call_abort; reflexivity].
  - apply free_with_call_bind; [apply IHPlain1|]. intro a'.
    apply free_with_call_bind; [apply IHPlain2|]. intro b'. apply free_eou.
  - apply free_with_call_bind; [apply IHPlain1|]. intro a'.
    apply free_with_call_bind; [apply IHPlain2|]. intro b'. apply free_eou.
  - apply free_with_call_bind; [apply IHPlain|]. intro a'. cbn [convert]. apply free_eou.
  - apply free_with_call_bind; [apply IHPlain1|]. intro p.
    cbn [map_monad]. apply free_with_call_bind.
    + apply free_with_call_bind; [apply IHPlain2|]. intro i.
      apply free_with_call_bind; [apply free_with_call_return|].
      intro values. apply free_with_call_return.
    + intro indices. apply free_eou.
Qed.

Lemma free_instruction i : plain_instruction i -> forall varargs, exception_free (denote_instr i varargs).
Proof.
  intro Plain. destruct Plain; intro varargs; unfold denote_instr.
  - apply exception_free_bind; [apply free_expression, H|]. intro value.
    apply exception_free_bind; [apply free_local_write|]. intro u. apply exception_free_return.
  - apply exception_free_bind; [apply free_expression, H|]. intro pointer_value.
    apply exception_free_bind; [apply free_load|]. intro value. apply free_local_write.
  - apply exception_free_bind; [apply free_expression, H|]. intro v.
    apply exception_free_bind; [apply free_expression, H0|]. intro p.
    apply exception_free_bind; [|intro u; apply exception_free_return].
    destruct p; try apply free_store.
    destruct db; try apply free_store. apply free_abort. reflexivity.
Qed.

Lemma free_terminator t : plain_terminator t -> exception_free (denote_terminator t).
Proof.
  intro Plain. destruct Plain; unfold denote_terminator.
  - apply exception_free_bind; [apply free_expression, H|]. intro returned. apply exception_free_return.
  - apply exception_free_bind; [apply free_expression, H|]. intro v.
    repeat match goal with |- exception_free (match ?value with _ => _ end) => destruct value end;
      try apply exception_free_return; try solve [apply free_abort; reflexivity].
    destruct sz; try solve [apply free_abort; reflexivity].
    destruct (VellvmIntegers.equ x VellvmIntegers.one); apply exception_free_return.
  - apply exception_free_return.
Qed.

Lemma free_map A B (f : A -> CFGtop B) xs :
  (forall x, In x xs -> exception_free (f x)) -> exception_free (map_monad f xs).
Proof.
  intro Free. induction xs as [|x xs IH]; cbn [map_monad].
  - apply exception_free_return.
  - apply exception_free_bind; [apply Free; now left|]. intro y.
    apply exception_free_bind; [apply IH; intros; apply Free; now right|].
    intro ys. apply exception_free_return.
Qed.

Lemma free_code code varargs : Forall plain_instruction code -> exception_free (denote_code code varargs).
Proof.
  intro Plain. unfold denote_code. induction Plain; cbn [loop_monad].
  - apply exception_free_return.
  - apply exception_free_bind; [apply free_instruction, H|]. intros; exact IHPlain.
Qed.

Lemma free_phi from p : plain_phi p -> exception_free (denote_phi from p).
Proof.
  intro Plain. destruct Plain. unfold denote_phi.
  destruct (assoc from arms) as [expression|] eqn:Found.
  - apply exception_free_bind; [apply free_expression; exact (@plain_assoc from arms expression H Found)|].
    intro returned. apply exception_free_return.
  - apply free_abort. reflexivity.
Qed.

Lemma free_phis from phis : Forall plain_phi phis -> exception_free (denote_phis from phis).
Proof.
  intro Plain. unfold denote_phis. apply exception_free_bind.
  - apply free_map. intros p Member. apply free_phi. eapply Forall_forall; eassumption.
  - intro values. apply exception_free_bind.
    + apply free_map. intros [id value] Member. apply free_local_write.
    + intro u. apply exception_free_return.
Qed.

Lemma free_block b : plain_block b -> forall from varargs, exception_free (denote_block b from varargs).
Proof.
  intros [Phis Code Term] from varargs. unfold denote_block.
  apply exception_free_bind; [apply free_phis, Phis|]. intro u.
  apply exception_free_bind; [apply free_code, Code|]. intro v. apply free_terminator, Term.
Qed.

Lemma full_ocfg_exception_free varargs start :
  exception_free (denote_ocfg (blks FullCFG.body) varargs start).
Proof.
  unfold denote_ocfg, denote_ocfg_map. apply exception_free_iter.
  intros [from label]. rewrite ocfg_map_find_block.
  destruct (find_block (blks FullCFG.body) label) as [block|] eqn:Found.
  - apply exception_free_bind.
    + apply free_block. eapply body_block_plain; eassumption.
    + intros [target|value]; apply exception_free_return.
  - apply exception_free_return.
Qed.

Theorem full_body_exception_free varargs : exception_free (denote_cfg FullCFG.body varargs).
Proof.
  unfold denote_cfg, denote_cfg_map. apply exception_free_bind.
  - apply full_ocfg_exception_free.
  - intros [missing|value]; [apply free_abort; reflexivity|apply exception_free_return].
Qed.
