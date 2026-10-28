(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Morphisms.
From ExtLib Require Import Core.RelDec.
From ITree Require Import ITree ITreeFacts Props.HasPost Events.State Events.StateFacts.
From Vellvm Require Import Utils Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Equational EOU Operations
  Interfaces.Memory Implementations.Memory Handlers.Memory Handlers.Local Handlers.Stack
  Handlers.Intrinsics.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG BodySyntax.
Import ListNotations.
Import ITreeNotations.
Open Scope itree_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* Retain equality of both return values in the invariant. The generic
   HasPost bind rule first derives this equality with an upstream axiom. *)
Definition strong_post {E A} (t : itree E A) (Q : A -> Prop) :=
  eutt (fun x y => x = y /\ Q x) t t.

#[local] Instance strong_post_eutt {E A} :
  Proper (eutt eq ==> eq ==> iff) (@strong_post E A).
Proof.
  intros t u Equal Q Q' Same; subst Q'. unfold strong_post.
  split; intro Post; [rewrite <- Equal|rewrite Equal]; exact Post.
Qed.

Lemma strong_post_ret E A (x : A) Q : Q x -> @strong_post E A (Ret x) Q.
Proof. intro Post. apply eutt_Ret. split; [reflexivity|exact Post]. Qed.

Lemma strong_post_weaken E A (t : itree E A) P Q :
  strong_post t P -> (forall x, P x -> Q x) -> strong_post t Q.
Proof.
  intros Post Weaken. eapply eqit_mon; try exact Post; try tauto.
  intros x y [Same Property]. split; [exact Same|apply Weaken, Property].
Qed.

Lemma strong_post_bind E A B (t : itree E A) (k : A -> itree E B) P Q :
  strong_post t P -> (forall x, P x -> strong_post (k x) Q) ->
  strong_post (ITree.bind t k) Q.
Proof.
  intros First Next. eapply eutt_clo_bind with (UU := fun x y => x = y /\ P x).
  - exact First.
  - intros x y [<- Post]. apply Next, Post.
Qed.

Lemma strong_post_bind_weak E A B (t : itree E A) (k : A -> itree E B) Q :
  (forall x, strong_post (k x) Q) -> strong_post (ITree.bind t k) Q.
Proof. intro Next. apply eutt_eq_bind. exact Next. Qed.

Lemma strong_post_abort (E : Type -> Type) A (e : E void) Q : strong_post (@trigger_cast' E A e) Q.
Proof. unfold trigger_cast'. apply strong_post_bind_weak. intros []. Qed.

Lemma strong_post_error E A `{FailureE -< E} message Q :
  strong_post (@raise E A _ message) Q.
Proof. apply strong_post_abort. Qed.

Lemma strong_post_ub E A `{UBE -< E} message Q :
  strong_post (@raiseUB E _ A message) Q.
Proof. apply strong_post_abort. Qed.

Lemma strong_post_oom E A `{OOME -< E} message Q :
  strong_post (@raiseOOM E _ A message) Q.
Proof. apply strong_post_abort. Qed.

Definition memory_structure (m : Impl.State) :=
  (Impl.Memory_stack_frame_stack (Impl.state_memory_stack m),
   Impl.Memory_stack_heap (Impl.state_memory_stack m), Impl.state_provenance m).

Definition structural_frame (s : FusedS) :=
  (memory_structure (fst s), snd (fst (snd s)), snd (snd s)).

Fixpoint memory_framed {A} (c : memM A) (s : Impl.State) : Prop :=
  match c with
  | Mret _ | Moom _ | Mub _ | Merr _ => True
  | Mget k => memory_framed (k s) s
  | Mput s' k => memory_structure s' = memory_structure s /\ memory_framed (k tt) s'
  | Mchoose _ _ => False
  end.

Lemma memory_framed_bind A B (c : memM A) (k : A -> memM B) s :
  memory_framed c s -> (forall x s', memory_framed (k x) s') ->
  memory_framed (memS_bind c k) s.
Proof.
  revert s. induction c; intros initial Frame Next; cbn [memS_bind memory_framed] in *;
    try exact I; try contradiction.
  - apply Next.
  - apply H; assumption.
  - destruct Frame as [Same Rest]. split; [exact Same|]. apply H; assumption.
Qed.

Lemma memory_framed_sound A (c : memM A) s : memory_framed c s ->
  strong_post (run_memory c s) (fun '(final, _) => memory_structure final = memory_structure s).
Proof.
  revert s. induction c; intros initial Frame; cbn [memory_framed] in Frame;
    unfold run_memory; cbn [Handler.memM_interp]; try contradiction.
  - apply strong_post_ret. reflexivity.
  - apply strong_post_oom.
  - apply strong_post_ub.
  - apply strong_post_error.
  - apply H, Frame.
  - destruct Frame as [Same Rest]. eapply strong_post_weaken; [apply H, Rest|].
    intros [final value] Equal. simpl in *. exact (eq_trans Equal Same).
Qed.

Lemma memory_framed_lift A (c : EOU A) s : memory_framed (Interfaces.Memory.lift c) s.
Proof. destruct c; exact I. Qed.

Lemma memory_framed_read_byte p s : memory_framed (Impl.Read_byte p) s.
Proof.
  destruct p as [address provenance]. unfold Impl.Read_byte, Impl.read_byte_raw. cbn -[access_allowed].
  destruct (Impl.read_byte_raw_mem (Impl.Memory_stack_memory (Impl.state_memory_stack s)) (address))
    as [[byte aid]|]; [|exact I].
  cbn -[access_allowed]. destruct (access_allowed provenance aid); exact I.
Qed.

Lemma memory_framed_write_byte p byte s : memory_framed (Impl.Write_byte p byte) s.
Proof.
  destruct p as [address provenance]. unfold Impl.Write_byte, Impl.read_byte_raw. cbn -[access_allowed].
  destruct (Impl.read_byte_raw_mem (Impl.Memory_stack_memory (Impl.state_memory_stack s)) (address))
    as [[old aid]|]; [|exact I].
  cbn -[access_allowed]. destruct (access_allowed provenance aid); [|exact I].
  unfold Impl.set_byte_raw, Impl.get_mem, Impl.upd_mem, Impl.app_mem.
  destruct s as [[data frames heap] next_provenance]. cbn. split; reflexivity.
Qed.

Lemma memory_framed_map_acc A B (f : A -> memM B) xs s :
  (forall x s', memory_framed (f x) s') -> memory_framed (map_monad_acc f xs) s.
Proof.
  intro Frame. unfold map_monad_acc. generalize (@nil B) at 2.
  revert s. induction xs as [|x xs IH]; intros s acc; [exact I|].
  cbn. apply memory_framed_bind; [apply Frame|]. intros y s'. apply IH.
Qed.

Lemma memory_framed_loop A B (f : A -> memM B) xs s :
  (forall x s', memory_framed (f x) s') -> memory_framed (loop_monad f xs) s.
Proof.
  intro Frame. revert s. induction xs as [|x xs IH]; intro s; [exact I|].
  cbn. apply memory_framed_bind; [apply Frame|]. intros y s'. apply IH.
Qed.

Lemma memory_framed_load dt p s : memory_framed (Impl.read_dvalue dt p) s.
Proof.
  unfold Impl.read_dvalue. apply memory_framed_bind; [|intros; apply memory_framed_lift].
  unfold Impl.read_bytes. apply memory_framed_bind; [apply memory_framed_lift|].
  intros ptrs state. apply memory_framed_map_acc. apply memory_framed_read_byte.
Qed.

Lemma memory_framed_store dt p value s : memory_framed (Impl.write_dvalue p dt value) s.
Proof.
  unfold Impl.write_dvalue. apply memory_framed_bind; [apply memory_framed_lift|].
  intros data state. unfold Impl.write_bytes.
  apply memory_framed_bind; [apply memory_framed_lift|].
  intros ptrs state'. apply memory_framed_loop. intros [ptr byte] state''.
  apply memory_framed_write_byte.
Qed.

Definition framed {A} (t : CFGtop A) := forall ctx s,
  strong_post (run ctx t s) (fun '(final, _) => structural_frame final = structural_frame s).

Lemma framed_ret A (x : A) : framed (Ret x).
Proof. intros ctx s. rewrite (runs_ret A s x ctx). apply strong_post_ret. reflexivity. Qed.

Lemma framed_bind A B (t : CFGtop A) (k : A -> CFGtop B) :
  framed t -> (forall x, framed (k x)) -> framed (ITree.bind t k).
Proof.
  intros First Next ctx s. rewrite run_bind.
  eapply strong_post_bind; [apply First|]. intros [middle x] Equal.
  eapply strong_post_weaken; [apply Next|]. intros [final y] Last. simpl in *.
  exact (eq_trans Last Equal).
Qed.

Lemma framed_eutt A (t u : CFGtop A) : eutt eq t u -> framed u -> framed t.
Proof. intros Equal Frame ctx s. rewrite Equal. apply Frame. Qed.

Lemma framed_with_call_bind A B (t : MCFGtop A) (k : A -> MCFGtop B) :
  framed (withCall t) -> (forall x, framed (withCall (k x))) ->
  framed (withCall (ITree.bind t k)).
Proof.
  intros First Next. eapply framed_eutt.
  - unfold withCall. rewrite translate_bind. reflexivity.
  - apply framed_bind; assumption.
Qed.

Lemma framed_with_call_ret A (x : A) : framed (withCall (Ret x)).
Proof. eapply framed_eutt; [unfold withCall; rewrite translate_ret; reflexivity|apply framed_ret]. Qed.

Lemma framed_abort A (e : CFGEtop void) : framed (@trigger_cast' CFGEtop A e).
Proof.
  intros ctx s. unfold trigger_cast'. rewrite run_bind. apply strong_post_bind_weak. intros [middle []].
Qed.

Lemma framed_with_call_abort A (e : MCFGEtop void) :
  framed (withCall (@trigger_cast' MCFGEtop A e)).
Proof.
  eapply framed_eutt; [unfold withCall, trigger_cast'; rewrite translate_bind; reflexivity|].
  intros ctx s. rewrite run_bind. apply strong_post_bind_weak. intros [middle []].
Qed.

Lemma framed_eou A (c : EOU A) : framed (withCall (EOU_to_itree c)).
Proof. destruct c; try apply framed_with_call_ret; apply framed_with_call_abort. Qed.

Lemma framed_event X (e : MCFGEtop X) :
  eutt eq (interp_intrinsics (trigger e)) (trigger e) ->
  (forall s, strong_post (interp_vellvm_h e s)
    (fun '(final, _) => structural_frame final = structural_frame s)) ->
  framed (trigger (inr1 e)).
Proof.
  intros Intrinsic Step ctx s. unfold run, interp_mcfg, interp_intrinsics.
  rewrite interp_mrec_as_interp, interp_trigger. cbn [mrecursive].
  unfold interp_intrinsics in Intrinsic. rewrite Intrinsic, interp_state_trigger. apply Step.
Qed.

Lemma framed_local_write id value : framed (lwrite id value).
Proof.
  intros ctx s. rewrite (runs_local_write s id value ctx). apply strong_post_ret.
  destruct s as [m [[frame stack] globals]]. reflexivity.
Qed.

Lemma framed_local_read id : framed (lread id).
Proof.
  unfold lread. eapply framed_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - intros [m [[frame stack] globals]]. destruct frame as [vars exc loc].
    unfold interp_vellvm_h, fused_local, on_ls, handle_local_stack, handle_local_debug, handle_local.
    cbn. destruct (RM.find id vars); cbn.
    + repeat rewrite Eqit.bind_ret_l. apply strong_post_ret. reflexivity.
    + repeat rewrite Eqit.bind_bind. eapply strong_post_bind with (P := fun _ => False).
      * apply strong_post_error.
      * intros x [].
Qed.

Lemma framed_memory_event X (e : MemoryE X) :
  (forall s, memory_framed (Impl.handle_memoryM e) s) ->
  framed (trigger (inr1 (subevent _ e))).
Proof.
  intro Frame. eapply framed_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - intros [m rest].
    change (strong_post
      (ITree.bind (run_memory (Impl.handle_memoryM e) m)
        (fun '(m', x) => Ret ((m', rest), x)))
      (fun '(final, _) => structural_frame final = structural_frame (m, rest))).
    eapply strong_post_bind; [apply memory_framed_sound, Frame|].
    intros [m' x] Equal. apply strong_post_ret. unfold structural_frame. simpl. now rewrite Equal.
Qed.

Lemma framed_load dt address : framed (LLVMEvents.load dt address).
Proof.
  apply framed_memory_event. intro s. destruct address; try exact I.
  destruct db; try exact I. apply memory_framed_load.
Qed.

Lemma framed_store dt address value : framed (LLVMEvents.store dt address value).
Proof.
  apply framed_memory_event. intro s. destruct address; try exact I.
  destruct db; try exact I. apply memory_framed_store.
Qed.

Lemma framed_expression e : plain_expression e -> forall top, framed (denote_exp' top e).
Proof.
  intro Plain. induction Plain; intro top; unfold denote_exp'; cbn [denote_exp].
  - eapply framed_eutt with (u := lread id).
    + unfold lookup_id, withCall, lread. rewrite translate_trigger. reflexivity.
    + apply framed_local_read.
  - destruct top; [apply framed_eou|apply framed_with_call_abort].
  - apply framed_with_call_bind; [apply IHPlain1|]. intro a'.
    apply framed_with_call_bind; [apply IHPlain2|]. intro b'. apply framed_eou.
  - apply framed_with_call_bind; [apply IHPlain1|]. intro a'.
    apply framed_with_call_bind; [apply IHPlain2|]. intro b'. apply framed_eou.
  - apply framed_with_call_bind; [apply IHPlain|]. intro a'. cbn [convert]. apply framed_eou.
  - apply framed_with_call_bind; [apply IHPlain1|]. intro p.
    cbn [map_monad]. apply framed_with_call_bind.
    + apply framed_with_call_bind; [apply IHPlain2|]. intro i.
      apply framed_with_call_bind; intro; apply framed_with_call_ret.
    + intro indices. apply framed_eou.
Qed.

Lemma framed_instruction i : plain_instruction i -> forall varargs, framed (denote_instr i varargs).
Proof.
  intro Plain. destruct Plain; intro varargs; unfold denote_instr.
  - apply framed_bind; [apply framed_expression, H|]. intro value.
    apply framed_bind; [apply framed_local_write|]. intro u. apply framed_ret.
  - apply framed_bind; [apply framed_expression, H|]. intro pointer_value.
    apply framed_bind; [apply framed_load|]. intro value. apply framed_local_write.
  - apply framed_bind; [apply framed_expression, H|]. intro v.
    apply framed_bind; [apply framed_expression, H0|]. intro p.
    apply framed_bind; [|intro u; apply framed_ret].
    destruct p; try apply framed_store.
    destruct db; try apply framed_store. apply framed_abort.
Qed.

Lemma framed_terminator t : plain_terminator t -> framed (denote_terminator t).
Proof.
  intro Plain. destruct Plain; unfold denote_terminator.
  - apply framed_bind; [apply framed_expression, H|]. intro returned. apply framed_ret.
  - apply framed_bind; [apply framed_expression, H|]. intro v.
    repeat match goal with |- framed (match ?value with _ => _ end) => destruct value end;
      try apply framed_ret; try apply framed_abort.
    destruct sz; try apply framed_abort.
    destruct (VellvmIntegers.equ x VellvmIntegers.one); apply framed_ret.
  - apply framed_ret.
Qed.

Lemma framed_map A B (f : A -> CFGtop B) xs :
  (forall x, In x xs -> framed (f x)) -> framed (map_monad f xs).
Proof.
  intro Frame. induction xs as [|x xs IH]; cbn [map_monad].
  - apply framed_ret.
  - apply framed_bind; [apply Frame; now left|]. intro y.
    apply framed_bind; [apply IH; intros; apply Frame; now right|]. intro ys. apply framed_ret.
Qed.

Lemma framed_code code varargs : Forall plain_instruction code -> framed (denote_code code varargs).
Proof.
  intro Plain. unfold denote_code. induction Plain; cbn [loop_monad].
  - apply framed_ret.
  - apply framed_bind; [apply framed_instruction, H|]. intros; exact IHPlain.
Qed.

Lemma plain_assoc (from : block_id) (arms : list (block_id * exp dtyp)) value : Forall (fun arm => plain_expression (snd arm)) arms ->
  assoc from arms = Some value -> plain_expression value.
Proof.
  intro Plain. induction Plain as [|[label expression] rest Expr Rest IH]; [discriminate|].
  cbn [assoc]. destruct (rel_dec from label); [intros E; inversion E; subst; exact Expr|apply IH].
Qed.

Lemma framed_phi from p : plain_phi p -> framed (denote_phi from p).
Proof.
  intro Plain. destruct Plain. unfold denote_phi.
  destruct (assoc from arms) as [expression|] eqn:Found.
  - apply framed_bind; [apply framed_expression; exact (@plain_assoc from arms expression H Found)|].
    intro returned. apply framed_ret.
  - apply framed_abort.
Qed.

Lemma framed_phis from phis : Forall plain_phi phis -> framed (denote_phis from phis).
Proof.
  intro Plain. unfold denote_phis. apply framed_bind.
  - apply framed_map. intros p Member. apply framed_phi. eapply Forall_forall; eassumption.
  - intro values. apply framed_bind.
    + apply framed_map. intros [id value] Member. apply framed_local_write.
    + intro u. apply framed_ret.
Qed.

Lemma framed_block b : plain_block b -> forall from varargs, framed (denote_block b from varargs).
Proof.
  intros [Phis Code Term] from varargs. unfold denote_block.
  apply framed_bind; [apply framed_phis, Phis|]. intro u.
  apply framed_bind; [apply framed_code, Code|]. intro v. apply framed_terminator, Term.
Qed.

Lemma framed_runs A (t : CFGtop A) initial final value :
  framed t -> runs t initial final value -> structural_frame final = structural_frame initial.
Proof.
  intros Frame Run.
  specialize (Frame (fun X _ => @ITree.spin CFGEtop X) initial).
  rewrite (Run (fun X _ => @ITree.spin CFGEtop X)) in Frame.
  apply eqit_inv_Ret in Frame. exact (proj2 Frame).
Qed.

Theorem full_block_path_frame varargs from label initial final value :
  block_path (blks FullCFG.body) varargs from label initial final value ->
  structural_frame final = structural_frame initial.
Proof.
  intro Path. induction Path.
  - eapply framed_runs; [apply framed_block; eapply body_block_plain; eassumption|exact H0].
  - transitivity (structural_frame middle); [exact IHPath|].
    eapply framed_runs; [apply framed_block; eapply body_block_plain; eassumption|exact H0].
Qed.

Theorem full_block_steps_frame varargs from label initial last_from last_label final :
  block_steps (blks FullCFG.body) varargs from label initial last_from last_label final ->
  structural_frame final = structural_frame initial.
Proof.
  intro Steps. induction Steps; [reflexivity|].
  transitivity (structural_frame middle); [exact IHSteps|].
  eapply framed_runs; [apply framed_block; eapply body_block_plain; eassumption|exact H0].
Qed.
