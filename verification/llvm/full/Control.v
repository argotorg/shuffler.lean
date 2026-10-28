(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String Morphisms.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents InterpretationStack Denotation Equational
  Handlers.Local Handlers.Stack Handlers.Intrinsics Interfaces.Memory
  Implementations.Memory Handlers.Memory.
Require Import MemoryRelation.
Import ListNotations.
Import ITreeNotations.
Open Scope itree_scope.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition call_context := CallE ~> CFGtop.

(* Use the same call interpreter and state interpreter as denote_mcfg and
   interpreter_gen. Keeping the call context arbitrary lets block proofs be
   used inside the complete module call. *)
Definition run {A} (ctx : call_context) (t : CFGtop A) (s : FusedS) :=
  interp_mcfg (interp_mrec ctx t) s.

Definition runs {A} (t : CFGtop A) initial final (value : A) : Prop :=
  forall ctx, eutt eq (run ctx t initial) (Ret (final, value)).

#[export] Instance run_respects A ctx :
  Proper (eutt eq ==> eq ==> eutt eq) (@run A ctx).
Proof.
  intros t u Equal s s' Same; subst s'.
  unfold run, interp_mcfg, interp_intrinsics.
  rewrite !interp_mrec_as_interp. now rewrite Equal.
Qed.


Lemma run_bind A B ctx (t : CFGtop A) (k : A -> CFGtop B) s :
  eutt eq (run ctx (ITree.bind t k) s)
    (ITree.bind (run ctx t s) (fun '(s', x) => run ctx (k x) s')).
Proof.
  unfold run, interp_mcfg, interp_intrinsics.
  rewrite interp_mrec_bind, interp_bind, interp_state_bind.
  apply eutt_eq_bind; intros [s' x]; reflexivity.
Qed.

Lemma runs_ret A s (x : A) : runs (Ret x) s s x.
Proof.
  intro ctx. unfold run, interp_mcfg, interp_intrinsics.
  rewrite interp_mrec_as_interp, !interp_ret, interp_state_ret.
  reflexivity.
Qed.

Lemma runs_bind A B (t : CFGtop A) (k : A -> CFGtop B) s middle final x y :
  runs t s middle x -> runs (k x) middle final y ->
  runs (ITree.bind t k) s final y.
Proof.
  intros First Last ctx. rewrite run_bind, (First ctx), bind_ret_l. apply Last.
Qed.

Lemma runs_eutt A (t u : CFGtop A) s final x :
  eutt eq t u -> runs u s final x -> runs t s final x.
Proof.
  intros Equal Run ctx.
  rewrite Equal. apply Run.
Qed.

Lemma runs_event X (e : MCFGEtop X) s final x :
  eutt eq (interp_intrinsics (trigger e)) (trigger e) ->
  eutt eq (interp_vellvm_h e s) (Ret (final, x)) ->
  runs (trigger (inr1 e)) s final x.
Proof.
  intros Intrinsic Step ctx. unfold run, interp_mcfg, interp_intrinsics.
  rewrite interp_mrec_as_interp, interp_trigger.
  cbn [mrecursive].
  unfold interp_intrinsics in Intrinsic.
  rewrite Intrinsic, interp_state_trigger. exact Step.
Qed.

Definition locals (s : FusedS) := stack_vars (fst (fst (snd s))).

Definition with_locals (s : FusedS) vars : FusedS :=
  let '(m, ((frame, stack), globals)) := s in
  (m, ((upd_local_sf frame vars, stack), globals)).

Definition set_local s id value :=
  with_locals s (Maps.add id value (locals s)).

Definition with_memory (s : FusedS) m : FusedS := (m, snd s).

Lemma with_memory_same s : with_memory s (fst s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma locals_with_memory s m : locals (with_memory s m) = locals s.
Proof. destruct s; reflexivity. Qed.

Lemma memory_set_local s id value : fst (set_local s id value) = fst s.
Proof. destruct s as [m [[frame stack] globals]]; reflexivity. Qed.

Lemma lookup_local_same s id value :
  Maps.lookup id (locals (set_local s id value)) = Some value.
Proof.
  destruct s as [m [[frame stack] globals]].
  change (RM.find id (RM.add id value (stack_vars frame)) = Some value).
  apply RMF.F.add_eq_o; reflexivity.
Qed.

Lemma lookup_local_other s id other value :
  other <> id ->
  Maps.lookup other (locals (set_local s id value)) = Maps.lookup other (locals s).
Proof.
  intro Different. destruct s as [m [[frame stack] globals]].
  change (RM.find other (RM.add id value (stack_vars frame)) =
    RM.find other (stack_vars frame)).
  apply RMF.F.add_neq_o. congruence.
Qed.

Lemma runs_local_read s id value :
  Maps.lookup id (locals s) = Some value ->
  runs (lread id) s s value.
Proof.
  intro Found. unfold lread. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [m [[frame stack] globals]]. destruct frame as [vars exc loc].
    change (RM.find id vars = Some value) in Found.
    unfold interp_vellvm_h, fused_local, on_ls, handle_local_stack,
      handle_local_debug, handle_local.
    cbn. rewrite Found. cbn.
    repeat rewrite bind_ret_l. reflexivity.
Qed.

Lemma runs_local_write s id value :
  runs (lwrite id value) s (set_local s id value) tt.
Proof.
  unfold lwrite. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [m [[frame stack] globals]]. destruct frame as [vars exc loc].
    unfold interp_vellvm_h, fused_local, on_ls, handle_local_stack,
      handle_local_debug, handle_local.
    cbn. repeat rewrite bind_ret_l. reflexivity.
Qed.

Lemma runs_load s p dt m value :
  run_memory (Impl.read_dvalue dt p) (fst s) = Ret (m, value) ->
  runs (LLVMEvents.load dt (DVALUE_Base (DVALUE_Pointer p))) s
    (with_memory s m) value.
Proof.
  intro Read. unfold LLVMEvents.load. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [initial rest].
    change (eutt eq
      (ITree.bind (run_memory (Impl.read_dvalue dt p) initial)
        (fun '(m', x) => Ret ((m', rest), x))) (Ret ((m, rest), value))).
    change (run_memory (Impl.read_dvalue dt p) initial = Ret (m, value)) in Read.
    rewrite Read.
    rewrite bind_ret_l. reflexivity.
Qed.

Lemma runs_store s p dt value m :
  run_memory (Impl.write_dvalue p dt value) (fst s) = Ret (m, tt) ->
  runs (LLVMEvents.store dt (DVALUE_Base (DVALUE_Pointer p)) value) s
    (with_memory s m) tt.
Proof.
  intro Write. unfold LLVMEvents.store. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [initial rest].
    change (eutt eq
      (ITree.bind (run_memory (Impl.write_dvalue p dt value) initial)
        (fun '(m', x) => Ret ((m', rest), x))) (Ret ((m, rest), tt))).
    change (run_memory (Impl.write_dvalue p dt value) initial = Ret (m, tt)) in Write.
    rewrite Write.
    rewrite bind_ret_l. reflexivity.
Qed.

(* A path through the actual LLVM blocks. The block premise is a theorem
   about Vellvm's denotation under the actual interpreters, not a second
   implementation of the instructions. *)
Inductive block_path (blocks : list (LLVMAst.block dtyp)) (varargs : option ptr) :
    block_id -> block_id -> FusedS -> FusedS -> dvalue -> Prop :=
| path_return from label b s final value :
    find_block blocks label = Some b ->
    runs (denote_block b from varargs) s final (inr value) ->
    block_path blocks varargs from label s final value
| path_jump from label b target s middle final value :
    find_block blocks label = Some b ->
    runs (denote_block b from varargs) s middle (inl target) ->
    block_path blocks varargs label target middle final value ->
    block_path blocks varargs from label s final value.

Theorem block_path_sound blocks varargs from label s final value :
  block_path blocks varargs from label s final value ->
  runs (denote_ocfg blocks varargs (from, label)) s final (inr value).
Proof.
  intro Path. induction Path.
  - eapply runs_eutt; [apply denote_ocfg_unfold_in; eassumption|].
    eapply runs_bind; [eassumption|apply runs_ret].
  - eapply runs_eutt; [apply denote_ocfg_unfold_in; eassumption|].
    eapply runs_bind; eassumption.
Qed.

(* A finite prefix may end at a loop exit, before the function returns. *)
Inductive block_steps (blocks : list (LLVMAst.block dtyp)) (varargs : option ptr) :
    block_id -> block_id -> FusedS -> block_id -> block_id -> FusedS -> Prop :=
| steps_done from label s : block_steps blocks varargs from label s from label s
| steps_next from label b target s middle last_from last_label final :
    find_block blocks label = Some b ->
    runs (denote_block b from varargs) s middle (inl target) ->
    block_steps blocks varargs label target middle last_from last_label final ->
    block_steps blocks varargs from label s last_from last_label final.

Theorem block_steps_sound blocks varargs from label s last_from last_label final :
  block_steps blocks varargs from label s last_from last_label final ->
  forall ctx, eutt eq (run ctx (denote_ocfg blocks varargs (from, label)) s)
    (run ctx (denote_ocfg blocks varargs (last_from, last_label)) final).
Proof.
  intro Steps. induction Steps; intro ctx; [reflexivity|].
  rewrite (denote_ocfg_unfold_in _ _ _ _ H), run_bind, (H0 ctx), bind_ret_l.
  apply IHSteps.
Qed.

Lemma block_steps_append blocks varargs from label s middle_from middle_label middle
    last_from last_label final :
  block_steps blocks varargs from label s middle_from middle_label middle ->
  block_steps blocks varargs middle_from middle_label middle last_from last_label final ->
  block_steps blocks varargs from label s last_from last_label final.
Proof.
  intros Prefix Suffix. induction Prefix; [exact Suffix|].
  eapply steps_next; eauto.
Qed.
