(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack EOU Operations
  Interfaces.Memory Implementations.Memory Handlers.Local Handlers.Stack Handlers.Intrinsics.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry.
Import ListNotations.
Import ITreeNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition memory_with_frames (m : Impl.State) frames :=
  Impl.mkState (Impl.mkMemoryStack (bytes m) frames
    (Impl.Memory_stack_heap (Impl.state_memory_stack m))) (Impl.state_provenance m).

Definition pushed_memory m := memory_with_frames m
  (Impl.Snoc (Impl.Memory_stack_frame_stack (Impl.state_memory_stack m)) []).

Definition fresh_memory (m : Impl.State) :=
  Impl.mkState (Impl.state_memory_stack m) (next_provenance (Impl.state_provenance m)).

Definition empty_varargs_pointer m : ptr :=
  (Handler.next_key_with_alignment (bytes m) 8,
   allocation_id_to_prov (provenance_to_allocation_id (next_provenance (Impl.state_provenance m)))).

Lemma cells_related_same_bytes layout c before after :
  bytes after = bytes before -> cells_related layout c before -> cells_related layout c after.
Proof.
  intros Bytes Related b k K. destruct (Related b k K) as [Valid [Writable Contents]].
  split; [exact Valid|]. split.
  - eapply writable_word_unchanged; [intros; rewrite Bytes; reflexivity|exact Writable].
  - intros x Load. eapply word_at_unchanged; [intros; rewrite Bytes; reflexivity|].
    apply Contents, Load.
Qed.

Lemma memory_push_correct m : run_memory Impl.Mempush m = Ret (pushed_memory m, tt).
Proof. destruct m as [[data frames heap] provenance]; reflexivity. Qed.

Lemma memory_pop_empty_correct m frames :
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack m) = Impl.Snoc frames [] ->
  run_memory Impl.Mempop m = Ret (memory_with_frames m frames, tt).
Proof.
  destruct m as [[data old_frames heap] provenance]. simpl. intro Frames. subst old_frames.
  reflexivity.
Qed.

Lemma empty_struct_store m p :
  run_memory (Impl.write_dvalue p (DTYPE_Struct true []) (DVALUE_Struct true [])) m = Ret (m, tt).
Proof. destruct p; reflexivity. Qed.

Lemma empty_struct_allocation m :
  eutt eq (run_memory (Impl.allocate_dtyp (DTYPE_Struct true []) 1 8) m)
    (Ret (fresh_memory m, empty_varargs_pointer m)).
Proof.
  destruct m as [[data frames heap] provenance].
  unfold run_memory, Impl.allocate_dtyp, Impl.allocate_bytes.
  cbn.
  rewrite Eqit.bind_ret_l. reflexivity.
Qed.

Definition pushed_locals (s : FusedS) args : FusedS :=
  let '(m, ((frame, stack), globals)) := s in
  let initial := List.fold_right (fun '(id, value) => Maps.add id value) Maps.empty args in
  let fresh := Build_stack_frame initial None (Some (printer_object.(printer_get_loc) tt)) in
  (m, ((fresh, frame :: stack), globals)).

Lemma runs_memory_push s : runs mem_push s (with_memory s (pushed_memory (fst s))) tt.
Proof.
  unfold mem_push. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [m rest].
    change (eutt eq (ITree.bind (run_memory Impl.Mempush m)
      (fun '(m', value) => Ret ((m', rest), value))) (Ret ((pushed_memory m, rest), tt))).
    rewrite memory_push_correct, Eqit.bind_ret_l. reflexivity.
Qed.

Lemma runs_memory_pop_empty s frames :
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst s)) = Impl.Snoc frames [] ->
  runs mem_pop s (with_memory s (memory_with_frames (fst s) frames)) tt.
Proof.
  intro Frames. unfold mem_pop. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [m rest].
    change (eutt eq (ITree.bind (run_memory Impl.Mempop m)
      (fun '(m', value) => Ret ((m', rest), value))) (Ret ((memory_with_frames m frames, rest), tt))).
    rewrite (@memory_pop_empty_correct m frames Frames), Eqit.bind_ret_l. reflexivity.
Qed.

Lemma runs_stack_push s args : runs (stack_push args) s (pushed_locals s args) tt.
Proof.
  unfold stack_push. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [m [[frame stack] globals]].
    unfold interp_vellvm_h, fused_stack, on_ls, handle_stack. cbn.
    rewrite !Eqit.bind_ret_l. reflexivity.
Qed.

Lemma runs_stack_pop m frame caller stack globals :
  runs stack_pop (m, ((frame, caller :: stack), globals)) (m, ((caller, stack), globals)) tt.
Proof.
  unfold stack_pop. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - unfold interp_vellvm_h, fused_stack, on_ls, handle_stack. cbn.
    rewrite !Eqit.bind_ret_l. reflexivity.
Qed.

Lemma runs_empty_alloca s :
  runs (alloca (DTYPE_Struct true []) 1 None) s
    (with_memory s (fresh_memory (fst s)))
    (DVALUE_Base (DVALUE_Pointer (empty_varargs_pointer (fst s)))).
Proof.
  unfold alloca. eapply runs_event.
  - unfold interp_intrinsics. rewrite interp_trigger. reflexivity.
  - destruct s as [[[data frames heap] provenance] rest].
    unfold interp_vellvm_h, fused_memory, on_mem, Handler.handle_memory,
      Impl.handle_memoryM, run_memory, Impl.allocate_dtyp, Impl.allocate_bytes.
    cbn. rewrite !Eqit.bind_ret_l. reflexivity.
Qed.

Definition call_bindings (n data perm target used trace output : dvalue) :=
  [(Name "v1", n); (Name "v2", data); (Name "v3", perm); (Name "v4", target);
   (Name "v5", used); (Name "v6", trace); (Name "v7", output)].

Definition call_state s n data perm target used trace output :=
  with_memory (pushed_locals s (call_bindings n data perm target used trace output))
    (fresh_memory (pushed_memory (fst s))).

Lemma combine_call_arguments n data perm target used trace output :
  combine_lists_varargs (df_args FullCFG.function) [n; data; perm; target; used; trace; output] =
    raise_ret (call_bindings n data perm target used trace output, []).
Proof. reflexivity. Qed.

Lemma push_call_runs s n data perm target used trace output :
  runs (push_call_frame FullCFG.function [n; data; perm; target; used; trace; output]) s
    (call_state s n data perm target used trace output) (empty_varargs_pointer (fst s)).
Proof.
  unfold push_call_frame. rewrite combine_call_arguments.
  cbn.
  eapply runs_bind; [apply runs_ret|].
  eapply runs_bind; [apply runs_ret|].
  eapply runs_bind; [apply runs_memory_push|].
  eapply runs_bind; [apply runs_stack_push|].
  eapply runs_bind; [apply runs_empty_alloca|].
  eapply runs_bind.
  - apply runs_store, empty_struct_store.
  - destruct s as [m [[frame stack] globals]]. apply runs_ret.
Qed.

Lemma call_state_bytes s n data perm target used trace output :
  bytes (fst (call_state s n data perm target used trace output)) = bytes (fst s).
Proof. destruct s as [m [[frame stack] globals]]; reflexivity. Qed.

Lemma call_state_related layout c s n data perm target used trace output :
  cells_related layout c (fst s) ->
  cells_related layout c (fst (call_state s n data perm target used trace output)).
Proof. apply cells_related_same_bytes, call_state_bytes. Qed.

Lemma call_state_bindings s n data perm target used trace output :
  Maps.lookup (Name "v1") (locals (call_state s n data perm target used trace output)) = Some n /\
  Maps.lookup (Name "v2") (locals (call_state s n data perm target used trace output)) = Some data /\
  Maps.lookup (Name "v3") (locals (call_state s n data perm target used trace output)) = Some perm /\
  Maps.lookup (Name "v4") (locals (call_state s n data perm target used trace output)) = Some target /\
  Maps.lookup (Name "v5") (locals (call_state s n data perm target used trace output)) = Some used /\
  Maps.lookup (Name "v6") (locals (call_state s n data perm target used trace output)) = Some trace /\
  Maps.lookup (Name "v7") (locals (call_state s n data perm target used trace output)) = Some output.
Proof.
  destruct s as [m [[frame stack] globals]].
  unfold call_state, pushed_locals, call_bindings, locals, with_memory. cbn.
  repeat split;
    repeat first [rewrite RMF.F.add_eq_o by reflexivity | rewrite RMF.F.add_neq_o by discriminate];
    reflexivity.
Qed.

Lemma pop_call_runs m frame caller stack globals frames :
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack m) = Impl.Snoc frames [] ->
  runs (@pop_call_frame _ _ _ _) (m, ((frame, caller :: stack), globals))
    (memory_with_frames m frames, ((caller, stack), globals)) tt.
Proof.
  intro Frames. unfold pop_call_frame.
  eapply runs_bind; [apply runs_stack_pop|]. apply runs_memory_pop_empty, Frames.
Qed.

Lemma popped_memory_related layout c m frames :
  cells_related layout c m -> cells_related layout c (memory_with_frames m frames).
Proof. apply cells_related_same_bytes. reflexivity. Qed.

Lemma call_state_structure s n data perm target used trace output :
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack
    (fst (call_state s n data perm target used trace output))) =
    Impl.Snoc (Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst s))) [] /\
  snd (fst (snd (call_state s n data perm target used trace output))) =
    fst (fst (snd s)) :: snd (fst (snd s)) /\
  snd (snd (call_state s n data perm target used trace output)) = snd (snd s).
Proof. destruct s as [m [[frame stack] globals]]; repeat split; reflexivity. Qed.

Definition returned_state (caller body : FusedS) : FusedS :=
  (memory_with_frames (fst body)
    (Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst caller))), snd caller).

Lemma pop_call_restores caller body :
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst body)) =
    Impl.Snoc (Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst caller))) [] ->
  snd (fst (snd body)) = fst (fst (snd caller)) :: snd (fst (snd caller)) ->
  snd (snd body) = snd (snd caller) ->
  runs (@pop_call_frame _ _ _ _) body (returned_state caller body) tt.
Proof.
  destruct caller as [old_memory [[old_frame old_stack] old_globals]].
  destruct body as [memory [[frame stack] globals]].
  cbn. intros Frames Stack Globals. subst stack globals. apply pop_call_runs, Frames.
Qed.

Lemma returned_state_related layout c caller body :
  cells_related layout c (fst body) -> cells_related layout c (fst (returned_state caller body)).
Proof. apply popped_memory_related. Qed.

Lemma returned_state_caller caller body : snd (returned_state caller body) = snd caller.
Proof. reflexivity. Qed.

Lemma call_denotation_runs caller body n data perm target used trace output value :
  runs (run_exc (denote_cfg FullCFG.body (Some (empty_varargs_pointer (fst caller)))))
    (call_state caller n data perm target used trace output) body (inr value) ->
  Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst body)) =
    Impl.Snoc (Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst caller))) [] ->
  snd (fst (snd body)) = fst (fst (snd caller)) :: snd (fst (snd caller)) ->
  snd (snd body) = snd (snd caller) ->
  runs (denote_function FullCFG.function [n; data; perm; target; used; trace; output])
    caller (returned_state caller body) (inr value).
Proof.
  intros Body Frames Stack Globals. unfold denote_function.
  eapply runs_bind; [apply push_call_runs|].
  eapply runs_bind; [exact Body|].
  eapply runs_bind with (middle := returned_state caller body) (x := tt).
  - exact (@pop_call_restores caller body Frames Stack Globals).
  - apply runs_ret.
Qed.
