(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes
  Cop Clight ClightBigstep.
Require Import Permute ClightMemory ClightEntry ClightEval ClightEvalProofs ClightScalar.
Import ListNotations.

Definition call_arguments size data_arg perm_arg target_arg used_arg trace_arg out_arg :=
  [Vint size; data_arg; perm_arg; target_arg; used_arg; trace_arg; out_arg].

Definition call_temps size data_arg perm_arg target_arg used_arg trace_arg out_arg :=
  PTree.set out out_arg
    (PTree.set trace trace_arg
    (PTree.set used used_arg
    (PTree.set target target_arg
    (PTree.set permutation perm_arg
    (PTree.set data data_arg
    (PTree.set n (Vint size) (create_undef_temps (fn_temps permute)))))))).

Lemma permute_entry ge m size da pa ta ua tr oa :
  function_entry2 ge permute (call_arguments size da pa ta ua tr oa) m empty_env
    (call_temps size da pa ta ua tr oa) m.
Proof.
  constructor.
  - constructor.
  - cbn [permute fn_params var_names map].
    repeat constructor; simpl; intuition discriminate.
  - unfold list_disjoint. cbn [permute fn_params fn_temps var_names map].
    intros x y Hx Hy.
    cbv [List.In fst n data permutation target used trace out i j top pos tmp depth] in Hx, Hy.
    intuition congruence.
  - constructor.
  - reflexivity.
Qed.

Definition nonempty_tail := seq [check_input; normalize;
  set top (sub (reg n) (lit 1));
  Sloop (seq [choose_position; exchange]) Sskip].

(* Compose the checked size guards with the rest of the function. *)
Lemma permute_nonempty_body ge e le m m1 m2 m3 le' m' outcome count :
  (1 <= count <= 1024)%Z ->
  PTree.get n le = Some (Vint (Int.repr count)) ->
  store ge le m (cell out (lit 0)) (lit 0) = Some m1 ->
  store ge le m1 (cell out (lit 1)) (lit 0) = Some m2 ->
  store ge le m2 (cell out (lit 2)) (lit 0) = Some m3 ->
  exec_stmt function_entry2 ge e le m3 nonempty_tail E0 le' m' outcome ->
  exec_stmt function_entry2 ge e le m (fn_body permute) E0 le' m' outcome.
Proof.
  intros Bound N S1 S2 S3 Tail.
  assert (C : uint count) by (unfold uint; change Int.max_unsigned with 4294967295%Z; lia).
  assert (Fits : expression ge le m3 (gt (reg n) (lit 1024)) = Some Vfalse).
  { pose proof (expression_compare ge le m3 Cgt (reg n) (lit 1024)
      count 1024 eq_refl eq_refl C ltac:(unfold uint; vm_compute; intuition discriminate)
      N eq_refl) as H.
    unfold zcompare in H. destruct (Coqlib.zlt 1024 count); [lia|exact H]. }
  assert (Nonempty : expression ge le m3 (Permute.eq (reg n) (lit 0)) = Some Vfalse).
  { pose proof (expression_compare ge le m3 Ceq (reg n) (lit 0)
      count 0 eq_refl eq_refl C ltac:(unfold uint; vm_compute; intuition discriminate)
      N eq_refl) as H.
    unfold zcompare in H. destruct (Coqlib.zeq count 0); [lia|exact H]. }
  cbn [permute fn_body seq fold_right].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_store; exact S1|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_store; exact S2|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_store; exact S3|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
    + apply expression_sound. exact Fits.
    + reflexivity.
    + constructor.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      * apply expression_sound. exact Nonempty.
      * reflexivity.
      * constructor.
    + exact Tail.
Qed.

Lemma set_top_value ge e le m count :
  (1 <= count <= 1024)%Z ->
  PTree.get n le = Some (Vint (Int.repr count)) ->
  exec_stmt function_entry2 ge e le m (set top (sub (reg n) (lit 1))) E0
    (PTree.set top (Vint (Int.repr (count - 1))) le) m Out_normal.
Proof.
  intros Bound N. apply exec_Sset. apply expression_sound.
  eapply expression_sub; try reflexivity; try exact N;
    unfold uint; change Int.max_unsigned with 4294967295%Z; lia.
Qed.

(* This wrapper supplies the real Clight function entry, return conversion,
   and empty local-block cleanup. A body theorem alone omits these steps. *)
Theorem permute_call ge m size da pa ta ua tr oa le' m' status :
  exec_stmt function_entry2 ge empty_env
    (call_temps size da pa ta ua tr oa) m (fn_body permute) E0 le' m'
    (Out_return (Some (Vint status, u32))) ->
  eval_funcall function_entry2 ge m (Internal permute)
    (call_arguments size da pa ta ua tr oa) E0 m' (Vint status).
Proof.
  intro Body. eapply eval_funcall_internal.
  - apply permute_entry.
  - exact Body.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.

Theorem permute_empty_call ge m da pa ta ua tr bo :
  writable_array m bo 3 ->
  exists m',
    eval_funcall function_entry2 ge m (Internal permute)
      (call_arguments Int.zero da pa ta ua tr (Vptr bo Ptrofs.zero)) E0 m' (Vint Int.zero) /\
    array_at m' bo [0%Z; 0%Z; 0%Z].
Proof.
  intro Writable.
  destruct (permute_empty ge empty_env
    (call_temps Int.zero da pa ta ua tr (Vptr bo Ptrofs.zero)) m bo
    eq_refl eq_refl Writable) as [m' [Body Output]].
  exists m'. split; [eapply permute_call; exact Body|exact Output].
Qed.

Theorem permute_oversized_call ge m da pa ta ua tr bo z :
  (1024 < z <= Int.max_unsigned)%Z -> writable_array m bo 3 ->
  exists m',
    eval_funcall function_entry2 ge m (Internal permute)
      (call_arguments (Int.repr z) da pa ta ua tr (Vptr bo Ptrofs.zero)) E0 m'
      (Vint (Int.repr 2)) /\ array_at m' bo [0%Z; 0%Z; 0%Z].
Proof.
  intros Size Writable.
  destruct (permute_oversized ge empty_env
    (call_temps (Int.repr z) da pa ta ua tr (Vptr bo Ptrofs.zero)) m bo z
    eq_refl Size eq_refl Writable) as [m' [Body Output]].
  exists m'. split; [eapply permute_call; exact Body|exact Output].
Qed.

Print Assumptions permute_call.
Print Assumptions permute_empty_call.
Print Assumptions permute_oversized_call.

Lemma cell_store_memory ge le m a index rhs b k m' :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  typeof index = u32 -> expression ge le m index = Some (Vint (Int.repr k)) ->
  (0 <= k <= 2048)%Z ->
  store ge le m (cell a index) rhs = Some m' ->
  exists value, Mem.store Mint32 m b (4 * k) value = Some m'.
Proof.
  intros Base IndexTy Index Bound Store.
  unfold store, cell in Store. cbn [expression] in Store.
  rewrite Base, Index, IndexTy in Store.
  rewrite pointer_index in Store by exact Bound.
  destruct (expression ge le m rhs) as [value|] eqn:R; try discriminate.
  destruct (sem_cast value (typeof rhs) u32 m) as [converted|] eqn:C;
    try discriminate.
  exists converted. cbn [u32 access_mode Mem.storev] in Store.
  rewrite Ptrofs.unsigned_repr in Store by
    (change (0 <= 4 * k <= 18446744073709551615)%Z; lia).
  exact Store.
Qed.

(* Initialize the output without changing any other array or its capacity.
   These frames are needed to compose the entry with the nonempty passes. *)
Lemma initialize_output_frame ge le m b :
  PTree.get out le = Some (Vptr b Ptrofs.zero) ->
  writable_array m b 3 ->
  exists m1 m2 m3,
    store ge le m (cell out (lit 0)) (lit 0) = Some m1 /\
    store ge le m1 (cell out (lit 1)) (lit 0) = Some m2 /\
    store ge le m2 (cell out (lit 2)) (lit 0) = Some m3 /\
    array_at m3 b [0%Z; 0%Z; 0%Z] /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m3 other xs) /\
    (forall other count, writable_array m other count -> writable_array m3 other count).
Proof.
  intros Out Writable.
  destruct (initialize_output ge le m b Out Writable) as [m1 [m2 [m3 [S1 [S2 [S3 Array]]]]]].
  destruct (cell_store_memory ge le m out (lit 0) (lit 0) b 0 m1
    Out eq_refl eq_refl ltac:(lia) S1) as [v1 W1].
  destruct (cell_store_memory ge le m1 out (lit 1) (lit 0) b 1 m2
    Out eq_refl eq_refl ltac:(lia) S2) as [v2 W2].
  destruct (cell_store_memory ge le m2 out (lit 2) (lit 0) b 2 m3
    Out eq_refl eq_refl ltac:(lia) S3) as [v3 W3].
  exists m1, m2, m3. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  split; [exact Array|]. split.
  - intros other xs Separate Other.
    eapply array_store_disjoint; [|exact Separate|exact W3].
    eapply array_store_disjoint; [|exact Separate|exact W2].
    eapply array_store_disjoint; eauto.
  - intros other count Other.
    eapply writable_array_store; [|exact W3].
    eapply writable_array_store; [|exact W2].
    eapply writable_array_store; eauto.
Qed.
