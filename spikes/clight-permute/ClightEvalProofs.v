(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Coq Require Import List ZArith.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import ClightEval.

Theorem expression_sound ge e le m a v :
  expression ge le m a = Some v -> eval_expr ge e le m a v.
Proof.
  revert v. induction a; simpl; intros v H; try discriminate.
  - inversion H; subst. constructor.
  - constructor. exact H.
  - destruct (expression ge le m a) as [x|] eqn:X; try discriminate.
    destruct x; try discriminate.
    destruct (access_mode t) eqn:A; try discriminate.
    eapply eval_Elvalue.
    + apply eval_Ederef. apply IHa. reflexivity.
    + eapply deref_loc_value; eauto.
  - destruct (expression ge le m a1) as [x|] eqn:X; try discriminate.
    destruct (expression ge le m a2) as [y|] eqn:Y; try discriminate.
    eapply eval_Ebinop; eauto.
Qed.

Theorem store_sound ge e le m lhs rhs m' :
  store ge le m lhs rhs = Some m' ->
  exists b ofs x y,
    eval_lvalue ge e le m lhs b ofs Full /\
    eval_expr ge e le m rhs x /\
    sem_cast x (typeof rhs) (typeof lhs) m = Some y /\
    assign_loc ge (typeof lhs) m b ofs Full y m'.
Proof.
  destruct lhs; simpl; try discriminate.
  destruct (expression ge le m lhs) as [address|] eqn:A; try discriminate.
  destruct address; try discriminate.
  destruct (expression ge le m rhs) as [x|] eqn:X; try discriminate.
  destruct (access_mode t) eqn:T; try discriminate.
  destruct (sem_cast x (typeof rhs) t m) as [y|] eqn:Y; try discriminate.
  intro H. exists b, i, x, y. repeat split.
  - apply eval_Ederef. now apply expression_sound.
  - now apply expression_sound.
  - exact Y.
  - eapply assign_loc_value; eauto.
Qed.

Theorem execute_sound fuel ge e le m s le' m' out :
  execute fuel ge le m s = Some (le', m', out) ->
  exec_stmt function_entry2 ge e le m s E0 le' m' out.
Proof.
  revert le m s le' m' out.
  induction fuel as [|fuel IH]; intros le m s le' m' out H; [discriminate|].
  destruct s; simpl in H; try discriminate.
  - inversion H; subst. constructor.
  - destruct (store ge le m e0 e1) as [next|] eqn:W; try discriminate.
    destruct (store_sound ge e le m e0 e1 next W) as [b [ofs [x [y [A [B [C D]]]]]]].
    inversion H; subst.
    eapply exec_Sassign; eauto.
  - destruct (expression ge le m e0) as [x|] eqn:X; try discriminate.
    inversion H; subst. constructor. now apply expression_sound.
  - destruct (execute fuel ge le m s1) as [[[next_env next_mem] how]|] eqn:First;
      try discriminate.
    destruct how.
    + inversion H; subst. eapply exec_Sseq_2; [eapply IH; eauto|discriminate].
    + inversion H; subst. eapply exec_Sseq_2; [eapply IH; eauto|discriminate].
    + change E0 with (E0 ** E0). eapply exec_Sseq_1; eapply IH; eauto.
    + inversion H; subst. eapply exec_Sseq_2; [eapply IH; eauto|discriminate].
  - destruct (expression ge le m e0) as [x|] eqn:X; try discriminate.
    destruct (bool_val x (typeof e0) m) as [choice|] eqn:C; try discriminate.
    eapply exec_Sifthenelse.
    + eapply expression_sound. exact X.
    + exact C.
    + now apply IH.
  - destruct s2; try discriminate.
    destruct (execute fuel ge le m s1) as [[[next_env next_mem] how]|] eqn:Body;
      try discriminate.
    destruct how; try discriminate.
    + inversion H; subst. eapply exec_Sloop_stop1; [eapply IH; eauto|constructor].
    + change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      * eapply IH; eauto.
      * constructor.
      * constructor.
      * eapply IH; eauto.
    + inversion H; subst. eapply exec_Sloop_stop1; [eapply IH; eauto|constructor].
  - inversion H; subst. constructor.
  - destruct o as [a|].
    + destruct (expression ge le m a) as [x|] eqn:X; try discriminate.
      inversion H; subst. constructor. now apply expression_sound.
    + inversion H; subst. constructor.
Qed.

Print Assumptions expression_sound.
Print Assumptions execute_sound.
