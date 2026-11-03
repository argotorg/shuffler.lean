(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Coq Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory.
Import ListNotations.
Open Scope Z_scope.

Lemma initialize_output ge le m b :
  PTree.get out le = Some (Vptr b Ptrofs.zero) ->
  writable_array m b 3 ->
  exists m1 m2 m3,
    store ge le m (cell out (lit 0)) (lit 0) = Some m1 /\
    store ge le m1 (cell out (lit 1)) (lit 0) = Some m2 /\
    store ge le m2 (cell out (lit 2)) (lit 0) = Some m3 /\
    array_at m3 b [0; 0; 0].
Proof.
  intros O W.
  assert (W0 : Mem.valid_access m Mint32 b 0 Writable) by (apply (W 0%nat); lia).
  destruct (Mem.valid_access_store m Mint32 b 0 (Vint (Int.repr 0)) W0) as [m1 S1].
  pose proof (writable_array_store m m1 b 3 b 0 _ W S1) as W1.
  assert (W4 : Mem.valid_access m1 Mint32 b 4 Writable) by (apply (W1 1%nat); lia).
  destruct (Mem.valid_access_store m1 Mint32 b 4 (Vint (Int.repr 0)) W4) as [m2 S2].
  pose proof (writable_array_store m1 m2 b 3 b 4 _ W1 S2) as W2.
  assert (W8 : Mem.valid_access m2 Mint32 b 8 Writable) by (apply (W2 2%nat); lia).
  destruct (Mem.valid_access_store m2 Mint32 b 8 (Vint (Int.repr 0)) W8) as [m3 S3].
  pose proof (writable_array_store m2 m3 b 3 b 8 _ W2 S3) as W3.
  assert (L0 : Mem.load Mint32 m3 b 0 = Some (Vint (Int.repr 0))).
  { rewrite (Mem.load_store_other Mint32 m2 b 8 _ m3 S3 Mint32 b 0)
      by (right; left; change (0 + 4 <= 8); lia).
    rewrite (Mem.load_store_other Mint32 m1 b 4 _ m2 S2 Mint32 b 0)
      by (right; left; change (0 + 4 <= 4); lia).
    exact (Mem.load_store_same Mint32 m b 0 _ m1 S1). }
  assert (L4 : Mem.load Mint32 m3 b 4 = Some (Vint (Int.repr 0))).
  { rewrite (Mem.load_store_other Mint32 m2 b 8 _ m3 S3 Mint32 b 4)
      by (right; left; change (4 + 4 <= 8); lia).
    exact (Mem.load_store_same Mint32 m1 b 4 _ m2 S2). }
  assert (L8 : Mem.load Mint32 m3 b 8 = Some (Vint (Int.repr 0)))
    by exact (Mem.load_store_same Mint32 m2 b 8 _ m3 S3).
  exists m1, m2, m3. split.
  - eapply cell_store with (b := b) (k := 0) (value := 0); eauto; reflexivity || lia.
  - split.
    + eapply cell_store with (b := b) (k := 1) (value := 0); eauto; reflexivity || lia.
    + split.
      * eapply cell_store with (b := b) (k := 2) (value := 0); eauto; reflexivity || lia.
      * intros [|[|[|k]]] v H; simpl in H; try discriminate.
        -- inversion H; subst. split; [exact L0|apply (W3 0%nat); lia].
        -- inversion H; subst. split; [exact L4|apply (W3 1%nat); lia].
        -- inversion H; subst. split; [exact L8|apply (W3 2%nat); lia].
        -- destruct k; discriminate.
Qed.

Lemma compare_size ge le m z :
  PTree.get n le = Some (Vint (Int.repr z)) ->
  0 <= z <= Int.max_unsigned ->
  expression ge le m (gt (reg n) (lit 1024)) =
    Some (Val.of_bool (Z.ltb 1024 z)).
Proof.
  intros N Z. cbn [expression gt reg lit]. rewrite N.
  change (Some (Val.of_bool (Int.ltu (Int.repr 1024) (Int.repr z))) =
    Some (Val.of_bool (Z.ltb 1024 z))).
  unfold Int.ltu. rewrite (Int.unsigned_repr z Z).
  rewrite Int.unsigned_repr by (change (0 <= 1024 <= 4294967295); lia).
  unfold Coqlib.zlt. destruct (Z_lt_dec 1024 z); destruct (Z.ltb_spec 1024 z);
    try lia; reflexivity.
Qed.

Lemma compare_empty ge le m :
  PTree.get n le = Some (Vint Int.zero) ->
  expression ge le m (Permute.eq (reg n) (lit 0)) = Some (Vint Int.one).
Proof.
  intro N. cbn [expression Permute.eq reg lit]. rewrite N.
  change (Some (Val.of_bool (Int.eq Int.zero Int.zero)) = Some (Vint Int.one)).
  rewrite Int.eq_true. reflexivity.
Qed.

Lemma exec_store ge e le m lhs rhs m' :
  store ge le m lhs rhs = Some m' ->
  exec_stmt function_entry2 ge e le m (Sassign lhs rhs) E0 le m' Out_normal.
Proof.
  intro H. apply (execute_sound 1). cbn [execute]. now rewrite H.
Qed.

Theorem permute_empty ge e le m b :
  PTree.get n le = Some (Vint Int.zero) ->
  PTree.get out le = Some (Vptr b Ptrofs.zero) ->
  writable_array m b 3 ->
  exists m',
    exec_stmt function_entry2 ge e le m (fn_body permute) E0 le m'
      (Out_return (Some (Vint Int.zero, u32))) /\
    array_at m' b [0; 0; 0].
Proof.
  intros N O W.
  destruct (initialize_output ge le m b O W)
    as [m1 [m2 [m3 [S1 [S2 [S3 A3]]]]]].
  exists m3. split; [|exact A3].
  cbn [permute fn_body seq fold_right].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le).
  - now apply exec_store.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le).
    + now apply exec_store.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := le).
      * now apply exec_store.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := le).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ apply expression_sound. apply (compare_size ge le m3 0 N).
              change (0 <= 0 <= 4294967295). lia.
           ++ reflexivity.
           ++ constructor.
        -- eapply exec_Sseq_2; [|discriminate].
           eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
           ++ apply expression_sound. now apply compare_empty.
           ++ reflexivity.
           ++ apply exec_Sreturn_some. constructor.
Qed.

Theorem permute_oversized ge e le m b z :
  PTree.get n le = Some (Vint (Int.repr z)) ->
  1024 < z <= Int.max_unsigned ->
  PTree.get out le = Some (Vptr b Ptrofs.zero) ->
  writable_array m b 3 ->
  exists m',
    exec_stmt function_entry2 ge e le m (fn_body permute) E0 le m'
      (Out_return (Some (Vint (Int.repr 2), u32))) /\
    array_at m' b [0; 0; 0].
Proof.
  intros N Z O W.
  destruct (initialize_output ge le m b O W)
    as [m1 [m2 [m3 [S1 [S2 [S3 A3]]]]]].
  exists m3. split; [|exact A3].
  cbn [permute fn_body seq fold_right].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le).
  - now apply exec_store.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le).
    + now apply exec_store.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := le).
      * now apply exec_store.
      * eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- apply expression_sound. rewrite (compare_size ge le m3 z N) by lia.
           assert (B : (1024 <? z) = true) by (apply Z.ltb_lt; lia).
           rewrite B. reflexivity.
        -- reflexivity.
        -- apply exec_Sreturn_some. constructor.
Qed.

Print Assumptions permute_empty.
Print Assumptions permute_oversized.
