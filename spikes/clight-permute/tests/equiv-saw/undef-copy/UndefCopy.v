(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes
  Clight ClightBigstep.
Require Import Permute.
Import ListNotations.

Definition probe_body := Ssequence (Sset i (reg j)) (ret 0).
Definition probe := {| fn_return := fn_return permute;
  fn_callconv := fn_callconv permute; fn_params := fn_params permute;
  fn_vars := fn_vars permute; fn_temps := fn_temps permute;
  fn_body := probe_body |}.
Definition args size da pa ta ua tr oa := [Vint size; da; pa; ta; ua; tr; oa].
Definition temps size da pa ta ua tr oa := PTree.set out oa
  (PTree.set trace tr (PTree.set used ua
  (PTree.set target ta (PTree.set permutation pa
  (PTree.set data da (PTree.set n (Vint size)
    (create_undef_temps (fn_temps probe)))))))).

Lemma entry ge m size da pa ta ua tr oa :
  function_entry2 ge probe (args size da pa ta ua tr oa) m empty_env
    (temps size da pa ta ua tr oa) m.
Proof.
  constructor.
  - constructor.
  - cbn [probe permute fn_params var_names map].
    repeat constructor; simpl; intuition discriminate.
  - unfold list_disjoint. cbn [probe permute fn_params fn_temps var_names map].
    intros x y Hx Hy.
    cbv [List.In fst n data permutation target used trace out i j top pos tmp depth] in Hx, Hy.
    intuition congruence.
  - constructor.
  - reflexivity.
Qed.

Theorem uninitialized_copy_returns_zero ge m size da pa ta ua tr oa :
  eval_funcall function_entry2 ge m (Internal probe)
    (args size da pa ta ua tr oa) E0 m (Vint Int.zero).
Proof.
  eapply eval_funcall_internal.
  - apply entry.
  - unfold probe; cbn [fn_body]. unfold probe_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. apply eval_Etempvar. reflexivity.
    + apply exec_Sreturn_some. apply eval_Econst_int.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.
Print Assumptions uninitialized_copy_returns_zero.

Definition prefixed := {| fn_return := fn_return permute;
  fn_callconv := fn_callconv permute; fn_params := fn_params permute;
  fn_vars := fn_vars permute; fn_temps := fn_temps permute;
  fn_body := Ssequence (Sset i (reg i)) (fn_body permute) |}.

Lemma prefixed_entry ge m size da pa ta ua tr oa :
  function_entry2 ge prefixed (args size da pa ta ua tr oa) m empty_env
    (temps size da pa ta ua tr oa) m.
Proof.
  constructor.
  - constructor.
  - cbn [prefixed permute fn_params var_names map].
    repeat constructor; simpl; intuition discriminate.
  - unfold list_disjoint. cbn [prefixed permute fn_params fn_temps var_names map].
    intros x y Hx Hy.
    cbv [List.In fst n data permutation target used trace out i j top pos tmp depth] in Hx, Hy.
    intuition congruence.
  - constructor.
  - reflexivity.
Qed.

Lemma initial_identity_copy ge m size da pa ta ua tr oa :
  exec_stmt function_entry2 ge empty_env (temps size da pa ta ua tr oa) m
    (Sset i (reg i)) E0 (temps size da pa ta ua tr oa) m Out_normal.
Proof.
  change (exec_stmt function_entry2 ge empty_env (temps size da pa ta ua tr oa) m
    (Sset i (reg i)) E0 (PTree.set i Vundef (temps size da pa ta ua tr oa)) m Out_normal).
  apply exec_Sset. apply eval_Etempvar. reflexivity.
Qed.

Theorem prefix_preserves_call ge m size da pa ta ua tr oa m' result :
  eval_funcall function_entry2 ge m (Internal permute)
    (args size da pa ta ua tr oa) E0 m' result ->
  eval_funcall function_entry2 ge m (Internal prefixed)
    (args size da pa ta ua tr oa) E0 m' result.
Proof.
  intro Run.
  inversion Run as [m0 f vargs t e le1 le2 m1 m2 out0 vres m3 Entry Body Result Free |]; subst.
  inversion Entry as [NoVars NoParams Separate Alloc Bind]; subst.
  cbn [permute fn_vars] in Alloc. inversion Alloc; subst.
  change (Some (temps size da pa ta ua tr oa) = Some le1) in Bind.
  injection Bind as Bound. subst le1.
  eapply eval_funcall_internal.
  - apply prefixed_entry.
  - cbn [prefixed fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply initial_identity_copy.
    + exact Body.
  - exact Result.
  - exact Free.
Qed.
Print Assumptions prefix_preserves_call.
