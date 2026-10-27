(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Bool ZArith.
From compcert Require Import AST Ctypes Clight.
Require Import AssignmentCheck.
Import ListNotations.
Open Scope Z_scope.

(* The path relation ignores expression values and memory. Either branch
   may be selected. The Boolean records whether each reached temporary
   read follows a parameter binding or assignment. It can be false. *)
Inductive exit_kind := Finished | Broke | Returned.

Inductive assignment_path : statement -> assigned -> assigned -> exit_kind -> bool -> Prop :=
| path_skip ids : assignment_path Sskip ids ids Finished true
| path_set ids id value :
    assignment_path (Sset id value) ids (id :: ids) Finished (uses ids value)
| path_store ids address ty value :
    assignment_path (Sassign (Ederef address ty) value) ids ids Finished
      (uses ids address && uses ids value)
| path_sequence first second initial middle final kind a b :
    assignment_path first initial middle Finished a ->
    assignment_path second middle final kind b ->
    assignment_path (Ssequence first second) initial final kind (a && b)
| path_sequence_stop first second initial final kind safe :
    kind <> Finished ->
    assignment_path first initial final kind safe ->
    assignment_path (Ssequence first second) initial final kind safe
| path_yes condition yes no initial final kind safe :
    assignment_path yes initial final kind safe ->
    assignment_path (Sifthenelse condition yes no) initial final kind
      (uses initial condition && safe)
| path_no condition yes no initial final kind safe :
    assignment_path no initial final kind safe ->
    assignment_path (Sifthenelse condition yes no) initial final kind
      (uses initial condition && safe)
| path_loop_break body initial final safe :
    assignment_path body initial final Broke safe ->
    assignment_path (Sloop body Sskip) initial final Finished safe
| path_loop_return body initial final safe :
    assignment_path body initial final Returned safe ->
    assignment_path (Sloop body Sskip) initial final Returned safe
| path_loop_next body initial middle final kind a b :
    assignment_path body initial middle Finished a ->
    assignment_path (Sloop body Sskip) middle final kind b ->
    assignment_path (Sloop body Sskip) initial final kind (a && b)
| path_break ids : assignment_path Sbreak ids ids Broke true
| path_return ids value :
    assignment_path (Sreturn (Some value)) ids ids Returned (uses ids value).

Definition guarantees (paths : exits) (kind : exit_kind) (actual : assigned) : Prop :=
  match kind with
  | Finished => match normal paths with Some ids => incl ids actual | None => False end
  | Broke => match broken paths with Some ids => incl ids actual | None => False end
  | Returned => True
  end.

Lemma uses_monotone small large value :
  incl small large -> uses small value = true -> uses large value = true.
Proof.
  intros Included. induction value; cbn; intro H; try discriminate; try reflexivity.
  - apply member_spec. apply Included. now apply member_spec.
  - now apply IHvalue.
  - apply andb_true_iff in H as [A B]. apply andb_true_iff. split; auto.
Qed.

Lemma join_left a b ids actual :
  a = Some ids -> incl ids actual ->
  match join a b with Some result => incl result actual | None => False end.
Proof.
  intros -> Bound. destruct b as [other|]; cbn; [|exact Bound].
  intros id H. apply filter_In in H as [H _]. now apply Bound.
Qed.

Lemma join_right a b ids actual :
  b = Some ids -> incl ids actual ->
  match join a b with Some result => incl result actual | None => False end.
Proof.
  intros -> Bound. destruct a as [other|]; cbn; [|exact Bound].
  intros id H. apply filter_In in H as [_ H]. apply Bound. now apply member_spec.
Qed.

Definition merged a b := {| normal := join (normal a) (normal b);
                            broken := join (broken a) (broken b) |}.
Definition sequenced a b := {| normal := normal b;
                               broken := join (broken a) (broken b) |}.

Lemma merge_left a b kind actual :
  guarantees a kind actual -> guarantees (merged a b) kind actual.
Proof.
  destruct kind; cbn [guarantees merged]; try tauto.
  - destruct (normal a) as [ids|] eqn:A; try contradiction.
    intro Bound. eapply join_left; eauto.
  - destruct (broken a) as [ids|] eqn:A; try contradiction.
    intro Bound. eapply join_left; eauto.
Qed.

Lemma merge_right a b kind actual :
  guarantees b kind actual -> guarantees (merged a b) kind actual.
Proof.
  destruct kind; cbn [guarantees merged]; try tauto.
  - destruct (normal b) as [ids|] eqn:B; try contradiction.
    intro Bound. eapply join_right; eauto.
  - destruct (broken b) as [ids|] eqn:B; try contradiction.
    intro Bound. eapply join_right; eauto.
Qed.

Lemma sequence_right a b kind actual :
  guarantees b kind actual -> guarantees (sequenced a b) kind actual.
Proof.
  destruct kind; cbn [guarantees sequenced]; try tauto.
  destruct (broken b) as [ids|] eqn:B; try contradiction.
  intro Bound. eapply join_right; eauto.
Qed.

Lemma sequence_left a b kind actual :
  kind <> Finished -> guarantees a kind actual -> guarantees (sequenced a b) kind actual.
Proof.
  destruct kind; cbn [guarantees sequenced]; try tauto.
  intros _ H. destruct (broken a) as [ids|] eqn:A; try contradiction.
  eapply join_left; eauto.
Qed.

Lemma path_preserves_assignments s initial final kind safe :
  assignment_path s initial final kind safe -> incl initial final.
Proof.
  intro Run. induction Run; try apply incl_refl; try assumption.
  - intros x H. right. exact H.
  - eapply incl_tran; eauto.
  - eapply incl_tran; eauto.
Qed.

Theorem complete_path_safe s initial final kind safe :
  assignment_path s initial final kind safe ->
  forall known paths, check known s = Some paths -> incl known initial ->
  safe = true /\ guarantees paths kind final.
Proof.
  intro Run. induction Run; intros known paths Checked Bound; cbn [check] in Checked.
  - inversion Checked; subst. split; [reflexivity|exact Bound].
  - destruct (uses known value) eqn:U; try discriminate.
    inversion Checked; subst. split.
    + eapply uses_monotone; eauto.
    + intros x [E|H]; [now left|right; now apply Bound].
  - destruct (uses known address && uses known value) eqn:U; try discriminate.
    inversion Checked; subst. split; [|exact Bound].
    apply andb_true_iff in U as [A B]. apply andb_true_iff. split;
      eapply uses_monotone; eauto.
  - destruct (check known first) as [before|] eqn:F; try discriminate.
    destruct (IHRun1 known before F Bound) as [SafeFirst ExitFirst].
    destruct (normal before) as [next|] eqn:N.
    + destruct (check next second) as [after|] eqn:S; try discriminate.
      inversion Checked; subst paths.
      unfold guarantees in ExitFirst. rewrite N in ExitFirst.
      destruct (IHRun2 next after S ExitFirst) as [SafeSecond ExitSecond].
      split; [now rewrite SafeFirst, SafeSecond|].
      now apply sequence_right.
    + unfold guarantees in ExitFirst. rewrite N in ExitFirst. contradiction.
  - destruct (check known first) as [before|] eqn:F; try discriminate.
    destruct (IHRun known before F Bound) as [SafeFirst ExitFirst].
    destruct (normal before) as [next|] eqn:N.
    + destruct (check next second) as [after|] eqn:S; try discriminate.
      inversion Checked; subst paths. split; [exact SafeFirst|].
      apply sequence_left; assumption.
    + inversion Checked; subst paths. now split.
  - destruct (uses known condition) eqn:C; try discriminate.
    destruct (check known yes) as [a|] eqn:Y; try discriminate.
    destruct (check known no) as [b|] eqn:N; try discriminate.
    inversion Checked; subst paths.
    destruct (IHRun known a Y Bound) as [SafeBranch ExitBranch].
    split.
    + rewrite (uses_monotone known initial condition Bound C), SafeBranch. reflexivity.
    + now apply merge_left.
  - destruct (uses known condition) eqn:C; try discriminate.
    destruct (check known yes) as [a|] eqn:Y; try discriminate.
    destruct (check known no) as [b|] eqn:N; try discriminate.
    inversion Checked; subst paths.
    destruct (IHRun known b N Bound) as [SafeBranch ExitBranch].
    split.
    + rewrite (uses_monotone known initial condition Bound C), SafeBranch. reflexivity.
    + now apply merge_right.
  - destruct (check known body) as [body_paths|] eqn:B; try discriminate.
    inversion Checked; subst paths.
    exact (IHRun known body_paths B Bound).
  - destruct (check known body) as [body_paths|] eqn:B; try discriminate.
    inversion Checked; subst paths.
    exact (IHRun known body_paths B Bound).
  - destruct (check known body) as [body_paths|] eqn:B; try discriminate.
    destruct (IHRun1 known body_paths B Bound) as [SafeBody ExitBody].
    assert (Later : incl known middle).
    { eapply incl_tran; [exact Bound|]. eapply path_preserves_assignments. exact Run1. }
    assert (Again : check known (Sloop body Sskip) = Some paths).
    { cbn [check]. now rewrite B. }
    destruct (IHRun2 known paths Again Later) as [SafeLoop ExitLoop].
    split; [now rewrite SafeBody, SafeLoop|exact ExitLoop].
  - inversion Checked; subst. split; [reflexivity|exact Bound].
  - destruct (uses known value) eqn:U; try discriminate.
    inversion Checked; subst. split; [eapply uses_monotone; eauto|exact I].
Qed.

Print Assumptions complete_path_safe.

(* Finite prefixes do not require the enclosing statement or loop to
   terminate. A completed inner statement can lead to another prefix. *)
Inductive assignment_prefix : statement -> assigned -> bool -> Prop :=
| prefix_empty s ids : assignment_prefix s ids true
| prefix_complete s initial final kind safe :
    assignment_path s initial final kind safe -> assignment_prefix s initial safe
| prefix_first first second initial safe :
    assignment_prefix first initial safe ->
    assignment_prefix (Ssequence first second) initial safe
| prefix_second first second initial middle a b :
    assignment_path first initial middle Finished a ->
    assignment_prefix second middle b ->
    assignment_prefix (Ssequence first second) initial (a && b)
| prefix_yes condition yes no initial safe :
    assignment_prefix yes initial safe ->
    assignment_prefix (Sifthenelse condition yes no) initial (uses initial condition && safe)
| prefix_no condition yes no initial safe :
    assignment_prefix no initial safe ->
    assignment_prefix (Sifthenelse condition yes no) initial (uses initial condition && safe)
| prefix_body body initial safe :
    assignment_prefix body initial safe ->
    assignment_prefix (Sloop body Sskip) initial safe
| prefix_iteration body initial middle a b :
    assignment_path body initial middle Finished a ->
    assignment_prefix (Sloop body Sskip) middle b ->
    assignment_prefix (Sloop body Sskip) initial (a && b).

Theorem prefix_safe s initial safe :
  assignment_prefix s initial safe ->
  forall known paths, check known s = Some paths -> incl known initial -> safe = true.
Proof.
  intro Prefix.
  induction Prefix as [s initial|s initial final kind safe Run|
    first second initial safe Prefix IH|
    first second initial middle a b Run Prefix IH|
    condition yes no initial safe Prefix IH|
    condition yes no initial safe Prefix IH|
    body initial safe Prefix IH|
    body initial middle a b Run Prefix IH]; intros known paths Checked Bound.
  - reflexivity.
  - exact (proj1 (complete_path_safe s initial final kind safe Run known paths Checked Bound)).
  - cbn [check] in Checked.
    destruct (check known first) as [before|] eqn:F; try discriminate.
    eapply IH; eauto.
  - cbn [check] in Checked.
    destruct (check known first) as [before|] eqn:F; try discriminate.
    destruct (complete_path_safe first initial middle Finished a Run known before F Bound)
      as [SafeFirst ExitFirst].
    destruct (normal before) as [next|] eqn:N.
    + destruct (check next second) as [after|] eqn:S; try discriminate.
      unfold guarantees in ExitFirst. rewrite N in ExitFirst.
      rewrite SafeFirst, (IH next after S ExitFirst). reflexivity.
    + unfold guarantees in ExitFirst. rewrite N in ExitFirst. contradiction.
  - cbn [check] in Checked.
    destruct (uses known condition) eqn:C; try discriminate.
    destruct (check known yes) as [a|] eqn:Y; try discriminate.
    destruct (check known no) as [b|] eqn:N; try discriminate.
    rewrite (uses_monotone known initial condition Bound C), (IH known a Y Bound).
    reflexivity.
  - cbn [check] in Checked.
    destruct (uses known condition) eqn:C; try discriminate.
    destruct (check known yes) as [a|] eqn:Y; try discriminate.
    destruct (check known no) as [b|] eqn:N; try discriminate.
    rewrite (uses_monotone known initial condition Bound C), (IH known b N Bound).
    reflexivity.
  - cbn [check] in Checked.
    destruct (check known body) as [body_paths|] eqn:B; try discriminate.
    eapply IH; eauto.
  - assert (Original := Checked). cbn [check] in Checked.
    destruct (check known body) as [body_paths|] eqn:B; try discriminate.
    destruct (complete_path_safe body initial middle Finished a Run known body_paths B Bound)
      as [SafeBody ExitBody].
    assert (Later : incl known middle).
    { eapply incl_tran; [exact Bound|]. eapply path_preserves_assignments. exact Run. }
    rewrite SafeBody, (IH known paths Original Later). reflexivity.
Qed.

Theorem checked_function_prefix fn safe :
  check_function fn = true ->
  assignment_prefix (fn_body fn) (map fst (fn_params fn)) safe -> safe = true.
Proof.
  unfold check_function.
  destruct (check (map fst (fn_params fn)) (fn_body fn)) as [paths|] eqn:C;
    try discriminate.
  intros _ Prefix. eapply prefix_safe; [exact Prefix|exact C|apply incl_refl].
Qed.

Corollary permute_prefix_safe safe :
  assignment_prefix (fn_body Permute.permute) (map fst (fn_params Permute.permute)) safe ->
  safe = true.
Proof. apply checked_function_prefix. exact permute_passes_assignment_check. Qed.

Example unsafe_copy_has_a_bad_prefix :
  assignment_prefix
    (Ssequence (Permute.set Permute.i (Permute.reg Permute.i)) (fn_body Permute.permute))
    (map fst (fn_params Permute.permute)) false.
Proof.
  apply prefix_first. eapply prefix_complete. apply path_set.
Qed.

(* These witnesses check that the path model includes the branches and
   loop boundaries used by the proof. They are control paths, not C tests. *)
Definition parameters := map fst (fn_params Permute.permute).
Definition parameter_zero := Permute.eq (Permute.reg Permute.n) (Permute.lit 0).

Example unassigned_else_path_is_represented :
  assignment_prefix (Ssequence
    (Sifthenelse parameter_zero (Permute.set Permute.i (Permute.lit 1)) Sskip)
    (Sreturn (Some (Permute.reg Permute.i)))) parameters false.
Proof.
  eapply prefix_second with (middle := parameters) (a := true) (b := false).
  - exact (path_no _ _ _ _ _ _ true (path_skip parameters)).
  - eapply prefix_complete. exact (path_return parameters (Permute.reg Permute.i)).
Qed.

Example zero_iteration_path_is_represented :
  assignment_prefix (Ssequence
    (Permute.loop parameter_zero (Permute.set Permute.i (Permute.lit 1)))
    (Sreturn (Some (Permute.reg Permute.i)))) parameters false.
Proof.
  eapply prefix_second with (middle := parameters) (a := true) (b := false).
  - apply path_loop_break. eapply path_sequence_stop; [discriminate|].
    exact (path_no _ _ _ _ _ _ true (path_break parameters)).
  - eapply prefix_complete. exact (path_return parameters (Permute.reg Permute.i)).
Qed.

Example inner_break_reaches_the_next_statement :
  assignment_prefix (Sloop (Ssequence (Sloop Sbreak Sskip)
    (Permute.set Permute.i (Permute.reg Permute.j))) Sskip) parameters false.
Proof.
  apply prefix_body.
  eapply prefix_second with (middle := parameters) (a := true) (b := false).
  - apply path_loop_break. apply path_break.
  - eapply prefix_complete. exact (path_set parameters Permute.i (Permute.reg Permute.j)).
Qed.

Example later_iteration_path_is_represented :
  assignment_prefix (Sloop
    (Sifthenelse parameter_zero (Permute.set Permute.i (Permute.reg Permute.j)) Sskip)
    Sskip) parameters false.
Proof.
  eapply prefix_iteration with (middle := parameters) (a := true) (b := false).
  - exact (path_no _ _ _ _ _ _ true (path_skip parameters)).
  - apply prefix_body. apply prefix_yes with (safe := false). eapply prefix_complete.
    exact (path_set parameters Permute.i (Permute.reg Permute.j)).
Qed.

Print Assumptions prefix_safe.
Print Assumptions checked_function_prefix.
Print Assumptions permute_prefix_safe.
