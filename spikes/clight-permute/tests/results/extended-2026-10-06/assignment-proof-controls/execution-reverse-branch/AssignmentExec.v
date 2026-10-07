(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Bool.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Events Memory Values Maps.
Require Import AssignmentCheck AssignmentSound.

(* This is a statement-shape condition, independent of assignment safety.
   In particular, unsafe temporary reads are still represented. *)
Inductive supported : statement -> Prop :=
| shape_skip : supported Sskip
| shape_set id value : supported (Sset id value)
| shape_store address ty value : supported (Sassign (Ederef address ty) value)
| shape_sequence first second :
    supported first -> supported second -> supported (Ssequence first second)
| shape_if condition yes no :
    supported yes -> supported no -> supported (Sifthenelse condition yes no)
| shape_loop body : supported body -> supported (Sloop body Sskip)
| shape_break : supported Sbreak
| shape_return value : supported (Sreturn (Some value)).

Theorem permute_has_supported_shape : supported (fn_body Permute.permute).
Proof. repeat constructor. Qed.

Definition outcome_kind (out : outcome) : option exit_kind :=
  match out with
  | Out_normal => Some Finished
  | Out_break => Some Broke
  | Out_return _ => Some Returned
  | Out_continue => None
  end.

Section Execution.
Variable function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.

(* The annotation uses the actual Clight expression evaluation and branch
   decision. Compound rules retain the intermediate environments, memories,
   outcomes and traces. No safety premise is imposed by this relation. *)
Inductive recorded_exec : env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome ->
    assigned -> assigned -> bool -> Prop :=
| record_skip e le m ids :
    recorded_exec e le m Sskip E0 le m Out_normal ids ids true
| record_set e le m id value v ids :
    eval_expr ge e le m value v ->
    recorded_exec e le m (Sset id value) E0 (PTree.set id v le) m Out_normal
      ids (id :: ids) (uses ids value)
| record_store e le m address ty value loc ofs bf v2 v m' ids :
    eval_lvalue ge e le m (Ederef address ty) loc ofs bf ->
    eval_expr ge e le m value v2 ->
    sem_cast v2 (typeof value) ty m = Some v ->
    assign_loc ge ty m loc ofs bf v m' ->
    recorded_exec e le m (Sassign (Ederef address ty) value) E0 le m' Out_normal
      ids ids (uses ids address && uses ids value)
| record_sequence e le m first second t1 le1 m1 t2 le2 m2 out initial middle final a b :
    recorded_exec e le m first t1 le1 m1 Out_normal initial middle a ->
    recorded_exec e le1 m1 second t2 le2 m2 out middle final b ->
    recorded_exec e le m (Ssequence first second) (t1 ** t2) le2 m2 out
      initial final (a && b)
| record_sequence_stop e le m first second t le' m' out initial final safe :
    out <> Out_normal ->
    recorded_exec e le m first t le' m' out initial final safe ->
    recorded_exec e le m (Ssequence first second) t le' m' out initial final safe
| record_if e le m condition yes no v choice t le' m' out initial final safe :
    eval_expr ge e le m condition v ->
    bool_val v (typeof condition) m = Some choice ->
    recorded_exec e le m (if choice then no else yes) t le' m' out initial final safe ->
    recorded_exec e le m (Sifthenelse condition yes no) t le' m' out
      initial final (uses initial condition && safe)
| record_loop_break e le m body t le' m' initial final safe :
    recorded_exec e le m body t le' m' Out_break initial final safe ->
    recorded_exec e le m (Sloop body Sskip) t le' m' Out_normal initial final safe
| record_loop_return e le m body t le' m' value initial final safe :
    recorded_exec e le m body t le' m' (Out_return value) initial final safe ->
    recorded_exec e le m (Sloop body Sskip) t le' m' (Out_return value) initial final safe
| record_loop_next e le m body t1 le1 m1 t2 le2 m2 out initial middle final a b :
    recorded_exec e le m body t1 le1 m1 Out_normal initial middle a ->
    recorded_exec e le1 m1 (Sloop body Sskip) t2 le2 m2 out middle final b ->
    recorded_exec e le m (Sloop body Sskip) (t1 ** E0 ** t2) le2 m2 out
      initial final (a && b)
| record_break e le m ids :
    recorded_exec e le m Sbreak E0 le m Out_break ids ids true
| record_return e le m value v ids :
    eval_expr ge e le m value v ->
    recorded_exec e le m (Sreturn (Some value)) E0 le m (Out_return (Some (v, typeof value)))
      ids ids (uses ids value).

Theorem recorded_erases e le m s t le' m' out initial final safe :
  recorded_exec e le m s t le' m' out initial final safe ->
  exec_stmt function_entry ge e le m s t le' m' out.
Proof.
  intro Run. induction Run.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply exec_Sseq_2; eauto.
  - eapply exec_Sifthenelse; eauto.
  - eapply exec_Sloop_stop1; [exact IHRun|constructor].
  - eapply exec_Sloop_stop1; [exact IHRun|constructor].
  - eapply exec_Sloop_loop; [exact IHRun1|constructor|constructor|exact IHRun2].
  - constructor.
  - econstructor; eauto.
Qed.

Theorem recorded_path e le m s t le' m' out initial final safe :
  recorded_exec e le m s t le' m' out initial final safe ->
  exists kind, outcome_kind out = Some kind /\ assignment_path s initial final kind safe.
Proof.
  intro Run. induction Run.
  - exists Finished. split; [reflexivity|constructor].
  - exists Finished. split; [reflexivity|constructor].
  - exists Finished. split; [reflexivity|constructor].
  - destruct IHRun1 as [kind1 [Kind1 Path1]]. cbn in Kind1. inversion Kind1; subst kind1.
    destruct IHRun2 as [kind [Kind Path]]. exists kind. split; [exact Kind|].
    econstructor; eauto.
  - destruct IHRun as [kind [Kind Path]]. exists kind. split; [exact Kind|].
    eapply path_sequence_stop; [|exact Path].
    destruct out; cbn in Kind; try discriminate; inversion Kind; congruence.
  - destruct IHRun as [kind [Kind Path]]. exists kind. split; [exact Kind|].
    destruct choice; [apply path_yes|apply path_no]; exact Path.
  - destruct IHRun as [kind [Kind Path]]. cbn in Kind. inversion Kind; subst kind.
    exists Finished. split; [reflexivity|]. now apply path_loop_break.
  - destruct IHRun as [kind [Kind Path]]. cbn in Kind. inversion Kind; subst kind.
    exists Returned. split; [reflexivity|]. now apply path_loop_return.
  - destruct IHRun1 as [kind1 [Kind1 Path1]]. cbn in Kind1. inversion Kind1; subst kind1.
    destruct IHRun2 as [kind [Kind Path]]. exists kind. split; [exact Kind|].
    eapply path_loop_next; eauto.
  - exists Broke. split; [reflexivity|constructor].
  - exists Returned. split; [reflexivity|constructor].
Qed.

Lemma recorded_no_continue e le m s t le' m' out initial final safe :
  recorded_exec e le m s t le' m' out initial final safe -> out <> Out_continue.
Proof.
  intro Run. destruct (recorded_path _ _ _ _ _ _ _ _ _ _ _ Run) as [kind [Kind _]].
  intro Equal. subst out. discriminate.
Qed.

Theorem execution_recorded e le m s t le' m' out :
  exec_stmt function_entry ge e le m s t le' m' out ->
  supported s -> forall initial,
  exists final safe, recorded_exec e le m s t le' m' out initial final safe.
Proof.
  intro Run. induction Run; intros Shape initial; inversion Shape; subst.
  - do 2 eexists. constructor.
  - do 2 eexists. econstructor; eauto.
  - do 2 eexists. econstructor; eauto.
  - assert (First : supported s1) by assumption.
    assert (Second : supported s2) by assumption.
    destruct (IHRun1 First initial) as [middle [a A]].
    destruct (IHRun2 Second middle) as [final [b B]].
    exists final, (a && b). econstructor; eauto.
  - assert (First : supported s1) by assumption.
    destruct (IHRun First initial) as [final [safe A]].
    exists final, safe. eapply record_sequence_stop; eauto.
  - assert (Selected : supported (if b then s1 else s2)) by (destruct b; assumption).
    destruct (IHRun Selected initial) as [final [safe A]].
    exists final, (uses initial a && safe). eapply record_if; eauto.
  - do 2 eexists. econstructor; eauto.
  - do 2 eexists. constructor.
  - assert (Body : supported s1) by assumption.
    destruct (IHRun Body initial) as [final [safe A]].
    inversion H; subst.
    + exists final, safe. now apply record_loop_break.
    + exists final, safe. now apply record_loop_return.
  - inversion Run2; subst. inversion H0.
  - assert (Body : supported s1) by assumption.
    destruct (IHRun1 Body initial) as [middle [a A]].
    assert (Normal : out1 = Out_normal).
    { inversion H; subst out1; [reflexivity|]. exfalso.
      eapply recorded_no_continue; [exact A|reflexivity]. }
    subst out1. inversion Run2; subst.
    destruct (IHRun3 Shape middle) as [final [b B]].
    exists final, (a && b). eapply record_loop_next; eauto.
Qed.

Theorem checked_execution_safe e le m s t le' m' out initial final safe paths :
  check initial s = Some paths ->
  recorded_exec e le m s t le' m' out initial final safe -> safe = true.
Proof.
  intros Checked Run.
  destruct (recorded_path _ _ _ _ _ _ _ _ _ _ _ Run) as [kind [_ Path]].
  exact (proj1 (complete_path_safe _ _ _ _ _ Path initial paths Checked (incl_refl _))).
Qed.

Theorem checked_supported_execution e le m s t le' m' out initial paths :
  check initial s = Some paths -> supported s ->
  exec_stmt function_entry ge e le m s t le' m' out ->
  exists final, recorded_exec e le m s t le' m' out initial final true.
Proof.
  intros Checked Shape Run.
  destruct (execution_recorded _ _ _ _ _ _ _ _ Run Shape initial) as [final [safe Record]].
  pose proof (checked_execution_safe _ _ _ _ _ _ _ _ _ _ _ _ Checked Record) as Safe.
  subst safe. now exists final.
Qed.

Theorem checked_function_execution fn e le m t le' m' out :
  check_function fn = true -> supported (fn_body fn) ->
  exec_stmt function_entry ge e le m (fn_body fn) t le' m' out ->
  exists final, recorded_exec e le m (fn_body fn) t le' m' out
    (map fst (fn_params fn)) final true.
Proof.
  unfold check_function.
  destruct (check (map fst (fn_params fn)) (fn_body fn)) as [paths|] eqn:Checked;
    try discriminate.
  intros _ Shape Run. eapply checked_supported_execution; eauto.
Qed.

Corollary permute_execution_safe e le m t le' m' out :
  exec_stmt function_entry ge e le m (fn_body Permute.permute) t le' m' out ->
  exists final, recorded_exec e le m (fn_body Permute.permute) t le' m' out
    (map fst (fn_params Permute.permute)) final true.
Proof.
  apply checked_function_execution.
  - exact permute_passes_assignment_check.
  - exact permute_has_supported_shape.
Qed.

Example unsafe_self_copy_execution_is_recorded e le m :
  PTree.get Permute.i le = Some Vundef ->
  recorded_exec e le m (Permute.set Permute.i (Permute.reg Permute.i)) E0
    (PTree.set Permute.i Vundef le) m Out_normal
    parameters (Permute.i :: parameters) false.
Proof.
  intro Read. change (recorded_exec e le m
    (Sset Permute.i (Permute.reg Permute.i)) E0
    (PTree.set Permute.i Vundef le) m Out_normal parameters
    (Permute.i :: parameters) (uses parameters (Permute.reg Permute.i))).
  apply record_set. constructor. exact Read.
Qed.

End Execution.

Print Assumptions recorded_erases.
Print Assumptions recorded_path.
Print Assumptions execution_recorded.
Print Assumptions checked_execution_safe.
Print Assumptions checked_supported_execution.
Print Assumptions checked_function_execution.
Print Assumptions permute_execution_safe.
Print Assumptions permute_has_supported_shape.
