(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Arith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
Import ListNotations.

Definition instruction_step (isem : iMon unit) : Exec.t seq_state string unit :=
  FMon.cinterp (sequential_model_outcome None) isem.

Lemma exec_bind_single {St E A B} (program : Exec.t St E A)
    (next : A -> Exec.t St E B) initial middle value :
  program initial = Exec.make [(middle, value)] [] ->
  (program ≫= next) initial = next value middle.
Proof.
  intro Run. unfold mbind, Exec.mbind_inst. rewrite Run.
  cbn [Exec.res_mbind_inst foldr List.map Exec.merge].
  change (Exec.merge (next value middle) (Exec.make [] []) = next value middle).
  destruct (next value middle). unfold Exec.merge. cbn. now rewrite !app_nil_r.
Qed.

(* The transition is the actual ArchSem event interpreter. The condition on
   intermediate states prevents an early hit on the return address. *)
Inductive instruction_steps (isem : iMon unit) (term : terminationCondition 1) :
    nat -> seq_state -> seq_state -> Prop :=
| instructions_done state : instruction_steps isem term 0 state state
| instructions_next count initial middle final :
    ~ archState.is_terminated term (sst initial) ->
    instruction_step isem initial = Exec.make [(middle, tt)] [] ->
    instruction_steps isem term count middle final ->
    instruction_steps isem term (S count) initial final.

Lemma instruction_steps_append isem term count first middle last rest :
  instruction_steps isem term count first middle ->
  instruction_steps isem term rest middle last ->
  instruction_steps isem term (count + rest) first last.
Proof.
  intros Prefix Suffix. induction Prefix; cbn; [exact Suffix|].
  econstructor; eauto.
Qed.

(* One additional step is required to observe the final return address. *)
Lemma sequential_step_done isem term state origin fuel :
  archState.is_terminated term (sst state) ->
  exists proof,
    opModel.step (sequential_opmodel None isem) term origin fuel state =
      Exec.make [(state, Some (existT (sst state) proof))] [].
Proof.
  intro Terminated. cbn [sequential_opmodel opModel.step].
  erewrite exec_bind_single with (program := mget sst); [|reflexivity].
  destruct (decide (archState.is_terminated term (sst state))) as [Yes|No].
  - exists Yes. reflexivity.
  - contradiction.
Qed.

Lemma sequential_step_next isem term initial middle origin fuel :
  ~ archState.is_terminated term (sst initial) ->
  instruction_step isem initial = Exec.make [(middle, tt)] [] ->
  opModel.step (sequential_opmodel None isem) term origin fuel initial =
    Exec.make [(middle, None)] [].
Proof.
  intros Active Step. cbn [sequential_opmodel opModel.step].
  erewrite exec_bind_single with (program := mget sst); [|reflexivity].
  destruct (decide (archState.is_terminated term (sst initial))) as [Yes|No].
  - contradiction.
  - erewrite exec_bind_single; [reflexivity|exact Step].
Qed.

Theorem instruction_steps_run isem term count initial final origin :
  instruction_steps isem term count initial final ->
  archState.is_terminated term (sst final) ->
  exists proof,
    opModel.run (sequential_opmodel None isem) (S count) term origin initial =
      Exec.make [(final, existT (sst final) proof)] [].
Proof.
  intros Steps Terminated. induction Steps.
  - destruct (sequential_step_done isem term state origin 1 Terminated)
      as [Proof Step]. exists Proof.
    cbn [opModel.run].
    erewrite exec_bind_single by exact Step. reflexivity.
  - destruct (IHSteps Terminated) as [Final Run].
    exists Final.
    cbn [opModel.run].
    pose proof (sequential_step_next isem term initial middle origin
      (S (S count)) H H0) as Step.
    erewrite exec_bind_single by exact Step.
    exact Run.
Qed.

Theorem instruction_steps_model isem term count initial final :
  instruction_steps isem term count
    {| sst := initial; written := ∅ |} final ->
  archState.is_terminated term (sst final) ->
  exists proof,
    sequential_modelc None (S count) isem 1%nat term initial =
      Listset [archModel.Res.FinalState (sst final) proof].
Proof.
  intros Steps Terminated.
  destruct (instruction_steps_run isem term count _ final initial Steps Terminated)
    as [Proof Run].
  exists Proof.
  change (archModel.Res.from_exec
    (opModel.run (sequential_opmodel None isem) (S count) term initial)
    {| sst := initial; written := ∅ |} =
    Listset [archModel.Res.FinalState (sst final) Proof]).
  unfold archModel.Res.from_exec. rewrite Run. reflexivity.
Qed.

Print Assumptions instruction_steps_run.
Print Assumptions instruction_steps_model.

Definition return_condition (address : bv 64) : terminationCondition 1 :=
  [# [address]].

Lemma return_condition_iff address state :
  archState.is_terminated (return_condition address) (sst state) <->
  read_reg_seq_state rip state = Some address.
Proof.
  unfold archState.is_terminated, return_condition.
  split.
  - intro All. specialize (All 0%fin).
    change (Is_true (pc_terminated [address] (read_reg_seq_state rip state))) in All.
    unfold pc_terminated in All.
    destruct (read_reg_seq_state rip state) as [pc|] eqn:Read; [|contradiction].
    apply bool_decide_spec in All.
    apply list_elem_of_singleton in All. subst pc. reflexivity.
  - intros Read tid. inv_fin tid.
    change (Is_true (pc_terminated [address] (read_reg_seq_state rip state))).
    unfold pc_terminated. rewrite Read. apply bool_decide_spec.
    apply list_elem_of_singleton. reflexivity.
    intro impossible. inv_fin impossible.
Qed.

Lemma not_at_return address pc state :
  read_reg_seq_state rip state = Some pc -> pc <> address ->
  ~ archState.is_terminated (return_condition address) (sst state).
Proof.
  intros Read Different Terminated. apply return_condition_iff in Terminated.
  rewrite Read in Terminated. inversion Terminated. contradiction.
Qed.

Print Assumptions return_condition_iff.
