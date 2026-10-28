(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ModelArrays.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index FixedBlocks Fixed SearchBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Scan.
Context (layout : allocation_layout) (count value : nat)
    (desired flags : 'I_count -> nat) (bt bu : Values.block).
Hypothesis Bound : (count <= 1024)%coq_nat.
Hypotheses (CT : (count <= block_words layout bt)%coq_nat)
    (CU : (count <= block_words layout bu)%coq_nat).
Hypotheses (ValueUInt : uint (Z.of_nat value))
    (TargetUInt : forall x, uint (Z.of_nat (desired x)))
    (FlagsUInt : forall x, uint (Z.of_nat (flags x))).

Record search_registers (s : FusedS) : Prop := {
  search_size_local : Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count)));
  search_count_local : Maps.lookup (Name "wide.trip.count309") (locals s) = Some (index_value (Z.of_nat count));
  search_target_local : Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt));
  search_used_local : Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu));
  search_value_local : Maps.lookup (Anon 6) (locals s) = Some (word_value (Int.repr (Z.of_nat value)))
}.

Definition search_match index := andb (Nat.eqb (flags index) 0) (Nat.eqb value (desired index)).

Lemma search_probe from varargs c s (index : 'I_count) :
  cells_related layout c (fst s) -> array_at c bt (words desired) -> array_at c bu (words flags) ->
  search_registers s -> search_input from s (Z.of_nat (nat_of_ord index)) ->
  exists previous s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end77") s previous
      (if search_match index then Name "while.end93.split.loop.exit" else Name "if.end91") s' /\
    Maps.lookup (Name "indvars.iv306") (locals s') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    search_registers s' /\
    (forall id, ~ In id search_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Relation TargetArray Flags Registers Input.
  destruct Registers as [Size Count Target Used Value].
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  assert (FlagCompare : word_equal (Int.repr (Z.of_nat (flags index))) Int.zero = Nat.eqb (flags index) 0).
  { apply (natural_word_equal (flags index) 0);
      [apply FlagsUInt|unfold uint; change (0 <= 0 <= 4294967295); lia]. }
  assert (TargetCompare : word_equal (Int.repr (Z.of_nat value)) (Int.repr (Z.of_nat (desired index))) =
      Nat.eqb value (desired index)).
  { apply natural_word_equal; [exact ValueUInt|apply TargetUInt]. }
  pose (s1 := search_used_state s (Z.of_nat (nat_of_ord index))
    (block_address layout bu) (block_provenance layout bu) (Int.repr (Z.of_nat (flags index)))).
  assert (UsedRun : runs (denote_block (proj1_sig search_used) from varargs) s s1
      (inl (if Nat.eqb (flags index) 0 then Name "if.then81" else Name "if.end91"))).
  { rewrite <- FlagCompare. apply search_used_runs; try assumption; try lia.
    eapply related_load; [exact Relation|lia|].
    exact (proj1 (Flags _ _ (words_nth_error flags index))). }
  assert (Other1 : forall id, ~ In id search_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply search_used_other, Outside. }
  assert (Index1 : Maps.lookup (Name "indvars.iv306") (locals s1) =
      Some (index_value (Z.of_nat (nat_of_ord index)))).
  { apply search_used_index. }
  unfold search_match. destruct (Nat.eqb (flags index) 0) eqn:Free; cbn [andb].
  - pose (s2 := search_target_state s1 (Z.of_nat (nat_of_ord index))
      (block_address layout bt) (block_provenance layout bt)
      (Int.repr (Z.of_nat value)) (Int.repr (Z.of_nat (desired index)))).
    assert (TargetRun : runs (denote_block (proj1_sig search_target) (Name "if.end77") varargs) s1 s2
        (inl (if Nat.eqb value (desired index) then Name "while.end93.split.loop.exit" else Name "if.end91"))).
    { rewrite <- TargetCompare. apply search_target_runs; [lia|exact Index1| | |].
      - rewrite -> Other1 by (unfold search_modified; simpl; intuition discriminate). exact Target.
      - rewrite -> Other1 by (unfold search_modified; simpl; intuition discriminate). exact Value.
      - unfold s1. rewrite -> search_used_memory.
        eapply related_load; [exact Relation|lia|].
        exact (proj1 (TargetArray _ _ (words_nth_error desired index))). }
    assert (Other2 : forall id, ~ In id search_modified ->
        Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
    { intros id Outside. unfold s2. rewrite -> search_target_other by exact Outside. apply Other1, Outside. }
    exists (Name "if.then81"), s2. split.
    + unfold s2, s1. rewrite -> search_target_memory, search_used_memory. reflexivity.
    + split.
      * eapply steps_next; [exact (proj2_sig search_used)|exact UsedRun|].
        eapply steps_next; [exact (proj2_sig search_target)|exact TargetRun|constructor].
      * split.
        -- unfold s2, search_target_state. rewrite -> !lookup_local_other by discriminate. exact Index1.
        -- split; [|exact Other2]. constructor;
             rewrite -> Other2 by (unfold search_modified; simpl; intuition discriminate); assumption.
  - exists (Name "if.end77"), s1. split; [apply search_used_memory|]. split.
    + eapply steps_next; [exact (proj2_sig search_used)|exact UsedRun|constructor].
    + split; [exact Index1|]. split; [|exact Other1]. constructor;
        rewrite -> Other1 by (unfold search_modified; simpl; intuition discriminate); assumption.
Qed.

Lemma search_registers_frame s final : search_registers s ->
  (forall id, ~ In id search_modified -> Maps.lookup id (locals final) = Maps.lookup id (locals s)) ->
  search_registers final.
Proof.
  intros [N Count Target Used Value] Frame. constructor;
    rewrite -> Frame by (unfold search_modified; simpl; intuition discriminate); assumption.
Qed.

Theorem search_found varargs c (found : 'I_count) :
  array_at c bt (words desired) -> array_at c bu (words flags) ->
  search_match found = true ->
  forall remaining start from s,
  (start + remaining = nat_of_ord found)%coq_nat ->
  (forall x, (start <= nat_of_ord x)%coq_nat ->
    (nat_of_ord x < nat_of_ord found)%coq_nat -> search_match x = false) ->
  cells_related layout c (fst s) -> search_registers s -> search_input from s (Z.of_nat start) ->
  exists s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end77") s
      (Name "while.end93") (Name "if.end97") s' /\
    Maps.lookup (Name "v9.0.lcssa") (locals s') =
      Some (word_value (Int.repr (Z.of_nat (nat_of_ord found)))) /\
    search_registers s' /\
    (forall id, ~ In id search_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros TargetArray Flags Found remaining. induction remaining as [|remaining IH];
    intros start from s Sum Minimal Relation Registers Input.
  all: assert (FoundBound : (nat_of_ord found < count)%coq_nat)
    by exact (elimT ltP (ltn_ord found)).
  all: assert (K : (start < count)%coq_nat) by lia.
  all: pose index : 'I_count := Ordinal (introT ltP K).
  all: destruct (@search_probe from varargs c s index Relation TargetArray Flags Registers Input)
    as [previous [s1 [Memory1 [Probe [Index1 [Registers1 Other1]]]]]].
  - assert (Current : index = found) by (apply val_inj; change (start = nat_of_ord found); lia).
    rewrite -> Current, Found in Probe.
    assert (IndexFound : Maps.lookup (Name "indvars.iv306") (locals s1) =
        Some (index_value (Z.of_nat (nat_of_ord found)))).
    { rewrite <- Current. exact Index1. }
    pose (s2 := set_local s1 (Anon 10) (word_value (Int.repr (Z.of_nat (nat_of_ord found))))).
    pose (s3 := search_result_state s2 (Z.of_nat (nat_of_ord found)) (Z.of_nat count)).
    assert (Exit : runs (denote_block (proj1_sig search_exit) previous varargs) s1 s2
        (inl (Name "while.end93"))).
    { apply search_exit_runs; [lia|exact IndexFound]. }
    assert (InRange : (Z.of_nat (nat_of_ord found) =? Z.of_nat count) = false)
      by (apply Z.eqb_neq; lia).
    assert (Result : runs (denote_block (proj1_sig search_result)
        (Name "while.end93.split.loop.exit") varargs) s2 s3 (inl (Name "if.end97"))).
    { replace (Name "if.end97") with
        (if Z.of_nat (nat_of_ord found) =? Z.of_nat count then Name "cleanup" else Name "if.end97")
        by (rewrite -> InRange; reflexivity).
      apply search_result_runs; try lia.
      - apply lookup_local_same.
      - unfold s2. rewrite -> lookup_local_other by discriminate.
        exact (search_size_local _ Registers1). }
    assert (Other : forall id, ~ In id search_modified ->
        Maps.lookup id (locals s3) = Maps.lookup id (locals s)).
    { intros id Outside. unfold s3. rewrite -> search_result_other by exact Outside.
      unfold s2. rewrite -> lookup_local_other by
        (intro E; subst id; apply Outside; unfold search_modified; simpl; tauto).
      apply Other1, Outside. }
    exists s3. split.
    + unfold s3, s2. rewrite -> search_result_memory, memory_set_local. exact Memory1.
    + split.
      * eapply block_steps_append; [exact Probe|].
        eapply steps_next; [exact (proj2_sig search_exit)|exact Exit|].
        eapply steps_next; [exact (proj2_sig search_result)|exact Result|constructor].
      * split; [apply search_result_value|]. split; [|exact Other].
        exact (@search_registers_frame s s3 Registers Other).
  - assert (Miss : search_match index = false) by (apply Minimal; change (start <= start)%coq_nat ||
      change (start < nat_of_ord found)%coq_nat; lia).
    rewrite -> Miss in Probe.
    pose (s2 := search_next_state s1 (Z.of_nat start) (Z.of_nat count)).
    assert (More : (Z.of_nat start + 1 =? Z.of_nat count) = false)
      by (apply Z.eqb_neq; lia).
    assert (Next : runs (denote_block (proj1_sig search_next) previous varargs) s1 s2
        (inl (Name "if.end77"))).
    { replace (Name "if.end77") with
        (if Z.of_nat start + 1 =? Z.of_nat count then Name "while.end93" else Name "if.end77")
        by (rewrite -> More; reflexivity).
      apply search_next_runs; try lia; [exact Index1|exact (search_count_local _ Registers1)]. }
    assert (Memory2 : fst s2 = fst s).
    { unfold s2. rewrite -> search_next_memory. exact Memory1. }
    assert (Other2 : forall id, ~ In id search_modified ->
        Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
    { intros id Outside. unfold s2. rewrite -> search_next_other by exact Outside. apply Other1, Outside. }
    assert (Relation2 : cells_related layout c (fst s2)) by (rewrite -> Memory2; exact Relation).
    assert (Registers2 : search_registers s2) by
      exact (@search_registers_frame s s2 Registers Other2).
    assert (Input2 : search_input (Name "if.end91") s2 (Z.of_nat (S start))).
    { rewrite -> Nat2Z.inj_succ. replace (Z.succ (Z.of_nat start)) with (Z.of_nat start + 1) by lia.
      apply search_next_input. }
    destruct (IH (S start) (Name "if.end91") s2 ltac:(lia)
      ltac:(intros x Lower Upper; apply Minimal; lia) Relation2 Registers2 Input2)
      as [s' [Memory [Steps [Value [FinalRegs Other]]]]].
    exists s'. split; [rewrite -> Memory; exact Memory2|]. split.
    + eapply block_steps_append; [exact Probe|].
      eapply steps_next; [exact (proj2_sig search_next)|exact Next|exact Steps].
    + split; [exact Value|]. split; [exact FinalRegs|].
      intros id Outside. rewrite -> Other by exact Outside. apply Other2, Outside.
Qed.
End Scan.
