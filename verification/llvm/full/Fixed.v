(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightExchangeSuccess ModelArrays ClightNormalize.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index FixedBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma natural_word_equal x y : uint (Z.of_nat x) -> uint (Z.of_nat y) ->
  word_equal (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y)) = Nat.eqb x y.
Proof.
  intros X Y. unfold word_equal. rewrite -> !Int.unsigned_repr by assumption.
  destruct (Nat.eqb_spec x y); destruct (Z.eqb_spec (Z.of_nat x) (Z.of_nat y));
    try lia; reflexivity.
Qed.

Section Pass.
Context (layout : allocation_layout) (count : nat)
    (source desired : 'I_count -> nat) (bd bt bp bu : Values.block).
Hypothesis Bound : (count <= 1024)%coq_nat.
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (TP : bt <> bp) (TU : bt <> bu) (PU : bp <> bu).
Hypotheses (CD : (count <= block_words layout bd)%coq_nat)
    (CT : (count <= block_words layout bt)%coq_nat)
    (CP : (count <= block_words layout bp)%coq_nat)
    (CU : (count <= block_words layout bu)%coq_nat).
Hypotheses (SourceUInt : forall x, uint (Z.of_nat (source x)))
    (TargetUInt : forall x, uint (Z.of_nat (desired x))).

Record fixed_arrays (assignment : 'I_count -> nat) (flags : list Z) (c : Mem.mem) : Prop := {
  fixed_data : array_at c bd (words source);
  fixed_target : array_at c bt (words desired);
  fixed_permutation : array_at c bp (words assignment);
  fixed_used : array_at c bu flags
}.

Record fixed_registers (s : FusedS) : Prop := {
  fixed_size_local : Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count)));
  fixed_count_local : Maps.lookup (Name "wide.trip.count304") (locals s) = Some (index_value (Z.of_nat count));
  fixed_data_local : Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd));
  fixed_target_local : Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt));
  fixed_permutation_local : Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp));
  fixed_used_local : Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu))
}.

Definition fixed_frame c final := forall other values, other <> bp -> other <> bu ->
  array_at c other values -> array_at final other values.

Lemma fixed_branch from varargs c s (index : 'I_count) assignment flags choice :
  cells_related layout c (fst s) -> fixed_arrays assignment flags c -> fixed_registers s ->
  fixed_input from s (Z.of_nat (nat_of_ord index)) ->
  word_equal (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index))) = choice ->
  exists c' s', cells_related layout c' (fst s') /\
    fixed_arrays (if choice then update_value assignment index (nat_of_ord index) else assignment) flags c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43") s
      (fixed_from choice) (Name "if.end57") s' /\
    Maps.lookup (Name "indvars.iv301") (locals s') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    fixed_registers s' /\
    (forall id, ~ In id fixed_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fixed_frame c c'.
Proof.
  intros Relation [AD AT AP AU] Registers Input Compare.
  destruct Registers as [N Count Data Target Perm Used].
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  pose (s1 := fixed_compare_state s (Z.of_nat (nat_of_ord index))
    (block_address layout bd) (block_provenance layout bd)
    (block_address layout bt) (block_provenance layout bt)
    (Int.repr (Z.of_nat (source index))) (Int.repr (Z.of_nat (desired index)))).
  assert (Comparison : runs (denote_block (proj1_sig FullCFG.fixed_compare) from varargs) s s1
      (inl (if choice then Name "if.then49" else Name "if.end57"))).
  { rewrite <- Compare. apply fixed_compare_runs; try assumption; try lia.
    - eapply related_load; [exact Relation|lia|].
      exact (proj1 (AD _ _ (words_nth_error source index))).
    - eapply related_load; [exact Relation|lia|].
      exact (proj1 (AT _ _ (words_nth_error desired index))). }
  assert (Other1 : forall id, ~ In id fixed_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply fixed_compare_other, Outside. }
  assert (Index1 : Maps.lookup (Name "indvars.iv301") (locals s1) =
      Some (index_value (Z.of_nat (nat_of_ord index)))).
  { unfold s1, fixed_compare_state. rewrite -> !lookup_local_other by discriminate. apply lookup_local_same. }
  destruct choice.
  - destruct (@related_store layout c (fst s) bp (nat_of_ord index)
      (Int.repr (Z.of_nat (nat_of_ord index))) Relation ltac:(lia))
      as [c1 [m1 [Store [Write [Related _]]]]].
    pose (s2 := fixed_assign_state s1 (Z.of_nat (nat_of_ord index))
      (block_address layout bp) (block_provenance layout bp) m1).
    assert (Assignment : runs (denote_block (proj1_sig FullCFG.fixed_assign)
        (Name "if.end43") varargs) s1 s2 (inl (Name "if.end57"))).
    { apply fixed_assign_runs; [lia|exact Index1| |].
      - rewrite -> Other1 by (unfold fixed_modified; simpl; intuition discriminate). exact Perm.
      - unfold s1, fixed_compare_state. rewrite -> !memory_set_local. exact Write. }
    assert (Other2 : forall id, ~ In id fixed_modified ->
        Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
    { intros id Outside. unfold s2. rewrite -> fixed_assign_other by exact Outside. apply Other1, Outside. }
    exists c1, s2. split; [unfold s2; rewrite -> fixed_assign_memory; exact Related|].
    split.
    + constructor.
      * eapply array_store_disjoint; [exact AD|exact DP|exact Store].
      * eapply array_store_disjoint; [exact AT|exact TP|exact Store].
      * rewrite <- words_update. eapply array_store_same; eassumption.
      * eapply array_store_disjoint; [exact AU|exact (not_eq_sym PU)|exact Store].
    + split.
      * eapply steps_next; [exact (proj2_sig FullCFG.fixed_compare)|exact Comparison|].
        eapply steps_next; [exact (proj2_sig FullCFG.fixed_assign)|exact Assignment|constructor].
      * split.
        -- unfold s2, fixed_assign_state. rewrite -> locals_with_memory.
           rewrite -> !lookup_local_other by discriminate. exact Index1.
        -- split.
           ++ constructor; rewrite -> Other2 by (unfold fixed_modified; simpl; intuition discriminate); assumption.
           ++ split; [exact Other2|]. intros other values NotPerm NotUsed A.
              eapply array_store_disjoint; [exact A|exact NotPerm|exact Store].
  - exists c, s1. split.
    { unfold s1, fixed_compare_state. rewrite -> !memory_set_local. exact Relation. }
    split; [constructor; assumption|]. split.
    + eapply steps_next; [exact (proj2_sig FullCFG.fixed_compare)|exact Comparison|constructor].
    + split; [exact Index1|]. split.
      * constructor; rewrite -> Other1 by (unfold fixed_modified; simpl; intuition discriminate); assumption.
      * split; [exact Other1|]. intros other values NotPerm NotUsed A. exact A.
Qed.

Definition fixed_invariant original processed :=
  fixed_arrays (fixed_assignment source desired original processed)
    (List.firstn processed (words (fixed_flags source desired))).

Lemma fixed_iteration from varargs c s (index : 'I_count) original :
  cells_related layout c (fst s) -> fixed_invariant original (nat_of_ord index) c ->
  fixed_registers s -> fixed_input from s (Z.of_nat (nat_of_ord index)) ->
  exists c' s', cells_related layout c' (fst s') /\
    fixed_invariant original (S (nat_of_ord index)) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43") s
      (Name "if.end57") (if Z.of_nat (nat_of_ord index) + 1 =? Z.of_nat count
        then Name "if.end65.preheader" else Name "if.end43") s' /\
    fixed_registers s' /\ fixed_input (Name "if.end57") s' (Z.of_nat (S (nat_of_ord index))) /\
    (forall id, ~ In id fixed_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fixed_frame c c'.
Proof.
  intros Relation Inv Registers Input.
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  pose (choice := Nat.eqb (source index) (desired index)).
  destruct (@fixed_branch from varargs c s index
    (fixed_assignment source desired original (nat_of_ord index))
    (List.firstn (nat_of_ord index) (words (fixed_flags source desired))) choice
    Relation Inv Registers Input (natural_word_equal _ _ (SourceUInt index) (TargetUInt index)))
    as [c1 [s1 [Related1 [Arrays1 [Branch [Index1 [Regs1 [Other1 Frame1]]]]]]]].
  destruct (@related_store layout c1 (fst s1) bu (nat_of_ord index) (flag_word choice)
    Related1 ltac:(lia)) as [c2 [m2 [Store [Write [Related2 _]]]]].
  pose (s2 := fixed_merge_state s1 (Z.of_nat (nat_of_ord index)) (Z.of_nat count)
    (block_address layout bu) (block_provenance layout bu) choice m2).
  destruct Regs1 as [N Count Data Target Perm Used].
  assert (Merge : runs (denote_block (proj1_sig FullCFG.fixed_merge) (fixed_from choice) varargs)
      s1 s2 (inl (if Z.of_nat (nat_of_ord index) + 1 =? Z.of_nat count
        then Name "if.end65.preheader" else Name "if.end43"))).
  { apply fixed_merge_runs; try assumption; lia. }
  assert (Other : forall id, ~ In id fixed_modified ->
      Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
  { intros id Outside. unfold s2. rewrite -> fixed_merge_other by exact Outside. apply Other1, Outside. }
  destruct Arrays1 as [AD AT AP AU].
  exists c2, s2. split; [unfold s2; rewrite -> fixed_merge_memory; exact Related2|].
  split.
  - constructor.
    + eapply array_store_disjoint; [exact AD|exact DU|exact Store].
    + eapply array_store_disjoint; [exact AT|exact TU|exact Store].
    + unfold choice in AP. rewrite -> fixed_assignment_step in AP.
      eapply array_store_disjoint; [exact AP|exact PU|exact Store].
    + rewrite -> (firstn_step _ (nat_of_ord index) (Z.of_nat (fixed_flags source desired index)))
        by exact (words_nth_error (fixed_flags source desired) index).
      eapply array_append_store; [exact AU|].
      rewrite -> List.firstn_length, words_length, Nat.min_l by lia.
      unfold flag_word, choice in Store. unfold fixed_flags.
      destruct (Nat.eqb (source index) (desired index)); exact Store.
  - split.
    + eapply block_steps_append; [exact Branch|].
      eapply steps_next; [exact (proj2_sig FullCFG.fixed_merge)|exact Merge|constructor].
    + split.
      * constructor; unfold s2; rewrite -> fixed_merge_other by
          (unfold fixed_modified; simpl; intuition discriminate); assumption.
      * split.
        -- rewrite -> Nat2Z.inj_succ. replace (Z.succ (Z.of_nat (nat_of_ord index))) with
             (Z.of_nat (nat_of_ord index) + 1) by lia. apply fixed_merge_next.
        -- split; [exact Other|]. intros other values NotPerm NotUsed A.
           eapply array_store_disjoint; [apply Frame1; eassumption|exact NotUsed|exact Store].
Qed.

Theorem fixed_loop varargs original : forall remaining start from c s,
  (0 < remaining)%coq_nat -> (start + remaining = count)%coq_nat ->
  cells_related layout c (fst s) -> fixed_invariant original start c -> fixed_registers s ->
  fixed_input from s (Z.of_nat start) ->
  exists c' s', cells_related layout c' (fst s') /\ fixed_invariant original count c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43") s
      (Name "if.end57") (Name "if.end65.preheader") s' /\
    (forall id, ~ In id fixed_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fixed_frame c c'.
Proof.
  intro remaining. induction remaining as [|remaining IH];
    intros start from c s Positive Sum Relation Inv Registers Input; [lia|].
  assert (K : (start < count)%coq_nat) by lia.
  pose index : 'I_count := Ordinal (introT ltP K).
  destruct (@fixed_iteration from varargs c s index original Relation Inv Registers Input)
    as [c1 [s1 [Related1 [Inv1 [Step [Locals1 [Next [Other Frame]]]]]]]].
  change (nat_of_ord index) with start in Inv1, Step, Next.
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat start + 1 =? Z.of_nat count) = true)
      by (apply Z.eqb_eq; lia).
    rewrite -> Last in Step. exists c1, s1. split; [exact Related1|].
    split; [replace count with (S start) by lia; exact Inv1|].
    split; [exact Step|]. split; assumption.
  - assert (More : (Z.of_nat start + 1 =? Z.of_nat count) = false)
      by (apply Z.eqb_neq; lia).
    rewrite -> More in Step.
    destruct (IH (S start) (Name "if.end57") c1 s1 ltac:(lia) ltac:(lia)
      Related1 Inv1 Locals1 Next) as [c' [s' [Related [Final [Steps [Locals Frame']]]]]].
    exists c', s'. split; [exact Related|]. split; [exact Final|]. split.
    + eapply block_steps_append; eassumption.
    + split.
      * intros id Outside. rewrite -> Locals by exact Outside. apply Other, Outside.
      * intros other values NotPerm NotUsed A. apply Frame'; try assumption.
        apply Frame; assumption.
Qed.

Lemma fixed_preheader_runs from varargs (s : FusedS) :
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count))) ->
  runs (denote_block (proj1_sig FullCFG.fixed_preheader) from varargs) s
    (set_local s (Name "wide.trip.count304") (index_value (Z.of_nat count)))
    (inl (Name "if.end43")).
Proof.
  intro N. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (Z.of_nat count)).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite -> extend_word, small_unsigned by lia. reflexivity.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Definition fixed_unmodified id := id <> Name "wide.trip.count304" /\ ~ In id fixed_modified.

Theorem fixed_pass from varargs c s original : (0 < count)%coq_nat ->
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bt (words desired) -> array_at c bp (words original) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  exists c' s', cells_related layout c' (fst s') /\
    fixed_arrays (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)
      (words (fixed_flags source desired)) c' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43.preheader") s
      (Name "if.end57") (Name "if.end65.preheader") s' /\
    (forall id, fixed_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    fixed_frame c c'.
Proof.
  intros Positive Relation AD AT AP N Data Target Perm Used.
  assert (Initial : fixed_invariant original 0 c).
  { constructor.
    - exact AD.
    - exact AT.
    - exact AP.
    - intros k v H. destruct k; discriminate. }
  pose (s1 := set_local s (Name "wide.trip.count304") (index_value (Z.of_nat count))).
  assert (Related1 : cells_related layout c (fst s1)).
  { unfold s1. rewrite -> memory_set_local. exact Relation. }
  assert (Registers : fixed_registers s1).
  { constructor; unfold s1;
      first [apply lookup_local_same | rewrite -> lookup_local_other by discriminate; assumption]. }
  destruct (@fixed_loop varargs original count 0 (Name "if.end43.preheader") c s1
    Positive Logic.eq_refl Related1 Initial Registers
    (or_introl (conj Logic.eq_refl Logic.eq_refl)))
    as [c' [s' [Related [Final [Steps [Locals Frame]]]]]].
  exists c', s'. split; [exact Related|]. split.
  - destruct Final as [D T P U]. constructor; try assumption.
    + assert (E : words (fixed_assignment source desired original count) =
        words (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)).
      { apply words_ext. intro x. unfold fixed_assignment.
        assert (B : Nat.ltb (nat_of_ord x) count = true).
        { apply Nat.ltb_lt. exact (elimT ltP (ltn_ord x)). }
        rewrite -> B. reflexivity. }
      rewrite <- E. exact P.
    + rewrite -> List.firstn_all2 in U by (rewrite -> words_length; lia). exact U.
  - split.
    + eapply steps_next; [exact (proj2_sig FullCFG.fixed_preheader)| |exact Steps].
      apply fixed_preheader_runs, N.
    + split; [|exact Frame]. intros id [Different Outside].
      rewrite -> Locals by exact Outside. unfold s1.
      rewrite -> lookup_local_other by exact Different. reflexivity.
Qed.

Corollary fixed_pass_semantics from varargs c s original : (0 < count)%coq_nat ->
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bt (words desired) -> array_at c bp (words original) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat count))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  exists c' s', cells_related layout c' (fst s') /\
    fixed_arrays (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)
      (words (fixed_flags source desired)) c' /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (from, Name "if.end43.preheader")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end57", Name "if.end65.preheader")) s')).
Proof.
  intros Positive Relation AD AT AP N Data Target Perm Used.
  destruct (@fixed_pass from varargs c s original Positive Relation AD AT AP N Data Target Perm Used)
    as [c' [s' [Related [Final [Steps Rest]]]]].
  exists c', s'. split; [exact Related|]. split; [exact Final|].
  apply block_steps_sound, Steps.
Qed.
End Pass.
