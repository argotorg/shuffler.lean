(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index Initialize.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma check_nonempty from varargs (s : FusedS) (n : Int.int) :
  0 < Int.unsigned n ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  runs (denote_block (proj1_sig FullCFG.check_empty) from varargs) s
    (set_local s (Name "cmp3") (boolean_value false))
    (inl (Name "if.end10.preheader")).
Proof.
  intros Positive N. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := boolean_value false).
      eapply runs_expression_icmp.
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * change (eval_icmp false Eq (word_value n) (word_value Int.zero) =
          raise_ret (boolean_value false)).
        rewrite word_eq. change (Int.unsigned Int.zero) with 0.
        assert (Nonzero : (Int.unsigned n =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite Nonzero. reflexivity.
    + apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 4,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp3")))
        (Name "cleanup") (Name "if.end10.preheader"), []))
      (set_local s (Name "cmp3") (boolean_value false))
      (set_local s (Name "cmp3") (boolean_value false))
      (inl (Name "if.end10.preheader"))).
    resolve_types. apply runs_branch with (choice := false). entry_lookup.
Qed.

Lemma prepare_initialize from varargs (s : FusedS) (n : Int.int) :
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  runs (denote_block (proj1_sig FullCFG.initialize_preheader) from varargs) s
    (set_local s (Name "wide.trip.count") (index_value (Int.unsigned n)))
    (inl (Name "if.end10")).
Proof.
  intro N. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (Int.unsigned n)).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. apply extend_word.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Definition prefix_unmodified id := entry_unmodified id /\
  id <> Name "cmp3" /\ id <> Name "wide.trip.count" /\ initialize_unmodified id.

Theorem initialized_prefix layout output used size varargs c s :
  (0 < size <= 1024)%nat ->
  (3 <= block_words layout output)%nat -> (size <= block_words layout used)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout used) (block_provenance layout used)) ->
  exists c1 c' s',
    output_stores c output c1 /\ zero_stores used 0 size c1 c' /\
    cells_related layout c' (fst s') /\
    block_steps (blks FullCFG.body) varargs (Name "entry") (Name "entry") s
      (Name "if.end10") (Name "if.end17.preheader") s' /\
    (forall id, prefix_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    output_registers layout output s'.
Proof.
  intros [Positive Size] OutputCapacity UsedCapacity Relation N Output Used.
  assert (Unsigned : Int.unsigned (Int.repr (Z.of_nat size)) = Z.of_nat size).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia. }
  destruct (@entry_related layout c s (Int.repr (Z.of_nat size)) output
    (Name "entry") varargs Relation OutputCapacity N Output)
    as [c1 [s1 [Stores [Related1 [Entry [Locals1 Output1]]]]]].
  rewrite Unsigned in Entry.
  assert (Within : (1024 <? Z.of_nat size) = false) by (apply Z.ltb_ge; lia).
  rewrite Within in Entry.
  assert (N1 : Maps.lookup (Name "v1") (locals s1) =
    Some (word_value (Int.repr (Z.of_nat size)))).
  { rewrite Locals1 by (repeat split; discriminate). exact N. }
  pose (s2 := set_local s1 (Name "cmp3") (boolean_value false)).
  assert (Nonempty : runs (denote_block (proj1_sig FullCFG.check_empty)
      (Name "entry") varargs) s1 s2 (inl (Name "if.end10.preheader"))).
  { apply check_nonempty with (n := Int.repr (Z.of_nat size)); [rewrite Unsigned; lia|exact N1]. }
  assert (N2 : Maps.lookup (Name "v1") (locals s2) =
    Some (word_value (Int.repr (Z.of_nat size)))).
  { unfold s2. rewrite lookup_local_other by discriminate. exact N1. }
  pose (s3 := set_local s2 (Name "wide.trip.count") (index_value (Z.of_nat size))).
  assert (Preheader : runs (denote_block (proj1_sig FullCFG.initialize_preheader)
      (Name "if.end") varargs) s2 s3 (inl (Name "if.end10"))).
  { unfold s3. rewrite <- Unsigned. apply prepare_initialize, N2. }
  assert (Related3 : cells_related layout c1 (fst s3)).
  { unfold s3, s2. rewrite !memory_set_local. exact Related1. }
  assert (Count : Maps.lookup (Name "wide.trip.count") (locals s3) =
      Some (index_value (Z.of_nat size))).
  { apply lookup_local_same. }
  assert (Base : Maps.lookup (Name "v5") (locals s3) = Some
      (pointer_value (block_address layout used) (block_provenance layout used))).
  { unfold s3, s2. rewrite !lookup_local_other by discriminate.
    rewrite Locals1 by (repeat split; discriminate). exact Used. }
  destruct (@initialize_loop layout used size varargs Size UsedCapacity size 0
    (Name "if.end10.preheader") c1 s3 Positive eq_refl Related3
    (or_introl (conj eq_refl eq_refl)) Count Base)
    as [c' [s' [Zeros [Related [Loop Locals]]]]].
  exists c1, c', s'. split; [exact Stores|]. split; [exact Zeros|].
  split; [exact Related|]. split.
  - eapply steps_next; [exact (proj2_sig FullCFG.entry)|exact Entry|].
    eapply steps_next; [exact (proj2_sig FullCFG.check_empty)|exact Nonempty|].
    eapply steps_next; [exact (proj2_sig FullCFG.initialize_preheader)|exact Preheader|].
    exact Loop.
  - split.
    + intros id [A [B [C D]]]. rewrite Locals by exact D.
      unfold s3, s2. rewrite !lookup_local_other by assumption. apply Locals1, A.
    + destruct Output1. constructor;
        rewrite Locals by (unfold initialize_unmodified; repeat split; discriminate);
        unfold s3, s2; rewrite !lookup_local_other by discriminate; assumption.
Qed.

(* This statement uses the actual call and state interpreters. It ends at the
   first validation block; no claim about the rest of the call is made here. *)
Corollary initialized_prefix_semantics layout output used size varargs c s :
  (0 < size <= 1024)%nat ->
  (3 <= block_words layout output)%nat -> (size <= block_words layout used)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat size))) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout used) (block_provenance layout used)) ->
  exists c' s',
    cells_related layout c' (fst s') /\
    (forall k, (k < size)%nat ->
      Mem.load Mint32 c' used (4 * Z.of_nat k) = Some (Vint Int.zero)) /\
    (forall ctx, eutt eq
      (run ctx (denote_ocfg (blks FullCFG.body) varargs (Name "entry", Name "entry")) s)
      (run ctx (denote_ocfg (blks FullCFG.body) varargs
        (Name "if.end10", Name "if.end17.preheader")) s')).
Proof.
  intros Size OutputCapacity UsedCapacity Relation N Output Used.
  destruct (@initialized_prefix layout output used size varargs c s Size
    OutputCapacity UsedCapacity Relation N Output Used)
    as [c1 [c' [s' [Stores [Zeros [Related [Steps Locals]]]]]]].
  exists c', s'. split; [exact Related|]. split.
  - intros k Bound. eapply zero_stores_values; [exact Zeros|lia].
  - apply block_steps_sound, Steps.
Qed.
