(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ModelArrays SolcModel ModelProofs FirstFree.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index SearchBlocks Search.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem first_free_search layout count value (desired : 'I_count -> nat)
    (reserved : {set 'I_count}) (bt bu : Values.block) varargs c s (chosen : 'I_count) :
  (count <= 1024)%coq_nat ->
  (count <= block_words layout bt)%coq_nat -> (count <= block_words layout bu)%coq_nat ->
  uint (Z.of_nat value) -> (forall x, uint (Z.of_nat (desired x))) ->
  first_free desired value reserved (enum 'I_count) = Some chosen ->
  cells_related layout c (fst s) ->
  array_at c bt (words desired) -> array_at c bu (words (used_flags reserved)) ->
  search_registers layout count value bt bu s ->
  exists s', fst s' = fst s /\
    block_steps (blks FullCFG.body) varargs (Name "if.end65") (Name "if.end77") s
      (Name "while.end93") (Name "if.end97") s' /\
    Maps.lookup (Name "v9.0.lcssa") (locals s') =
      Some (word_value (Int.repr (Z.of_nat (nat_of_ord chosen)))) /\
    search_registers layout count value bt bu s' /\
    (forall id, ~ In id search_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Bound CT CU ValueUInt TargetUInt Choice Related Target Flags Registers.
  destruct (first_free_some Choice) as [_ [Free Match]].
  assert (FreeFlag : used_flags reserved chosen = 0%nat).
  { unfold used_flags. by move/negbTE: Free=> ->. }
  assert (Found : search_match count value desired (used_flags reserved) chosen = true).
  { unfold search_match. rewrite -> FreeFlag, Match, !Nat.eqb_refl. reflexivity. }
  assert (Minimum : forall x, (0 <= nat_of_ord x)%coq_nat ->
      (nat_of_ord x < nat_of_ord chosen)%coq_nat ->
      search_match count value desired (used_flags reserved) x = false).
  { intros x Lower Upper. unfold search_match.
    destruct (first_free_minimum Choice Upper) as [Used|Different].
    - unfold used_flags. rewrite -> Used. reflexivity.
    - assert (Miss : Nat.eqb value (desired x) = false) by (apply Nat.eqb_neq; congruence).
      rewrite -> Miss, Bool.andb_false_r. reflexivity. }
  exact (@search_found layout count value desired (used_flags reserved) bt bu
    Bound CT CU ValueUInt TargetUInt (used_flags_uint count reserved) varargs c chosen
    Target Flags Found (nat_of_ord chosen) 0 (Name "if.end65") s
    ltac:(lia) Minimum Related Registers (or_introl (conj Logic.eq_refl Logic.eq_refl))).
Qed.
