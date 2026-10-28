(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers.
From Vellvm Require Import Utils Syntax TypToDtyp ScopeTheory Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index WordArithmetic.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition main_preheader : {b : LLVMAst.block dtyp | FullCFG.named_block "while.end105" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 21 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition main_preheader_state s n pa pp da dp :=
  let s1 := set_local s (Name "sub") (word_value (Int.repr (n - 1))) in
  let s2 := set_local s1 (Name "idxprom108") (index_value (n - 1)) in
  let s3 := set_local s2 (Name "arrayidx109") (pointer_value (pa + 4 * (n - 1)) pp) in
  let s4 := set_local s3 (Name "arrayidx137") (pointer_value (da + 4 * (n - 1)) dp) in
  set_local s4 (Name "add149") (word_value (Int.repr (2 * n))).

Lemma main_preheader_runs from varargs s n pa pp da dp :
  0 < n <= 1024 ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr n)) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value pa pp) ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value da dp) ->
  runs (denote_block (proj1_sig main_preheader) from varargs) s
    (main_preheader_state s n pa pp da dp) (inl (Name "while.cond106")).
Proof.
  intros Bound Size Perm Data. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := word_value (Int.repr (n - 1))).
      eapply runs_expression_ibinop with (vb := word_value (Int.repr (-1))).
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. rewrite word_repr. reflexivity.
      * apply word_add.
    + eapply runs_code_cons.
      * apply runs_assign with (value := index_value (n - 1)).
        eapply runs_expression_conversion; [entry_lookup|].
        resolve_types. rewrite extend_word, small_unsigned by lia. reflexivity.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := pointer_value (pa + 4 * (n - 1)) pp).
           eapply runs_expression_gep; [entry_lookup|entry_lookup|].
           resolve_types. apply index_gep; lia.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := pointer_value (da + 4 * (n - 1)) dp).
              eapply runs_expression_gep; [entry_lookup|entry_lookup|].
              resolve_types. apply index_gep; lia.
           ++ eapply runs_code_cons.
              ** apply runs_assign with (value := word_value (Int.repr (2 * n))).
                 eapply runs_expression_ibinop with (vb := word_value Int.one).
                 --- entry_lookup.
                 --- apply runs_expression_integer. resolve_types. reflexivity.
                 --- apply word_double; lia.
              ** apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma main_preheader_memory s n pa pp da dp :
  fst (main_preheader_state s n pa pp da dp) = fst s.
Proof. unfold main_preheader_state. rewrite !memory_set_local. reflexivity. Qed.

Definition main_preheader_modified : list raw_id :=
  [Name "sub"; Name "idxprom108"; Name "arrayidx109"; Name "arrayidx137"; Name "add149"].

Lemma main_preheader_other s n pa pp da dp id : ~ In id main_preheader_modified ->
  Maps.lookup id (locals (main_preheader_state s n pa pp da dp)) = Maps.lookup id (locals s).
Proof.
  intro Outside. unfold main_preheader_state.
  repeat rewrite lookup_local_other by
    (intro E; subst id; apply Outside; unfold main_preheader_modified; simpl; tauto).
  reflexivity.
Qed.

Lemma main_preheader_bindings s n pa pp da dp :
  Maps.lookup (Name "sub") (locals (main_preheader_state s n pa pp da dp)) =
    Some (word_value (Int.repr (n - 1))) /\
  Maps.lookup (Name "arrayidx109") (locals (main_preheader_state s n pa pp da dp)) =
    Some (pointer_value (pa + 4 * (n - 1)) pp) /\
  Maps.lookup (Name "arrayidx137") (locals (main_preheader_state s n pa pp da dp)) =
    Some (pointer_value (da + 4 * (n - 1)) dp) /\
  Maps.lookup (Name "add149") (locals (main_preheader_state s n pa pp da dp)) =
    Some (word_value (Int.repr (2 * n))).
Proof.
  unfold main_preheader_state. repeat split;
    repeat rewrite lookup_local_other by discriminate; apply lookup_local_same.
Qed.
