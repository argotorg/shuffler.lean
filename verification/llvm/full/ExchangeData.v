(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers.
From Vellvm Require Import Utils Syntax TypToDtyp ScopeTheory Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index
  WordArithmetic FixedBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition exchange_data : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end153" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 32 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Lemma trace_unsigned x : 0 <= x <= 2048 -> Int.unsigned (Int.repr x) = x.
Proof.
  intro Bound. apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia.
Qed.

Lemma trace_gep address provenance x : 0 <= x <= 2048 ->
  eval_gep (DTYPE_I 32) (pointer_value address provenance) (index_value x :: nil) =
    raise_ret (pointer_value (address + 4 * x) provenance).
Proof.
  intro Bound.
  change (raise_ret (pointer_value
    (address + 4 * @LLVMInt.signed 64 (LLVMInt.repr x)) provenance) =
    raise_ret (pointer_value (address + 4 * x) provenance)).
  rewrite LLVMInt.signed_repr by
    (change (-9223372036854775808 <= x <= 9223372036854775807); lia).
  reflexivity.
Qed.

Definition exchange_data_state s count ta tp m1 m2 m3 m4 :=
  let s1 := with_memory (with_memory s m1) m2 in
  let s2 := set_local s1 (Anon 21) (word_value (Int.repr count)) in
  let s3 := set_local s2 (Name "idxprom163") (index_value count) in
  let s4 := set_local s3 (Name "arrayidx164") (pointer_value (ta + 4 * count) tp) in
  let s5 := with_memory s4 m3 in
  let s6 := set_local s5 (Anon 22) (word_value (Int.repr count)) in
  let s7 := set_local s6 (Name "add166") (word_value (Int.repr (count + 1))) in
  with_memory s7 m4.

Lemma exchange_data_runs from varargs s selected top dp ta tp oa op x y depth count m1 m2 m3 m4 :
  0 <= count <= 2048 ->
  Maps.lookup (Name "arrayidx135") (locals s) = Some (pointer_value selected dp) ->
  Maps.lookup (Name "arrayidx137") (locals s) = Some (pointer_value top dp) ->
  Maps.lookup (Name "v6") (locals s) = Some (pointer_value ta tp) ->
  Maps.lookup (Name "v7") (locals s) = Some (pointer_value oa op) ->
  Maps.lookup (Anon 18) (locals s) = Some (word_value x) ->
  Maps.lookup (Anon 19) (locals s) = Some (word_value y) ->
  Maps.lookup (Name "sub140") (locals s) = Some (word_value (Int.repr depth)) ->
  run_memory (Impl.write_dvalue (selected, dp) (DTYPE_I 32) (word_value y)) (fst s) =
    Ret (m1, tt) ->
  run_memory (Impl.write_dvalue (top, dp) (DTYPE_I 32) (word_value x)) m1 =
    Ret (m2, tt) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (oa, op)) m2 =
    Ret (m2, word_value (Int.repr count)) ->
  run_memory (Impl.write_dvalue (ta + 4 * count, tp) (DTYPE_I 32)
    (word_value (Int.repr depth))) m2 = Ret (m3, tt) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (oa, op)) m3 =
    Ret (m3, word_value (Int.repr count)) ->
  run_memory (Impl.write_dvalue (oa, op) (DTYPE_I 32)
    (word_value (Int.repr (count + 1)))) m3 = Ret (m4, tt) ->
  runs (denote_block (proj1_sig exchange_data) from varargs) s
    (exchange_data_state s count ta tp m1 m2 m3 m4) (inl (Name "if.end169")).
Proof.
  intros Bound Selected Top Trace Output X Y Depth WriteSelected WriteTop ReadCount1
    WriteTrace ReadCount2 WriteCount.
  eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_store; [entry_lookup|entry_lookup|].
      resolve_types. exact WriteSelected.
    + eapply runs_code_cons.
      * eapply runs_instruction_store; [entry_lookup|entry_lookup|].
        resolve_types. exact WriteTop.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value (Int.repr count)).
           ++ entry_lookup.
           ++ resolve_types. exact ReadCount1.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := index_value count).
              eapply runs_expression_conversion; [entry_lookup|].
              resolve_types. rewrite extend_word, trace_unsigned by exact Bound. reflexivity.
           ++ eapply runs_code_cons.
              ** apply runs_assign with (value := pointer_value (ta + 4 * count) tp).
                 eapply runs_expression_gep; [entry_lookup|entry_lookup|].
                 resolve_types. apply trace_gep, Bound.
              ** eapply runs_code_cons.
                 --- eapply runs_instruction_store; [entry_lookup|entry_lookup|].
                     resolve_types. rewrite !memory_set_local. exact WriteTrace.
                 --- eapply runs_code_cons.
                     +++ eapply runs_instruction_read with (value := word_value (Int.repr count)).
                         *** entry_lookup.
                         *** resolve_types. exact ReadCount2.
                     +++ eapply runs_code_cons.
                         *** apply runs_assign with (value := word_value (Int.repr (count + 1))).
                             eapply runs_expression_ibinop with (vb := word_value (Int.repr 1)).
                             ---- entry_lookup.
                             ---- apply runs_expression_integer. resolve_types. reflexivity.
                             ---- apply word_add.
                         *** eapply runs_code_cons.
                             ---- eapply runs_instruction_store; [entry_lookup|entry_lookup|].
                                  resolve_types. rewrite !memory_set_local. exact WriteCount.
                             ---- apply runs_code_nil.
  - apply runs_jump.
Qed.

Definition exchange_data_modified : list raw_id :=
  [Anon 21; Name "idxprom163"; Name "arrayidx164"; Anon 22; Name "add166"].

Lemma exchange_data_memory s count ta tp m1 m2 m3 m4 :
  fst (exchange_data_state s count ta tp m1 m2 m3 m4) = m4.
Proof. reflexivity. Qed.

Lemma exchange_data_other s count ta tp m1 m2 m3 m4 id :
  ~ In id exchange_data_modified ->
  Maps.lookup id (locals (exchange_data_state s count ta tp m1 m2 m3 m4)) =
    Maps.lookup id (locals s).
Proof.
  intro Outside. unfold exchange_data_state.
  repeat first [rewrite locals_with_memory |
    rewrite lookup_local_other by
      (intro E; subst; apply Outside; unfold exchange_data_modified; simpl; tauto)].
  reflexivity.
Qed.
