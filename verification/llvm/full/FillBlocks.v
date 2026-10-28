(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax TypToDtyp ScopeTheory Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index FixedBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition fill_preheader : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end65.preheader" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 12 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fill_compare : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end65" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 13 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fill_assign : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end97" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 19 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fill_next : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end103" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 20 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fill_input from s k : Prop :=
  (from = Name "if.end65.preheader" /\ k = 0) \/
  (from = Name "if.end103" /\
   Maps.lookup (Name "indvars.iv.next312") (locals s) = Some (index_value k)).

Definition fill_preheader_state s n :=
  set_local (set_local s (Name "wide.trip.count314") (index_value n))
    (Name "wide.trip.count309") (index_value n).

Definition fill_compare_state s k da dp ta tp x y :=
  let s1 := set_local s (Name "indvars.iv311") (index_value k) in
  let s2 := set_local s1 (Name "arrayidx67") (pointer_value (da + 4 * k) dp) in
  let s3 := set_local s2 (Anon 6) (word_value x) in
  let s4 := set_local s3 (Name "arrayidx69") (pointer_value (ta + 4 * k) tp) in
  let s5 := set_local s4 (Anon 7) (word_value y) in
  set_local s5 (Name "cmp70.not") (boolean_value (word_equal x y)).

Definition fill_assign_state s k j pa pp ua up m1 m2 :=
  let s1 := set_local s (Name "arrayidx99") (pointer_value (pa + 4 * k) pp) in
  let s2 := with_memory s1 m1 in
  let s3 := set_local s2 (Name "idxprom100") (index_value j) in
  let s4 := set_local s3 (Name "arrayidx101") (pointer_value (ua + 4 * j) up) in
  with_memory s4 m2.

Definition fill_next_state s k n :=
  let s1 := set_local s (Name "indvars.iv.next312") (index_value (k + 1)) in
  set_local s1 (Name "exitcond315.not") (boolean_value (k + 1 =? n)).

Lemma fill_preheader_runs from varargs (s : FusedS) n :
  0 <= n <= 1024 ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr n)) ->
  runs (denote_block (proj1_sig fill_preheader) from varargs) s (fill_preheader_state s n)
    (inl (Name "if.end65")).
Proof.
  intros Bound Size. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value n).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by exact Bound. reflexivity.
    + eapply runs_code_cons.
      * apply runs_assign with (value := index_value n).
        eapply runs_expression_conversion; [entry_lookup|].
        resolve_types. rewrite extend_word, small_unsigned by exact Bound. reflexivity.
      * apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma fill_phi from s k : fill_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig fill_compare))) s
    (set_local s (Name "indvars.iv311") (index_value k)) tt.
Proof.
  intros [[-> ->]|[-> Next]]; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma fill_compare_runs from varargs (s : FusedS) k da dp ta tp x y :
  0 <= k <= 1024 -> fill_input from s k ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value da dp) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value ta tp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (da + 4 * k, dp)) (fst s) =
    Ret (fst s, word_value x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (ta + 4 * k, tp)) (fst s) =
    Ret (fst s, word_value y) ->
  runs (denote_block (proj1_sig fill_compare) from varargs) s
    (fill_compare_state s k da dp ta tp x y)
    (inl (if word_equal x y then Name "if.end103" else Name "if.end77")).
Proof.
  intros Bound Input Data Target ReadData ReadTarget.
  eapply runs_block; [apply fill_phi, Input| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (da + 4 * k) dp).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, Bound.
    + eapply runs_code_cons.
      * eapply runs_instruction_read with (value := word_value x).
        -- entry_lookup.
        -- resolve_types. rewrite !memory_set_local. exact ReadData.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := pointer_value (ta + 4 * k) tp).
           eapply runs_expression_gep; [entry_lookup|entry_lookup|].
           resolve_types. apply index_gep, Bound.
        -- eapply runs_code_cons.
           ++ eapply runs_instruction_read with (value := word_value y).
              ** entry_lookup.
              ** resolve_types. rewrite !memory_set_local. exact ReadTarget.
           ++ eapply runs_code_cons.
              ** apply runs_assign with (value := boolean_value (word_equal x y)).
                 eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
                 cbv beta delta [endo Endo_id].
                 lazymatch goal with
                 | |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq
                 end.
              ** apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 21,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp70.not")))
        (Name "if.end103") (Name "if.end77"), []))
      (fill_compare_state s k da dp ta tp x y) (fill_compare_state s k da dp ta tp x y)
      (inl (if word_equal x y then Name "if.end103" else Name "if.end77"))).
    resolve_types. apply runs_branch. unfold fill_compare_state. entry_lookup.
Qed.

Lemma fill_assign_runs from varargs (s : FusedS) k j pa pp ua up m1 m2 :
  0 <= k <= 1024 -> 0 <= j <= 1024 ->
  Maps.lookup (Name "indvars.iv311") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "v9.0.lcssa") (locals s) = Some (word_value (Int.repr j)) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value pa pp) ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value ua up) ->
  run_memory (Impl.write_dvalue (pa + 4 * k, pp) (DTYPE_I 32)
    (word_value (Int.repr j))) (fst s) = Ret (m1, tt) ->
  run_memory (Impl.write_dvalue (ua + 4 * j, up) (DTYPE_I 32)
    (word_value Int.one)) m1 = Ret (m2, tt) ->
  runs (denote_block (proj1_sig fill_assign) from varargs) s
    (fill_assign_state s k j pa pp ua up m1 m2) (inl (Name "if.end103")).
Proof.
  intros K J Index Chosen Perm Used WritePerm WriteUsed. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (pa + 4 * k) pp).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, K.
    + eapply runs_code_cons.
      * eapply runs_instruction_store; [entry_lookup|entry_lookup|].
        resolve_types. rewrite memory_set_local. exact WritePerm.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := index_value j).
           eapply runs_expression_conversion; [entry_lookup|].
           resolve_types. rewrite extend_word, small_unsigned by exact J. reflexivity.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := pointer_value (ua + 4 * j) up).
              eapply runs_expression_gep; [entry_lookup|entry_lookup|].
              resolve_types. apply index_gep, J.
           ++ eapply runs_code_cons.
              ** eapply runs_instruction_store with (v := word_value Int.one).
                 --- apply runs_expression_integer. resolve_types. reflexivity.
                 --- entry_lookup.
                 --- resolve_types. rewrite !memory_set_local. exact WriteUsed.
              ** apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma fill_next_runs from varargs (s : FusedS) k n :
  0 <= k < n -> n <= 1024 ->
  Maps.lookup (Name "indvars.iv311") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "wide.trip.count314") (locals s) = Some (index_value n) ->
  runs (denote_block (proj1_sig fill_next) from varargs) s (fill_next_state s k n)
    (inl (if k + 1 =? n then Name "while.end105" else Name "if.end65")).
Proof.
  intros Bound Size Index Count. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (k + 1)).
      eapply runs_expression_ibinop with (vb := index_value 1).
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * apply index_add; lia.
    + eapply runs_code_cons.
      * apply runs_assign with (value := boolean_value (k + 1 =? n)).
        eapply runs_expression_icmp; [entry_lookup|entry_lookup|apply index_eq; lia].
      * apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 30,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "exitcond315.not")))
        (Name "while.end105") (Name "if.end65"), []))
      (fill_next_state s k n) (fill_next_state s k n)
      (inl (if k + 1 =? n then Name "while.end105" else Name "if.end65"))).
    resolve_types. apply runs_branch. unfold fill_next_state. entry_lookup.
Qed.

Definition fill_modified : list raw_id :=
  [Name "indvars.iv311"; Name "arrayidx67"; Anon 6; Name "arrayidx69"; Anon 7;
   Name "cmp70.not"; Name "arrayidx99"; Name "idxprom100"; Name "arrayidx101";
   Name "indvars.iv.next312"; Name "exitcond315.not"].

Ltac fill_locals :=
  repeat first [rewrite lookup_local_other by
    (intro E; subst; match goal with H : ~ In _ fill_modified |- _ =>
      apply H; unfold fill_modified; simpl; tauto end)
    | rewrite locals_with_memory].

Lemma fill_compare_memory s k da dp ta tp x y :
  fst (fill_compare_state s k da dp ta tp x y) = fst s.
Proof. unfold fill_compare_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma fill_assign_memory s k j pa pp ua up m1 m2 :
  fst (fill_assign_state s k j pa pp ua up m1 m2) = m2.
Proof. reflexivity. Qed.

Lemma fill_next_memory s k n : fst (fill_next_state s k n) = fst s.
Proof. unfold fill_next_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma fill_compare_other s k da dp ta tp x y id : ~ In id fill_modified ->
  Maps.lookup id (locals (fill_compare_state s k da dp ta tp x y)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fill_compare_state. fill_locals. reflexivity. Qed.

Lemma fill_assign_other s k j pa pp ua up m1 m2 id : ~ In id fill_modified ->
  Maps.lookup id (locals (fill_assign_state s k j pa pp ua up m1 m2)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fill_assign_state. fill_locals. reflexivity. Qed.

Lemma fill_next_other s k n id : ~ In id fill_modified ->
  Maps.lookup id (locals (fill_next_state s k n)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fill_next_state. fill_locals. reflexivity. Qed.

Lemma fill_compare_index s k da dp ta tp x y :
  Maps.lookup (Name "indvars.iv311") (locals (fill_compare_state s k da dp ta tp x y)) =
    Some (index_value k).
Proof.
  unfold fill_compare_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
Qed.

Lemma fill_compare_value s k da dp ta tp x y :
  Maps.lookup (Anon 6) (locals (fill_compare_state s k da dp ta tp x y)) = Some (word_value x).
Proof.
  unfold fill_compare_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
Qed.

Lemma fill_assign_index s k j pa pp ua up m1 m2 :
  Maps.lookup (Name "indvars.iv311") (locals (fill_assign_state s k j pa pp ua up m1 m2)) =
    Maps.lookup (Name "indvars.iv311") (locals s).
Proof.
  unfold fill_assign_state.
  repeat first [rewrite locals_with_memory | rewrite lookup_local_other by discriminate].
  reflexivity.
Qed.

Lemma fill_next_input s k n : fill_input (Name "if.end103") (fill_next_state s k n) (k + 1).
Proof.
  right; split; [reflexivity|]. unfold fill_next_state.
  rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.
