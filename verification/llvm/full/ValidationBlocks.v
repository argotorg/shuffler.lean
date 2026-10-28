(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition validation_input from s k : Prop :=
  (from = Name "if.end17.preheader" /\ k = 0) \/
  (from = Name "if.end29" /\
   Maps.lookup (Name "indvars.iv.next297") (locals s) = Some (index_value k)).

Definition range_state s k j address provenance :=
  let s1 := set_local s (Name "indvars.iv296") (index_value k) in
  let s2 := set_local s1 (Name "arrayidx19")
    (pointer_value (address + 4 * k) provenance) in
  let s3 := set_local s2 (Anon 0) (word_value (Int.repr j)) in
  set_local s3 (Name "cmp20.not") (boolean_value true).

Definition unused_state s j address provenance :=
  let s1 := set_local s (Name "idxprom24") (index_value j) in
  let s2 := set_local s1 (Name "arrayidx25")
    (pointer_value (address + 4 * j) provenance) in
  let s3 := set_local s2 (Anon 1) (word_value Int.zero) in
  set_local s3 (Name "cmp26.not") (boolean_value true).

Definition store_state s k n j data_address data_prov target_address target_prov
    m1 m2 value :=
  let s1 := with_memory s m1 in
  let s2 := set_local s1 (Name "arrayidx33")
    (pointer_value (data_address + 4 * k) data_prov) in
  let s3 := set_local s2 (Anon 2) (word_value value) in
  let s4 := set_local s3 (Name "arrayidx35")
    (pointer_value (target_address + 4 * j) target_prov) in
  let s5 := with_memory s4 m2 in
  let s6 := set_local s5 (Name "indvars.iv.next297") (index_value (k + 1)) in
  set_local s6 (Name "exitcond300.not") (boolean_value (k + 1 =? n)).

Lemma validation_phi from s k : validation_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig FullCFG.validation_range))) s
    (set_local s (Name "indvars.iv296") (index_value k)) tt.
Proof.
  intros [[-> ->]|[-> Next]]; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma validation_range_runs from varargs (s : FusedS) k n j address provenance :
  0 <= k < n -> 0 <= j < n -> n <= 1024 ->
  validation_input from s k ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr n)) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (address + 4 * k, provenance))
    (fst s) = Ret (fst s, word_value (Int.repr j)) ->
  runs (denote_block (proj1_sig FullCFG.validation_range) from varargs) s
    (range_state s k j address provenance) (inl (Name "if.end23")).
Proof.
  intros K J N Input Size Base Read.
  eapply runs_block.
  - apply validation_phi, Input.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep. lia.
    + eapply runs_code_cons.
      * eapply runs_instruction_read with (value := word_value (Int.repr j)).
        -- entry_lookup.
        -- resolve_types. rewrite !memory_set_local. exact Read.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := boolean_value true).
           eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
           rewrite word_lt, !small_unsigned by lia.
           assert (Less : (j <? n) = true) by (apply Z.ltb_lt; lia).
           rewrite Less. reflexivity.
        -- apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 9,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp20.not")))
        (Name "if.end23") (Name "cleanup"), []))
      (range_state s k j address provenance) (range_state s k j address provenance)
      (inl (Name "if.end23"))).
    resolve_types. apply runs_branch with (choice := true).
    unfold range_state. entry_lookup.
Qed.

Lemma validation_unused_runs from varargs (s : FusedS) j address provenance :
  0 <= j <= 1024 ->
  Maps.lookup (Anon 0) (locals s) = Some (word_value (Int.repr j)) ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (address + 4 * j, provenance))
    (fst s) = Ret (fst s, word_value Int.zero) ->
  runs (denote_block (proj1_sig FullCFG.validation_unused) from varargs) s
    (unused_state s j address provenance) (inl (Name "if.end29")).
Proof.
  intros J Destination Base Read. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value j).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by exact J. reflexivity.
    + eapply runs_code_cons.
      * apply runs_assign with (value := pointer_value (address + 4 * j) provenance).
        eapply runs_expression_gep; [entry_lookup|entry_lookup|].
        resolve_types. apply index_gep, J.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value Int.zero).
           ++ entry_lookup.
           ++ resolve_types. rewrite !memory_set_local. exact Read.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := boolean_value true).
              eapply runs_expression_icmp with (vb := word_value Int.zero).
              ** entry_lookup.
              ** apply runs_expression_integer. resolve_types. reflexivity.
              ** reflexivity.
           ++ apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 10,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp26.not")))
        (Name "if.end29") (Name "cleanup"), []))
      (unused_state s j address provenance) (unused_state s j address provenance)
      (inl (Name "if.end29"))).
    resolve_types. apply runs_branch with (choice := true).
    unfold unused_state. entry_lookup.
Qed.

Lemma validation_store_runs from varargs (s : FusedS) k n j
    data_address data_prov target_address target_prov used_address used_prov
    (m1 m2 : Impl.State) value :
  0 <= k < n -> 0 <= j < n -> n <= 1024 ->
  Maps.lookup (Name "indvars.iv296") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "wide.trip.count299") (locals s) = Some (index_value n) ->
  Maps.lookup (Name "idxprom24") (locals s) = Some (index_value j) ->
  Maps.lookup (Name "arrayidx25") (locals s) = Some (pointer_value used_address used_prov) ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value data_address data_prov) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value target_address target_prov) ->
  run_memory (Impl.write_dvalue (used_address, used_prov) (DTYPE_I 32)
    (word_value Int.one)) (fst s) = Ret (m1, tt) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (data_address + 4 * k, data_prov)) m1 =
    Ret (m1, word_value value) ->
  run_memory (Impl.write_dvalue (target_address + 4 * j, target_prov) (DTYPE_I 32)
    (word_value value)) m1 = Ret (m2, tt) ->
  runs (denote_block (proj1_sig FullCFG.validation_store) from varargs) s
    (store_state s k n j data_address data_prov target_address target_prov m1 m2 value)
    (inl (if k + 1 =? n then Name "if.end43.preheader" else Name "if.end17")).
Proof.
  intros K J N Index Count Destination Used Data Target WriteUsed Read WriteTarget.
  eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_store with (v := word_value Int.one).
      * apply runs_expression_integer. resolve_types. reflexivity.
      * entry_lookup.
      * resolve_types. exact WriteUsed.
    + eapply runs_code_cons.
      * apply runs_assign with (value := pointer_value (data_address + 4 * k) data_prov).
        eapply runs_expression_gep; [entry_lookup|entry_lookup|].
        resolve_types. apply index_gep. lia.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value value).
           ++ entry_lookup.
           ++ resolve_types. rewrite memory_set_local. exact Read.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := pointer_value (target_address + 4 * j) target_prov).
              eapply runs_expression_gep; [entry_lookup|entry_lookup|].
              resolve_types. apply index_gep. lia.
           ++ eapply runs_code_cons.
              ** eapply runs_instruction_store.
                 --- entry_lookup.
                 --- entry_lookup.
                 --- resolve_types. rewrite !memory_set_local. exact WriteTarget.
              ** eapply runs_code_cons.
                 --- apply runs_assign with (value := index_value (k + 1)).
                     eapply runs_expression_ibinop with (vb := index_value 1).
                     +++ entry_lookup.
                     +++ apply runs_expression_integer. resolve_types. reflexivity.
                     +++ apply index_add. lia.
                 --- eapply runs_code_cons.
                     +++ apply runs_assign with (value := boolean_value (k + 1 =? n)).
                         eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
                         apply index_eq; lia.
                     +++ apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 13,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "exitcond300.not")))
        (Name "if.end43.preheader") (Name "if.end17"), []))
      (store_state s k n j data_address data_prov target_address target_prov m1 m2 value)
      (store_state s k n j data_address data_prov target_address target_prov m1 m2 value)
      (inl (if k + 1 =? n then Name "if.end43.preheader" else Name "if.end17"))).
    resolve_types. apply runs_branch. unfold store_state. entry_lookup.
Qed.

Definition validation_modified : list raw_id :=
  [Name "indvars.iv296"; Name "arrayidx19"; Anon 0; Name "cmp20.not";
   Name "idxprom24"; Name "arrayidx25"; Anon 1; Name "cmp26.not";
   Name "arrayidx33"; Anon 2; Name "arrayidx35";
   Name "indvars.iv.next297"; Name "exitcond300.not"].

Definition iteration_state layout bd bp bt bu s k n j m1 m2 value :=
  store_state
    (unused_state (range_state s k j (block_address layout bp) (block_provenance layout bp))
      j (block_address layout bu) (block_provenance layout bu))
    k n j (block_address layout bd) (block_provenance layout bd)
    (block_address layout bt) (block_provenance layout bt) m1 m2 value.

Lemma iteration_memory layout bd bp bt bu s k n j m1 m2 value :
  fst (iteration_state layout bd bp bt bu s k n j m1 m2 value) = m2.
Proof. unfold iteration_state, store_state; rewrite !memory_set_local; reflexivity. Qed.

Lemma iteration_other layout bd bp bt bu s k n j m1 m2 value id :
  ~ In id validation_modified ->
  Maps.lookup id (locals (iteration_state layout bd bp bt bu s k n j m1 m2 value)) =
    Maps.lookup id (locals s).
Proof.
  intro Outside. unfold iteration_state, store_state, unused_state, range_state.
  repeat first [rewrite lookup_local_other by
    (intro E; subst; apply Outside; unfold validation_modified; simpl; tauto)
    | rewrite locals_with_memory]. reflexivity.
Qed.

Lemma iteration_next layout bd bp bt bu s k n j m1 m2 value :
  validation_input (Name "if.end29")
    (iteration_state layout bd bp bt bu s k n j m1 m2 value) (k + 1).
Proof.
  right; split; [reflexivity|]. unfold iteration_state, store_state.
  rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.
