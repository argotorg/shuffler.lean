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

Definition search_used : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end77" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 14 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition search_target : {b : LLVMAst.block dtyp | FullCFG.named_block "if.then81" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 15 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition search_next : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end91" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 16 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition search_exit : {b : LLVMAst.block dtyp | FullCFG.named_block "while.end93.split.loop.exit" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 17 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition search_result : {b : LLVMAst.block dtyp | FullCFG.named_block "while.end93" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 18 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition search_input from s k : Prop :=
  (from = Name "if.end65" /\ k = 0) \/
  (from = Name "if.end91" /\
   Maps.lookup (Name "indvars.iv.next307") (locals s) = Some (index_value k)).

Definition search_used_state s k address provenance flag :=
  let s1 := set_local s (Name "indvars.iv306") (index_value k) in
  let s2 := set_local s1 (Name "arrayidx79") (pointer_value (address + 4 * k) provenance) in
  let s3 := set_local s2 (Anon 8) (word_value flag) in
  set_local s3 (Name "cmp80") (boolean_value (word_equal flag Int.zero)).

Definition search_target_state s k address provenance x y :=
  let s1 := set_local s (Name "arrayidx85") (pointer_value (address + 4 * k) provenance) in
  let s2 := set_local s1 (Anon 9) (word_value y) in
  set_local s2 (Name "cmp86") (boolean_value (word_equal x y)).

Definition search_next_state s k n :=
  let s1 := set_local s (Name "indvars.iv.next307") (index_value (k + 1)) in
  set_local s1 (Name "exitcond310.not") (boolean_value (k + 1 =? n)).

Definition search_result_state s k n :=
  let s1 := set_local s (Name "v9.0.lcssa") (word_value (Int.repr k)) in
  set_local s1 (Name "cmp94") (boolean_value (k =? n)).

Lemma search_phi from s k : search_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig search_used))) s
    (set_local s (Name "indvars.iv306") (index_value k)) tt.
Proof.
  intros [[-> ->]|[-> Next]]; eapply runs_phis_single.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - apply runs_expression_integer. resolve_types. reflexivity.
  - apply assoc_hd.
  - entry_lookup.
Qed.

Lemma search_used_runs from varargs (s : FusedS) k address provenance flag :
  0 <= k <= 1024 -> search_input from s k ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (address + 4 * k, provenance)) (fst s) =
    Ret (fst s, word_value flag) ->
  runs (denote_block (proj1_sig search_used) from varargs) s
    (search_used_state s k address provenance flag)
    (inl (if word_equal flag Int.zero then Name "if.then81" else Name "if.end91")).
Proof.
  intros Bound Input Used Read.
  eapply runs_block; [apply search_phi, Input| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, Bound.
    + eapply runs_code_cons.
      * eapply runs_instruction_read with (value := word_value flag).
        -- entry_lookup.
        -- resolve_types. rewrite !memory_set_local. exact Read.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := boolean_value (word_equal flag Int.zero)).
           eapply runs_expression_icmp with (vb := word_value Int.zero).
           ++ entry_lookup.
           ++ apply runs_expression_integer. resolve_types. reflexivity.
           ++ apply word_eq.
        -- apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 22,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp80")))
        (Name "if.then81") (Name "if.end91"), []))
      (search_used_state s k address provenance flag) (search_used_state s k address provenance flag)
      (inl (if word_equal flag Int.zero then Name "if.then81" else Name "if.end91"))).
    resolve_types. apply runs_branch. unfold search_used_state. entry_lookup.
Qed.

Lemma search_target_runs from varargs (s : FusedS) k address provenance x y :
  0 <= k <= 1024 ->
  Maps.lookup (Name "indvars.iv306") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value address provenance) ->
  Maps.lookup (Anon 6) (locals s) = Some (word_value x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (address + 4 * k, provenance)) (fst s) =
    Ret (fst s, word_value y) ->
  runs (denote_block (proj1_sig search_target) from varargs) s
    (search_target_state s k address provenance x y)
    (inl (if word_equal x y then Name "while.end93.split.loop.exit" else Name "if.end91")).
Proof.
  intros Bound Index Target Source Read. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, Bound.
    + eapply runs_code_cons.
      * eapply runs_instruction_read with (value := word_value y).
        -- entry_lookup.
        -- resolve_types. rewrite memory_set_local. exact Read.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := boolean_value (word_equal x y)).
           eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
           cbv beta delta [endo Endo_id].
           lazymatch goal with
           | |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq
           end.
        -- apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 23,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp86")))
        (Name "while.end93.split.loop.exit") (Name "if.end91"), []))
      (search_target_state s k address provenance x y) (search_target_state s k address provenance x y)
      (inl (if word_equal x y then Name "while.end93.split.loop.exit" else Name "if.end91"))).
    resolve_types. apply runs_branch. unfold search_target_state. entry_lookup.
Qed.

Lemma search_next_runs from varargs (s : FusedS) k n :
  0 <= k < n -> n <= 1024 ->
  Maps.lookup (Name "indvars.iv306") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "wide.trip.count309") (locals s) = Some (index_value n) ->
  runs (denote_block (proj1_sig search_next) from varargs) s (search_next_state s k n)
    (inl (if k + 1 =? n then Name "while.end93" else Name "if.end77")).
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
  - change (runs (denote_terminator (IVoid 24,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "exitcond310.not")))
        (Name "while.end93") (Name "if.end77"), []))
      (search_next_state s k n) (search_next_state s k n)
      (inl (if k + 1 =? n then Name "while.end93" else Name "if.end77"))).
    resolve_types. apply runs_branch. unfold search_next_state. entry_lookup.
Qed.

Lemma search_exit_runs from varargs (s : FusedS) k :
  0 <= k <= 1024 ->
  Maps.lookup (Name "indvars.iv306") (locals s) = Some (index_value k) ->
  runs (denote_block (proj1_sig search_exit) from varargs) s
    (set_local s (Anon 10) (word_value (Int.repr k))) (inl (Name "while.end93")).
Proof.
  intros Bound Index. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := word_value (Int.repr k)).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. apply truncate_index, Bound.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma search_result_runs varargs (s : FusedS) k n :
  0 <= k <= 1024 -> 0 <= n <= 1024 ->
  Maps.lookup (Anon 10) (locals s) = Some (word_value (Int.repr k)) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr n)) ->
  runs (denote_block (proj1_sig search_result) (Name "while.end93.split.loop.exit") varargs)
    s (search_result_state s k n)
    (inl (if k =? n then Name "cleanup" else Name "if.end97")).
Proof.
  intros IndexBound Size Found SizeLocal.
  eapply runs_block_single_phi with (value := word_value (Int.repr k)).
  - apply assoc_hd.
  - entry_lookup.
  - eapply runs_code_cons.
    + apply runs_assign with (value := boolean_value (k =? n)).
      eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
      cbv beta delta [endo Endo_id].
      lazymatch goal with
      | |- @eval_icmp _ false LLVMAst.Eq _ _ = _ =>
          rewrite word_eq, !small_unsigned by assumption; reflexivity
      end.
    + apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 26,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp94")))
        (Name "cleanup") (Name "if.end97"), []))
      (search_result_state s k n) (search_result_state s k n)
      (inl (if k =? n then Name "cleanup" else Name "if.end97"))).
    resolve_types. apply runs_branch. unfold search_result_state. entry_lookup.
Qed.

Definition search_modified : list raw_id :=
  [Name "indvars.iv306"; Name "arrayidx79"; Anon 8; Name "cmp80";
   Name "arrayidx85"; Anon 9; Name "cmp86";
   Name "indvars.iv.next307"; Name "exitcond310.not"; Anon 10;
   Name "v9.0.lcssa"; Name "cmp94"].

Ltac search_locals :=
  repeat rewrite lookup_local_other by
    (intro E; subst; match goal with H : ~ In _ search_modified |- _ =>
      apply H; unfold search_modified; simpl; tauto end).

Lemma search_used_memory s k address provenance flag :
  fst (search_used_state s k address provenance flag) = fst s.
Proof. unfold search_used_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma search_target_memory s k address provenance x y :
  fst (search_target_state s k address provenance x y) = fst s.
Proof. unfold search_target_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma search_next_memory s k n : fst (search_next_state s k n) = fst s.
Proof. unfold search_next_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma search_result_memory s k n : fst (search_result_state s k n) = fst s.
Proof. unfold search_result_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma search_used_other s k address provenance flag id : ~ In id search_modified ->
  Maps.lookup id (locals (search_used_state s k address provenance flag)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold search_used_state. search_locals. reflexivity. Qed.

Lemma search_target_other s k address provenance x y id : ~ In id search_modified ->
  Maps.lookup id (locals (search_target_state s k address provenance x y)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold search_target_state. search_locals. reflexivity. Qed.

Lemma search_next_other s k n id : ~ In id search_modified ->
  Maps.lookup id (locals (search_next_state s k n)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold search_next_state. search_locals. reflexivity. Qed.

Lemma search_result_other s k n id : ~ In id search_modified ->
  Maps.lookup id (locals (search_result_state s k n)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold search_result_state. search_locals. reflexivity. Qed.

Lemma search_used_index s k address provenance flag :
  Maps.lookup (Name "indvars.iv306") (locals (search_used_state s k address provenance flag)) =
    Some (index_value k).
Proof.
  unfold search_used_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same.
Qed.

Lemma search_next_input s k n : search_input (Name "if.end91") (search_next_state s k n) (k + 1).
Proof.
  right; split; [reflexivity|]. unfold search_next_state.
  rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.

Lemma search_result_value s k n :
  Maps.lookup (Name "v9.0.lcssa") (locals (search_result_state s k n)) = Some (word_value (Int.repr k)).
Proof.
  unfold search_result_state. rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.
