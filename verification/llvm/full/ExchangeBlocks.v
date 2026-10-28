(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers.
From Vellvm Require Import Utils Syntax TypToDtyp ScopeTheory Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index
  WordArithmetic FixedBlocks Choose.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition exchange_compare : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end133" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 28 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition exchange_depth : {b : LLVMAst.block dtyp | FullCFG.named_block "if.then139" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 29 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition exchange_blocked : {b : LLVMAst.block dtyp | FullCFG.named_block "if.then142" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 30 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition exchange_capacity : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end147" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 31 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition exchange_permutation : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end169" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 33 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition exchange_compare_state s k da dp x y :=
  let s1 := set_local s (Name "v11.2") (word_value (Int.repr k)) in
  let s2 := set_local s1 (Name "idxprom134") (index_value k) in
  let s3 := set_local s2 (Name "arrayidx135") (pointer_value (da + 4 * k) dp) in
  let s4 := set_local s3 (Anon 18) (word_value x) in
  let s5 := set_local s4 (Anon 19) (word_value y) in
  set_local s5 (Name "cmp138.not") (boolean_value (word_equal x y)).

Definition exchange_depth_state s d k :=
  let s1 := set_local s (Name "sub140") (word_value (Int.repr (d - k))) in
  set_local s1 (Name "cmp141") (boolean_value (16 <? d - k)).

Definition exchange_blocked_state s depth m1 m2 :=
  with_memory (set_local (with_memory s m1) (Name "sub144")
    (word_value (Int.repr (depth - 16)))) m2.

Definition exchange_capacity_state s count capacity :=
  set_local (set_local s (Anon 20) (word_value count)) (Name "cmp150.not")
    (boolean_value (Int.unsigned count <? Int.unsigned capacity)).

Definition exchange_permutation_state s k pa pp x y m1 m2 :=
  let s1 := set_local s (Name "arrayidx171") (pointer_value (pa + 4 * k) pp) in
  let s2 := set_local s1 (Anon 23) (word_value x) in
  let s3 := set_local s2 (Anon 24) (word_value y) in
  with_memory (with_memory s3 m1) m2.

Lemma exchange_compare_phi from s k : choose_binding from s (Some k) ->
  runs (denote_phis from (blk_phis (proj1_sig exchange_compare))) s
    (set_local s (Name "v11.2") (word_value (Int.repr (Z.of_nat k)))) tt.
Proof.
  intros [[-> Value]|[-> Value]]; eapply runs_phis_single.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
  - apply assoc_hd.
  - entry_lookup.
Qed.

Lemma exchange_compare_runs from varargs s k da dp top_address x y :
  (k <= 1024)%nat -> choose_binding from s (Some k) ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value da dp) ->
  Maps.lookup (Name "arrayidx137") (locals s) = Some (pointer_value top_address dp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (da + 4 * Z.of_nat k, dp)) (fst s) =
    Ret (fst s, word_value x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (top_address, dp)) (fst s) =
    Ret (fst s, word_value y) ->
  runs (denote_block (proj1_sig exchange_compare) from varargs) s
    (exchange_compare_state s (Z.of_nat k) da dp x y)
    (inl (if word_equal x y then Name "if.end169" else Name "if.then139")).
Proof.
  intros Bound Input Data Top ReadSelected ReadTop.
  eapply runs_block; [apply exchange_compare_phi, Input| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (Z.of_nat k)).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by lia. reflexivity.
    + eapply runs_code_cons.
      * apply runs_assign with (value := pointer_value (da + 4 * Z.of_nat k) dp).
        eapply runs_expression_gep; [entry_lookup|entry_lookup|].
        resolve_types. apply index_gep; lia.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value x).
           ++ entry_lookup.
           ++ resolve_types. rewrite !memory_set_local. exact ReadSelected.
        -- eapply runs_code_cons.
           ++ eapply runs_instruction_read with (value := word_value y).
              ** entry_lookup.
              ** resolve_types. rewrite !memory_set_local. exact ReadTop.
           ++ eapply runs_code_cons.
              ** apply runs_assign with (value := boolean_value (word_equal x y)).
                 eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
                 cbv beta delta [endo Endo_id].
                 lazymatch goal with |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq end.
              ** apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 38,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp138.not")))
        (Name "if.end169") (Name "if.then139"), []))
      (exchange_compare_state s (Z.of_nat k) da dp x y)
      (exchange_compare_state s (Z.of_nat k) da dp x y)
      (inl (if word_equal x y then Name "if.end169" else Name "if.then139"))).
    resolve_types. apply runs_branch. unfold exchange_compare_state. entry_lookup.
Qed.

Lemma exchange_depth_runs from varargs s d k :
  0 <= k <= d -> d <= 1024 ->
  Maps.lookup (Name "sub") (locals s) = Some (word_value (Int.repr d)) ->
  Maps.lookup (Name "v11.2") (locals s) = Some (word_value (Int.repr k)) ->
  runs (denote_block (proj1_sig exchange_depth) from varargs) s
    (exchange_depth_state s d k)
    (inl (if 16 <? d - k then Name "if.then142" else Name "if.end147")).
Proof.
  intros K D Top Position. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := word_value (Int.repr (d - k))).
      eapply runs_expression_ibinop; [entry_lookup|entry_lookup|].
      apply word_sub.
    + eapply runs_code_cons.
      * apply runs_assign with (value := boolean_value (16 <? d - k)).
        eapply runs_expression_icmp with (vb := word_value (Int.repr 16)).
        -- entry_lookup.
        -- apply runs_expression_integer. resolve_types. reflexivity.
        -- cbv beta delta [endo Endo_id].
           lazymatch goal with |- @eval_icmp _ false LLVMAst.Ugt _ _ = _ => rewrite word_gt end.
           rewrite !small_unsigned by lia. reflexivity.
      * apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 39,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp141")))
        (Name "if.then142") (Name "if.end147"), []))
      (exchange_depth_state s d k) (exchange_depth_state s d k)
      (inl (if 16 <? d - k then Name "if.then142" else Name "if.end147"))).
    resolve_types. apply runs_branch. unfold exchange_depth_state. entry_lookup.
Qed.

Lemma exchange_blocked_runs from varargs s k depth oa op m1 m2 :
  Maps.lookup (Name "v11.2") (locals s) = Some (word_value (Int.repr k)) ->
  Maps.lookup (Name "sub140") (locals s) = Some (word_value (Int.repr depth)) ->
  Maps.lookup (Name "arrayidx1") (locals s) = Some (pointer_value (oa + 4) op) ->
  Maps.lookup (Name "arrayidx2") (locals s) = Some (pointer_value (oa + 8) op) ->
  run_memory (Impl.write_dvalue (oa + 4, op) (DTYPE_I 32) (word_value (Int.repr k)))
    (fst s) = Ret (m1, tt) ->
  run_memory (Impl.write_dvalue (oa + 8, op) (DTYPE_I 32) (word_value (Int.repr (depth - 16))))
    m1 = Ret (m2, tt) ->
  runs (denote_block (proj1_sig exchange_blocked) from varargs) s
    (exchange_blocked_state s depth m1 m2) (inl (Name "cleanup")).
Proof.
  intros Position Depth Field1 Field2 Write1 Write2. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_store; [entry_lookup|entry_lookup|].
      resolve_types. exact Write1.
    + eapply runs_code_cons.
      * apply runs_assign with (value := word_value (Int.repr (depth - 16))).
        eapply runs_expression_ibinop with (vb := word_value (Int.repr (-16))).
        -- entry_lookup.
        -- apply runs_expression_integer. resolve_types. rewrite word_repr. reflexivity.
        -- replace (depth - 16) with (depth + -16) by ring. apply word_add.
      * eapply runs_code_cons.
        -- eapply runs_instruction_store; [entry_lookup|entry_lookup|].
           resolve_types. rewrite memory_set_local. exact Write2.
        -- apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma exchange_capacity_runs from varargs s oa op count capacity :
  Maps.lookup (Name "v7") (locals s) = Some (pointer_value oa op) ->
  Maps.lookup (Name "add149") (locals s) = Some (word_value capacity) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (oa, op)) (fst s) =
    Ret (fst s, word_value count) ->
  runs (denote_block (proj1_sig exchange_capacity) from varargs) s
    (exchange_capacity_state s count capacity)
    (inl (if Int.unsigned count <? Int.unsigned capacity then Name "if.end153" else Name "cleanup")).
Proof.
  intros Output Capacity Read. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_read with (value := word_value count); [entry_lookup|].
      resolve_types. exact Read.
    + eapply runs_code_cons.
      * apply runs_assign with (value := boolean_value (Int.unsigned count <? Int.unsigned capacity)).
        eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
        cbv beta delta [endo Endo_id].
        lazymatch goal with |- @eval_icmp _ false LLVMAst.Ult _ _ = _ => apply word_lt end.
      * apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 43,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp150.not")))
        (Name "if.end153") (Name "cleanup"), []))
      (exchange_capacity_state s count capacity) (exchange_capacity_state s count capacity)
      (inl (if Int.unsigned count <? Int.unsigned capacity then Name "if.end153" else Name "cleanup"))).
    resolve_types. apply runs_branch. unfold exchange_capacity_state. entry_lookup.
Qed.

Lemma exchange_permutation_runs from varargs s k pa pp top_address x y m1 m2 :
  0 <= k <= 1024 ->
  Maps.lookup (Name "idxprom134") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value pa pp) ->
  Maps.lookup (Name "arrayidx109") (locals s) = Some (pointer_value top_address pp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (pa + 4 * k, pp)) (fst s) =
    Ret (fst s, word_value x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (top_address, pp)) (fst s) =
    Ret (fst s, word_value y) ->
  run_memory (Impl.write_dvalue (pa + 4 * k, pp) (DTYPE_I 32) (word_value y)) (fst s) =
    Ret (m1, tt) ->
  run_memory (Impl.write_dvalue (top_address, pp) (DTYPE_I 32) (word_value x)) m1 =
    Ret (m2, tt) ->
  runs (denote_block (proj1_sig exchange_permutation) from varargs) s
    (exchange_permutation_state s k pa pp x y m1 m2) (inl (Name "while.cond106")).
Proof.
  intros Bound Index Perm Top ReadSelected ReadTop WriteSelected WriteTop.
  eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (pa + 4 * k) pp).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, Bound.
    + eapply runs_code_cons.
      * eapply runs_instruction_read with (value := word_value x).
        -- entry_lookup.
        -- resolve_types. rewrite memory_set_local. exact ReadSelected.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value y).
           ++ entry_lookup.
           ++ resolve_types. rewrite !memory_set_local. exact ReadTop.
        -- eapply runs_code_cons.
           ++ eapply runs_instruction_store; [entry_lookup|entry_lookup|].
              resolve_types. rewrite !memory_set_local. exact WriteSelected.
           ++ eapply runs_code_cons.
              ** eapply runs_instruction_store; [entry_lookup|entry_lookup|].
                 resolve_types. exact WriteTop.
              ** apply runs_code_nil.
  - apply runs_jump.
Qed.

Definition exchange_modified : list raw_id :=
  [Name "v11.2"; Name "idxprom134"; Name "arrayidx135"; Anon 18; Anon 19;
   Name "cmp138.not"; Name "sub140"; Name "cmp141"; Name "sub144";
   Anon 20; Name "cmp150.not"; Name "arrayidx171"; Anon 23; Anon 24].

Lemma exchange_compare_memory s k da dp x y :
  fst (exchange_compare_state s k da dp x y) = fst s.
Proof. unfold exchange_compare_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma exchange_depth_memory s d k : fst (exchange_depth_state s d k) = fst s.
Proof. unfold exchange_depth_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma exchange_capacity_memory s count capacity :
  fst (exchange_capacity_state s count capacity) = fst s.
Proof. unfold exchange_capacity_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma exchange_blocked_memory s depth m1 m2 : fst (exchange_blocked_state s depth m1 m2) = m2.
Proof. reflexivity. Qed.

Lemma exchange_permutation_memory s k pa pp x y m1 m2 :
  fst (exchange_permutation_state s k pa pp x y m1 m2) = m2.
Proof. reflexivity. Qed.

Ltac exchange_local_frame id :=
  let Outside := fresh "Outside" in
  intro Outside; repeat rewrite locals_with_memory;
  repeat rewrite lookup_local_other by
    (intro E; subst id; apply Outside; unfold exchange_modified; simpl; tauto);
  reflexivity.

Lemma exchange_compare_other s k da dp x y id : ~ In id exchange_modified ->
  Maps.lookup id (locals (exchange_compare_state s k da dp x y)) = Maps.lookup id (locals s).
Proof. unfold exchange_compare_state. exchange_local_frame id. Qed.

Lemma exchange_depth_other s d k id : ~ In id exchange_modified ->
  Maps.lookup id (locals (exchange_depth_state s d k)) = Maps.lookup id (locals s).
Proof. unfold exchange_depth_state. exchange_local_frame id. Qed.

Lemma exchange_capacity_other s count capacity id : ~ In id exchange_modified ->
  Maps.lookup id (locals (exchange_capacity_state s count capacity)) = Maps.lookup id (locals s).
Proof. unfold exchange_capacity_state. exchange_local_frame id. Qed.

Lemma exchange_blocked_other s depth m1 m2 id : ~ In id exchange_modified ->
  Maps.lookup id (locals (exchange_blocked_state s depth m1 m2)) = Maps.lookup id (locals s).
Proof.
  unfold exchange_blocked_state. intro Outside.
  rewrite locals_with_memory, lookup_local_other by
    (intro E; subst id; apply Outside; unfold exchange_modified; simpl; tauto).
  rewrite locals_with_memory. reflexivity.
Qed.

Lemma exchange_permutation_other s k pa pp x y m1 m2 id : ~ In id exchange_modified ->
  Maps.lookup id (locals (exchange_permutation_state s k pa pp x y m1 m2)) = Maps.lookup id (locals s).
Proof. unfold exchange_permutation_state. exchange_local_frame id. Qed.

Lemma exchange_compare_bindings s k da dp x y :
  Maps.lookup (Name "v11.2") (locals (exchange_compare_state s k da dp x y)) =
    Some (word_value (Int.repr k)) /\
  Maps.lookup (Name "idxprom134") (locals (exchange_compare_state s k da dp x y)) =
    Some (index_value k) /\
  Maps.lookup (Name "arrayidx135") (locals (exchange_compare_state s k da dp x y)) =
    Some (pointer_value (da + 4 * k) dp) /\
  Maps.lookup (Anon 18) (locals (exchange_compare_state s k da dp x y)) = Some (word_value x) /\
  Maps.lookup (Anon 19) (locals (exchange_compare_state s k da dp x y)) = Some (word_value y).
Proof.
  unfold exchange_compare_state. repeat split;
    repeat rewrite lookup_local_other by discriminate; apply lookup_local_same.
Qed.

Lemma exchange_depth_binding s d k :
  Maps.lookup (Name "sub140") (locals (exchange_depth_state s d k)) =
    Some (word_value (Int.repr (d - k))).
Proof. unfold exchange_depth_state. rewrite lookup_local_other by discriminate. apply lookup_local_same. Qed.
