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

Definition choose_head : {b : LLVMAst.block dtyp | FullCFG.named_block "while.cond106" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 22 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_zero : {b : LLVMAst.block dtyp | FullCFG.named_block "while.cond112" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 23 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_preheader : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end117.preheader" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 24 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_scan : {b : LLVMAst.block dtyp | FullCFG.named_block "if.end117" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 25 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_exit : {b : LLVMAst.block dtyp | FullCFG.named_block "while.end125.loopexit" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 26 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_result : {b : LLVMAst.block dtyp | FullCFG.named_block "while.end125" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 27 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition choose_head_state s value top :=
  set_local (set_local s (Anon 11) (word_value value))
    (Name "cmp110") (boolean_value (word_equal value top)).

Definition choose_zero_state s value :=
  set_local s (Name "cmp114.old.not") (boolean_value (word_equal value Int.zero)).

Definition choose_scan_input from s k : Prop :=
  (from = Name "if.end117.preheader" /\ Maps.lookup (Anon 12) (locals s) = Some (index_value k)) \/
  (from = Name "if.end117" /\ Maps.lookup (Name "indvars.iv.next317") (locals s) = Some (index_value k)).

Definition choose_continue k value := andb (k - 1 =? value) (negb (k - 1 =? 0)).

Definition choose_scan_state s k pa pp value :=
  let s1 := set_local s (Name "indvars.iv316") (index_value k) in
  let s2 := set_local s1 (Anon 13) (index_value (k - 1)) in
  let s3 := set_local s2 (Name "indvars.iv.next317") (index_value (k - 1)) in
  let s4 := set_local s3 (Name "arrayidx120") (pointer_value (pa + 4 * (k - 1)) pp) in
  let s5 := set_local s4 (Anon 14) (word_value (Int.repr value)) in
  let s6 := set_local s5 (Anon 15) (index_value value) in
  let s7 := set_local s6 (Name "cmp121.wide") (boolean_value (k - 1 =? value)) in
  let s8 := set_local s7 (Name "cmp114.wide") (boolean_value (negb (k - 1 =? 0))) in
  set_local s8 (Name "or.cond") (boolean_value (choose_continue k value)).

Definition choose_result_input from s k : Prop :=
  (from = Name "while.cond112" /\ k = 0) \/
  (from = Name "while.end125.loopexit" /\
   Maps.lookup (Anon 16) (locals s) = Some (word_value (Int.repr k))).

Definition choose_result_state s k pa pp value :=
  let s1 := set_local s (Name "v11.1") (word_value (Int.repr k)) in
  let s2 := set_local s1 (Name "idxprom126") (index_value k) in
  let s3 := set_local s2 (Name "arrayidx127") (pointer_value (pa + 4 * k) pp) in
  let s4 := set_local s3 (Anon 17) (word_value value) in
  set_local s4 (Name "cmp128") (boolean_value (word_equal value (Int.repr k))).

Lemma choose_head_runs from varargs s pa pp value top :
  Maps.lookup (Name "arrayidx109") (locals s) = Some (pointer_value pa pp) ->
  Maps.lookup (Name "sub") (locals s) = Some (word_value top) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (pa, pp)) (fst s) = Ret (fst s, word_value value) ->
  runs (denote_block (proj1_sig choose_head) from varargs) s (choose_head_state s value top)
    (inl (if word_equal value top then Name "while.cond112" else Name "if.end133")).
Proof.
  intros TopPointer Top Read. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_read with (value := word_value value); [entry_lookup|].
      resolve_types. exact Read.
    + eapply runs_code_cons.
      * apply runs_assign with (value := boolean_value (word_equal value top)).
        eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
        cbv beta delta [endo Endo_id].
        lazymatch goal with |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq end.
      * apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 32,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp110")))
        (Name "while.cond112") (Name "if.end133"), []))
      (choose_head_state s value top) (choose_head_state s value top)
      (inl (if word_equal value top then Name "while.cond112" else Name "if.end133"))).
    resolve_types. apply runs_branch. unfold choose_head_state. entry_lookup.
Qed.

Lemma choose_zero_runs from varargs s value :
  Maps.lookup (Anon 11) (locals s) = Some (word_value value) ->
  runs (denote_block (proj1_sig choose_zero) from varargs) s (choose_zero_state s value)
    (inl (if word_equal value Int.zero then Name "while.end125" else Name "if.end117.preheader")).
Proof.
  intro Value. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := boolean_value (word_equal value Int.zero)).
      eapply runs_expression_icmp with (vb := word_value Int.zero).
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * cbv beta delta [endo Endo_id].
        lazymatch goal with |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq end.
    + apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 33,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp114.old.not")))
        (Name "while.end125") (Name "if.end117.preheader"), []))
      (choose_zero_state s value) (choose_zero_state s value)
      (inl (if word_equal value Int.zero then Name "while.end125" else Name "if.end117.preheader"))).
    resolve_types. apply runs_branch. unfold choose_zero_state. entry_lookup.
Qed.

Lemma choose_preheader_runs from varargs s k :
  0 <= k <= 1024 -> Maps.lookup (Anon 11) (locals s) = Some (word_value (Int.repr k)) ->
  runs (denote_block (proj1_sig choose_preheader) from varargs) s
    (set_local s (Anon 12) (index_value k)) (inl (Name "if.end117")).
Proof.
  intros Bound Value. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value k).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by exact Bound. reflexivity.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma choose_scan_phi from s k : choose_scan_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig choose_scan))) s
    (set_local s (Name "indvars.iv316") (index_value k)) tt.
Proof.
  intros [[-> Value]|[-> Value]]; eapply runs_phis_single.
  - apply assoc_hd.
  - entry_lookup.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma choose_scan_runs from varargs s k pa pp value :
  0 < k <= 1024 -> 0 <= value <= 1024 -> choose_scan_input from s k ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value pa pp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (pa + 4 * (k - 1), pp)) (fst s) =
    Ret (fst s, word_value (Int.repr value)) ->
  runs (denote_block (proj1_sig choose_scan) from varargs) s (choose_scan_state s k pa pp value)
    (inl (if choose_continue k value then Name "if.end117" else Name "while.end125.loopexit")).
Proof.
  intros Bound ValueBound Input Perm Read. eapply runs_block; [apply choose_scan_phi, Input| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value (k - 1)).
      eapply runs_expression_ibinop with (vb := index_value (-1)).
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * apply index_decrement.
    + eapply runs_code_cons.
      * apply runs_assign with (value := index_value (k - 1)).
        eapply runs_expression_ibinop with (vb := index_value (-1)).
        -- entry_lookup.
        -- apply runs_expression_integer. resolve_types. reflexivity.
        -- apply index_decrement.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := pointer_value (pa + 4 * (k - 1)) pp).
           eapply runs_expression_gep; [entry_lookup|entry_lookup|].
           resolve_types. apply index_gep; lia.
        -- eapply runs_code_cons.
           ++ eapply runs_instruction_read with (value := word_value (Int.repr value)).
              ** entry_lookup.
              ** resolve_types. rewrite !memory_set_local. exact Read.
           ++ eapply runs_code_cons.
              ** apply runs_assign with (value := index_value value).
                 eapply runs_expression_conversion; [entry_lookup|].
                 resolve_types. rewrite extend_word, small_unsigned by exact ValueBound. reflexivity.
              ** eapply runs_code_cons.
                 --- apply runs_assign with (value := boolean_value (k - 1 =? value)).
                     eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
                     cbv beta delta [endo Endo_id].
                     lazymatch goal with |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply index_eq; lia end.
                 --- eapply runs_code_cons.
                     +++ apply runs_assign with (value := boolean_value (negb (k - 1 =? 0))).
                         eapply runs_expression_icmp with (vb := index_value 0).
                         *** entry_lookup.
                         *** apply runs_expression_integer. resolve_types. reflexivity.
                         *** cbv beta delta [endo Endo_id].
                             lazymatch goal with
                             | |- @eval_icmp _ false LLVMAst.Ne _ _ = _ => apply index_ne; lia
                             end.
                     +++ eapply runs_code_cons.
                         *** apply runs_assign with (value := boolean_value (choose_continue k value)).
                             eapply runs_expression_ibinop; [entry_lookup|entry_lookup|].
                             cbv beta delta [endo Endo_id].
                             lazymatch goal with
                             | |- @eval_iop _ LLVMAst.And _ _ = _ => apply boolean_and
                             end.
                         *** apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 35,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "or.cond")))
        (Name "if.end117") (Name "while.end125.loopexit"), []))
      (choose_scan_state s k pa pp value) (choose_scan_state s k pa pp value)
      (inl (if choose_continue k value then Name "if.end117" else Name "while.end125.loopexit"))).
    resolve_types. apply runs_branch. unfold choose_scan_state. entry_lookup.
Qed.

Lemma choose_exit_runs from varargs s k :
  0 <= k <= 1024 -> Maps.lookup (Anon 13) (locals s) = Some (index_value k) ->
  runs (denote_block (proj1_sig choose_exit) from varargs) s
    (set_local s (Anon 16) (word_value (Int.repr k))) (inl (Name "while.end125")).
Proof.
  intros Bound Value. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := word_value (Int.repr k)).
      eapply runs_expression_conversion; [entry_lookup|]. resolve_types. apply truncate_index, Bound.
    + apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma choose_result_phi from s k : choose_result_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig choose_result))) s
    (set_local s (Name "v11.1") (word_value (Int.repr k))) tt.
Proof.
  intros [[-> ->]|[-> Value]]; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma choose_result_runs from varargs s k pa pp value :
  0 <= k <= 1024 -> choose_result_input from s k ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value pa pp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (pa + 4 * k, pp)) (fst s) = Ret (fst s, word_value value) ->
  runs (denote_block (proj1_sig choose_result) from varargs) s (choose_result_state s k pa pp value)
    (inl (if word_equal value (Int.repr k) then Name "cleanup" else Name "if.end133")).
Proof.
  intros Bound Input Perm Read. eapply runs_block; [apply choose_result_phi, Input| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := index_value k).
      eapply runs_expression_conversion; [entry_lookup|].
      resolve_types. rewrite extend_word, small_unsigned by exact Bound. reflexivity.
    + eapply runs_code_cons.
      * apply runs_assign with (value := pointer_value (pa + 4 * k) pp).
        eapply runs_expression_gep; [entry_lookup|entry_lookup|]. resolve_types. apply index_gep, Bound.
      * eapply runs_code_cons.
        -- eapply runs_instruction_read with (value := word_value value); [entry_lookup|].
           resolve_types. rewrite !memory_set_local. exact Read.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := boolean_value (word_equal value (Int.repr k))).
              eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
              cbv beta delta [endo Endo_id].
              lazymatch goal with |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq end.
           ++ apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 37,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp128")))
        (Name "cleanup") (Name "if.end133"), []))
      (choose_result_state s k pa pp value) (choose_result_state s k pa pp value)
      (inl (if word_equal value (Int.repr k) then Name "cleanup" else Name "if.end133"))).
    resolve_types. apply runs_branch. unfold choose_result_state. entry_lookup.
Qed.

Definition choose_modified : list raw_id :=
  [Anon 11; Name "cmp110"; Name "cmp114.old.not"; Anon 12; Name "indvars.iv316";
   Anon 13; Name "indvars.iv.next317"; Name "arrayidx120"; Anon 14; Anon 15;
   Name "cmp121.wide"; Name "cmp114.wide"; Name "or.cond"; Anon 16;
   Name "v11.1"; Name "idxprom126"; Name "arrayidx127"; Anon 17; Name "cmp128"].

Ltac choose_locals := repeat rewrite lookup_local_other by
  (intro E; subst; match goal with H : ~ In _ choose_modified |- _ =>
    apply H; unfold choose_modified; simpl; tauto end).

Lemma choose_head_memory s value top : fst (choose_head_state s value top) = fst s.
Proof. unfold choose_head_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma choose_zero_memory s value : fst (choose_zero_state s value) = fst s.
Proof. unfold choose_zero_state. apply memory_set_local. Qed.

Lemma choose_scan_memory s k pa pp value : fst (choose_scan_state s k pa pp value) = fst s.
Proof. unfold choose_scan_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma choose_result_memory s k pa pp value : fst (choose_result_state s k pa pp value) = fst s.
Proof. unfold choose_result_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma choose_head_other s value top id : ~ In id choose_modified ->
  Maps.lookup id (locals (choose_head_state s value top)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold choose_head_state. choose_locals. reflexivity. Qed.

Lemma choose_zero_other s value id : ~ In id choose_modified ->
  Maps.lookup id (locals (choose_zero_state s value)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold choose_zero_state. choose_locals. reflexivity. Qed.

Lemma choose_scan_other s k pa pp value id : ~ In id choose_modified ->
  Maps.lookup id (locals (choose_scan_state s k pa pp value)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold choose_scan_state. choose_locals. reflexivity. Qed.

Lemma choose_result_other s k pa pp value id : ~ In id choose_modified ->
  Maps.lookup id (locals (choose_result_state s k pa pp value)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold choose_result_state. choose_locals. reflexivity. Qed.

Lemma choose_head_value s value top :
  Maps.lookup (Anon 11) (locals (choose_head_state s value top)) = Some (word_value value).
Proof. unfold choose_head_state. rewrite lookup_local_other by discriminate. apply lookup_local_same. Qed.

Lemma choose_scan_index s k pa pp value :
  Maps.lookup (Anon 13) (locals (choose_scan_state s k pa pp value)) = Some (index_value (k - 1)).
Proof. unfold choose_scan_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same. Qed.

Lemma choose_scan_next s k pa pp value :
  choose_scan_input (Name "if.end117") (choose_scan_state s k pa pp value) (k - 1).
Proof.
  right; split; [reflexivity|]. unfold choose_scan_state.
  rewrite !lookup_local_other by discriminate. apply lookup_local_same.
Qed.

Lemma choose_result_value s k pa pp value :
  Maps.lookup (Name "v11.1") (locals (choose_result_state s k pa pp value)) = Some (word_value (Int.repr k)).
Proof. unfold choose_result_state. rewrite !lookup_local_other by discriminate. apply lookup_local_same. Qed.
