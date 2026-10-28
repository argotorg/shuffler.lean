(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Utils Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations
  Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition word_equal x y := Int.unsigned x =? Int.unsigned y.
Definition flag_word (choice : bool) := Int.repr (if choice then 1 else 0).
Definition fixed_from (choice : bool) := if choice then Name "if.then49" else Name "if.end43".

Definition fixed_input from s k : Prop :=
  (from = Name "if.end43.preheader" /\ k = 0) \/
  (from = Name "if.end57" /\
   Maps.lookup (Name "indvars.iv.next302") (locals s) = Some (index_value k)).

Definition fixed_compare_state s k da dp ta tp x y :=
  let s1 := set_local s (Name "indvars.iv301") (index_value k) in
  let s2 := set_local s1 (Name "arrayidx45") (pointer_value (da + 4 * k) dp) in
  let s3 := set_local s2 (Anon 3) (word_value x) in
  let s4 := set_local s3 (Name "arrayidx47") (pointer_value (ta + 4 * k) tp) in
  let s5 := set_local s4 (Anon 4) (word_value y) in
  set_local s5 (Name "cmp48") (boolean_value (word_equal x y)).

Definition fixed_assign_state s k address provenance m :=
  let s1 := set_local s (Name "arrayidx51") (pointer_value (address + 4 * k) provenance) in
  let s2 := set_local s1 (Anon 5) (word_value (Int.repr k)) in
  with_memory s2 m.

Definition fixed_merge_state s k n address provenance choice m :=
  let s1 := set_local s (Name ".sink") (word_value (flag_word choice)) in
  let s2 := set_local s1 (Name "arrayidx56") (pointer_value (address + 4 * k) provenance) in
  let s3 := with_memory s2 m in
  let s4 := set_local s3 (Name "indvars.iv.next302") (index_value (k + 1)) in
  set_local s4 (Name "exitcond305.not") (boolean_value (k + 1 =? n)).

Lemma fixed_phi from s k : fixed_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig FullCFG.fixed_compare))) s
    (set_local s (Name "indvars.iv301") (index_value k)) tt.
Proof.
  intros [[-> ->]|[-> Next]]; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma fixed_compare_runs from varargs (s : FusedS) k da dp ta tp x y :
  0 <= k <= 1024 -> fixed_input from s k ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value da dp) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value ta tp) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (da + 4 * k, dp)) (fst s) =
    Ret (fst s, word_value x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32) (ta + 4 * k, tp)) (fst s) =
    Ret (fst s, word_value y) ->
  runs (denote_block (proj1_sig FullCFG.fixed_compare) from varargs) s
    (fixed_compare_state s k da dp ta tp x y)
    (inl (if word_equal x y then Name "if.then49" else Name "if.end57")).
Proof.
  intros Bound Input Data Target ReadData ReadTarget.
  eapply runs_block; [apply fixed_phi, Input| |].
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
                 (* Reject a changed opcode before evaluating integer comparisons. *)
                 cbv beta delta [endo Endo_id].
                 lazymatch goal with
                 | |- @eval_icmp _ false LLVMAst.Eq _ _ = _ => apply word_eq
                 end.
              ** apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 15,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp48")))
        (Name "if.then49") (Name "if.end57"), []))
      (fixed_compare_state s k da dp ta tp x y) (fixed_compare_state s k da dp ta tp x y)
      (inl (if word_equal x y then Name "if.then49" else Name "if.end57"))).
    resolve_types. apply runs_branch. unfold fixed_compare_state. entry_lookup.
Qed.

Lemma fixed_assign_runs from varargs (s : FusedS) k address provenance (m : Impl.State) :
  0 <= k <= 1024 ->
  Maps.lookup (Name "indvars.iv301") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.write_dvalue (address + 4 * k, provenance) (DTYPE_I 32)
    (word_value (Int.repr k))) (fst s) = Ret (m, tt) ->
  runs (denote_block (proj1_sig FullCFG.fixed_assign) from varargs) s
    (fixed_assign_state s k address provenance m) (inl (Name "if.end57")).
Proof.
  intros Bound Index Base Write. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep, Bound.
    + eapply runs_code_cons.
      * apply runs_assign with (value := word_value (Int.repr k)).
        eapply runs_expression_conversion; [entry_lookup|].
        resolve_types. apply truncate_index, Bound.
      * eapply runs_code_cons.
        -- eapply runs_instruction_store; [entry_lookup|entry_lookup|].
           resolve_types. rewrite !memory_set_local. exact Write.
        -- apply runs_code_nil.
  - apply runs_jump.
Qed.

Lemma fixed_flag_phi choice s :
  runs (denote_phis (fixed_from choice) (blk_phis (proj1_sig FullCFG.fixed_merge))) s
    (set_local s (Name ".sink") (word_value (flag_word choice))) tt.
Proof.
  destruct choice; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - apply runs_expression_integer. resolve_types. reflexivity.
Qed.

Lemma fixed_merge_runs varargs (s : FusedS) k n address provenance choice (m : Impl.State) :
  0 <= k < n -> n <= 1024 ->
  Maps.lookup (Name "indvars.iv301") (locals s) = Some (index_value k) ->
  Maps.lookup (Name "wide.trip.count304") (locals s) = Some (index_value n) ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.write_dvalue (address + 4 * k, provenance) (DTYPE_I 32)
    (word_value (flag_word choice))) (fst s) = Ret (m, tt) ->
  runs (denote_block (proj1_sig FullCFG.fixed_merge) (fixed_from choice) varargs) s
    (fixed_merge_state s k n address provenance choice m)
    (inl (if k + 1 =? n then Name "if.end65.preheader" else Name "if.end43")).
Proof.
  intros K N Index Count Base Write.
  eapply runs_block; [apply fixed_flag_phi| |].
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep; [entry_lookup|entry_lookup|].
      resolve_types. apply index_gep. lia.
    + eapply runs_code_cons.
      * eapply runs_instruction_store; [entry_lookup|entry_lookup|].
        resolve_types. rewrite !memory_set_local. exact Write.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := index_value (k + 1)).
           eapply runs_expression_ibinop with (vb := index_value 1).
           ++ entry_lookup.
           ++ apply runs_expression_integer. resolve_types. reflexivity.
           ++ apply index_add. lia.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := boolean_value (k + 1 =? n)).
              eapply runs_expression_icmp; [entry_lookup|entry_lookup|].
              apply index_eq; lia.
           ++ apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 19,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "exitcond305.not")))
        (Name "if.end65.preheader") (Name "if.end43"), []))
      (fixed_merge_state s k n address provenance choice m)
      (fixed_merge_state s k n address provenance choice m)
      (inl (if k + 1 =? n then Name "if.end65.preheader" else Name "if.end43"))).
    resolve_types. apply runs_branch. unfold fixed_merge_state. entry_lookup.
Qed.

Definition fixed_modified : list raw_id :=
  [Name "indvars.iv301"; Name "arrayidx45"; Anon 3; Name "arrayidx47"; Anon 4;
   Name "cmp48"; Name "arrayidx51"; Anon 5; Name ".sink"; Name "arrayidx56";
   Name "indvars.iv.next302"; Name "exitcond305.not"].

Lemma fixed_compare_memory s k da dp ta tp x y :
  fst (fixed_compare_state s k da dp ta tp x y) = fst s.
Proof. unfold fixed_compare_state. rewrite !memory_set_local. reflexivity. Qed.

Lemma fixed_assign_memory s k address provenance m :
  fst (fixed_assign_state s k address provenance m) = m.
Proof. reflexivity. Qed.

Lemma fixed_merge_memory s k n address provenance choice m :
  fst (fixed_merge_state s k n address provenance choice m) = m.
Proof. unfold fixed_merge_state. rewrite !memory_set_local. reflexivity. Qed.

Ltac fixed_locals :=
  repeat first [rewrite lookup_local_other by
    (intro E; subst; match goal with H : ~ In _ fixed_modified |- _ =>
      apply H; unfold fixed_modified; simpl; tauto end)
    | rewrite locals_with_memory].

Lemma fixed_compare_other s k da dp ta tp x y id : ~ In id fixed_modified ->
  Maps.lookup id (locals (fixed_compare_state s k da dp ta tp x y)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fixed_compare_state. fixed_locals. reflexivity. Qed.

Lemma fixed_assign_other s k address provenance m id : ~ In id fixed_modified ->
  Maps.lookup id (locals (fixed_assign_state s k address provenance m)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fixed_assign_state. fixed_locals. reflexivity. Qed.

Lemma fixed_merge_other s k n address provenance choice m id : ~ In id fixed_modified ->
  Maps.lookup id (locals (fixed_merge_state s k n address provenance choice m)) = Maps.lookup id (locals s).
Proof. intro Outside. unfold fixed_merge_state. fixed_locals. reflexivity. Qed.

Lemma fixed_merge_next s k n address provenance choice m :
  fixed_input (Name "if.end57") (fixed_merge_state s k n address provenance choice m) (k + 1).
Proof.
  right; split; [reflexivity|]. unfold fixed_merge_state.
  rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.
