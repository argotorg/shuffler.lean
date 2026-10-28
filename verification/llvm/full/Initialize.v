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

Definition initialize_input from s k : Prop :=
  (from = Name "if.end10.preheader" /\ k = 0) \/
  (from = Name "if.end10" /\
   Maps.lookup (Name "indvars.iv.next") (locals s) = Some (index_value k)).

Definition initialize_state s k n address provenance m :=
  let s1 := set_local s (Name "indvars.iv") (index_value k) in
  let s2 := set_local s1 (Name "arrayidx11")
    (pointer_value (address + 4 * k) provenance) in
  let s3 := with_memory s2 m in
  let s4 := set_local s3 (Name "indvars.iv.next") (index_value (k + 1)) in
  set_local s4 (Name "exitcond.not") (boolean_value (k + 1 =? n)).

Lemma initialize_phi from s k : initialize_input from s k ->
  runs (denote_phis from (blk_phis (proj1_sig FullCFG.initialize_used))) s
    (set_local s (Name "indvars.iv") (index_value k)) tt.
Proof.
  intros [[-> ->] | [-> Next]]; eapply runs_phis_single.
  - apply assoc_hd.
  - apply runs_expression_integer. resolve_types. reflexivity.
  - eapply eq_trans; [apply assoc_tl; discriminate|apply assoc_hd].
  - entry_lookup.
Qed.

Lemma initialize_step from varargs (s : FusedS) k n address provenance
    (m : Impl.State) :
  0 <= k < n -> n <= 1024 ->
  initialize_input from s k ->
  Maps.lookup (Name "wide.trip.count") (locals s) = Some (index_value n) ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.write_dvalue (address + 4 * k, provenance) (DTYPE_I 32)
    (word_value Int.zero)) (fst s) = Ret (m, tt) ->
  runs (denote_block (proj1_sig FullCFG.initialize_used) from varargs) s
    (initialize_state s k n address provenance m)
    (inl (if k + 1 =? n then Name "if.end17.preheader" else Name "if.end10")).
Proof.
  intros K N Input Count Base Store.
  eapply runs_block.
  - apply initialize_phi, Input.
  - eapply runs_code_cons.
    + apply runs_assign with (value := pointer_value (address + 4 * k) provenance).
      eapply runs_expression_gep.
      * entry_lookup.
      * entry_lookup.
      * resolve_types. apply index_gep. lia.
    + eapply runs_code_cons.
      * eapply runs_instruction_store.
        -- apply runs_expression_integer. resolve_types. reflexivity.
        -- entry_lookup.
        -- resolve_types. rewrite !memory_set_local. exact Store.
      * eapply runs_code_cons.
        -- apply runs_assign with (value := index_value (k + 1)).
           eapply runs_expression_ibinop with (vb := index_value 1).
           ++ entry_lookup.
           ++ apply runs_expression_integer. resolve_types. reflexivity.
           ++ apply index_add. lia.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := boolean_value (k + 1 =? n)).
              eapply runs_expression_icmp.
              ** entry_lookup.
              ** entry_lookup.
              ** apply index_eq; lia.
           ++ apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 7,
      TERM_Br ((typ_to_dtyp [] (TYPE_I 1)), EXP_Ident (ID_Local (Name "exitcond.not")))
        (Name "if.end17.preheader") (Name "if.end10"), []))
      (initialize_state s k n address provenance m)
      (initialize_state s k n address provenance m)
      (inl (if k + 1 =? n then Name "if.end17.preheader" else Name "if.end10"))).
    resolve_types. apply runs_branch. unfold initialize_state. entry_lookup.
Qed.

Lemma initialize_state_memory s k n address provenance m :
  fst (initialize_state s k n address provenance m) = m.
Proof. unfold initialize_state; rewrite !memory_set_local; reflexivity. Qed.

Definition initialize_unmodified id : Prop :=
  id <> Name "indvars.iv" /\ id <> Name "arrayidx11" /\
  id <> Name "indvars.iv.next" /\ id <> Name "exitcond.not".

Lemma initialize_state_other s k n address provenance m id :
  initialize_unmodified id ->
  Maps.lookup id (locals (initialize_state s k n address provenance m)) =
    Maps.lookup id (locals s).
Proof.
  intros [A [B [C D]]]. unfold initialize_state.
  rewrite !lookup_local_other by assumption.
  rewrite locals_with_memory.
  rewrite !lookup_local_other by assumption. reflexivity.
Qed.

Lemma initialize_state_next s k n address provenance m :
  initialize_input (Name "if.end10")
    (initialize_state s k n address provenance m) (k + 1).
Proof.
  right; split; [reflexivity|]. unfold initialize_state.
  rewrite lookup_local_other by discriminate. apply lookup_local_same.
Qed.

(* This relation records the CompCert stores matched by the loop. *)
Inductive zero_stores (b : Values.block) : nat -> nat -> Mem.mem -> Mem.mem -> Prop :=
| zero_stores_done start c : zero_stores b start 0 c c
| zero_stores_next start count c middle final :
    Mem.store Mint32 c b (4 * Z.of_nat start) (Vint Int.zero) = Some middle ->
    zero_stores b (S start) count middle final ->
    zero_stores b start (S count) c final.

Lemma zero_stores_frame b start count c final :
  zero_stores b start count c final ->
  forall other k, other <> b \/ (k < start \/ start + count <= k)%nat ->
  Mem.load Mint32 final other (4 * Z.of_nat k) =
    Mem.load Mint32 c other (4 * Z.of_nat k).
Proof.
  intro Stores. induction Stores; intros other k Outside; [reflexivity|].
  rewrite IHStores by (destruct Outside as [B|K]; [now left|right; lia]).
  eapply Mem.load_store_other; [eassumption|].
  destruct Outside as [B|K]; [left; congruence|right].
  change (4 * Z.of_nat k + 4 <= 4 * Z.of_nat start \/
    4 * Z.of_nat start + 4 <= 4 * Z.of_nat k). lia.
Qed.

Lemma zero_stores_values b start count c final :
  zero_stores b start count c final ->
  forall k, (start <= k < start + count)%nat ->
  Mem.load Mint32 final b (4 * Z.of_nat k) = Some (Vint Int.zero).
Proof.
  intro Stores. induction Stores; intros k K; [lia|].
  destruct (Nat.eq_dec k start) as [->|Different].
  - rewrite (@zero_stores_frame _ _ _ _ _ Stores b start) by (right; lia).
    exact (Mem.load_store_same Mint32 c b (4 * Z.of_nat start)
      (Vint Int.zero) middle H).
  - apply IHStores. lia.
Qed.

Theorem initialize_loop layout b size varargs : (size <= 1024)%nat ->
  (size <= block_words layout b)%nat ->
  forall remaining start from c s,
  (0 < remaining)%nat -> (start + remaining = size)%nat ->
  cells_related layout c (fst s) ->
  initialize_input from s (Z.of_nat start) ->
  Maps.lookup (Name "wide.trip.count") (locals s) = Some (index_value (Z.of_nat size)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout b) (block_provenance layout b)) ->
  exists c' s',
    zero_stores b start remaining c c' /\
    cells_related layout c' (fst s') /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end10") s
      (Name "if.end10") (Name "if.end17.preheader") s' /\
    (forall id, initialize_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)).
Proof.
  intros Size Capacity remaining. induction remaining as [|remaining IH];
    intros start from c s Positive Sum Relation Input Count Base; [lia|].
  destruct (@related_store layout c (fst s) b start Int.zero Relation ltac:(lia))
    as [c1 [m1 [Store [Write [Relation1 _]]]]].
  pose (s1 := initialize_state s (Z.of_nat start) (Z.of_nat size)
    (block_address layout b) (block_provenance layout b) m1).
  assert (Relation1' : cells_related layout c1 (fst s1)).
  { unfold s1. rewrite initialize_state_memory. exact Relation1. }
  assert (Step : runs (denote_block (proj1_sig FullCFG.initialize_used) from varargs)
      s s1 (inl (if Z.of_nat start + 1 =? Z.of_nat size
        then Name "if.end17.preheader" else Name "if.end10"))).
  { apply initialize_step; try assumption; try lia. }
  assert (Other : forall id, initialize_unmodified id ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Different. apply initialize_state_other, Different. }
  destruct remaining as [|remaining].
  - assert (Last : (Z.of_nat start + 1 =? Z.of_nat size) = true)
      by (apply Z.eqb_eq; lia).
    rewrite Last in Step. exists c1, s1. split.
    + eapply zero_stores_next; [exact Store|constructor].
    + split; [exact Relation1'|]. split; [|exact Other].
      eapply steps_next; [exact (proj2_sig FullCFG.initialize_used)|exact Step|constructor].
  - assert (More : (Z.of_nat start + 1 =? Z.of_nat size) = false)
      by (apply Z.eqb_neq; lia).
    rewrite More in Step.
    assert (Next : initialize_input (Name "if.end10") s1 (Z.of_nat (S start))).
    { rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat start)) with
        (Z.of_nat start + 1) by lia. apply initialize_state_next. }
    assert (Count1 : Maps.lookup (Name "wide.trip.count") (locals s1) =
        Some (index_value (Z.of_nat size))).
    { rewrite Other by (repeat split; discriminate). exact Count. }
    assert (Base1 : Maps.lookup (Name "v5") (locals s1) = Some
        (pointer_value (block_address layout b) (block_provenance layout b))).
    { rewrite Other by (repeat split; discriminate). exact Base. }
    destruct (IH (S start) (Name "if.end10") c1 s1 ltac:(lia) ltac:(lia)
      Relation1' Next Count1 Base1) as [c' [s' [Stores [Related [Steps Locals]]]]].
    exists c', s'. split.
    + eapply zero_stores_next; eassumption.
    + split; [exact Related|]. split.
      * eapply steps_next; [exact (proj2_sig FullCFG.initialize_used)|exact Step|exact Steps].
      * intros id Different. rewrite Locals by exact Different. apply Other, Different.
Qed.

Corollary initialize_array layout b size varargs c s :
  (0 < size <= 1024)%nat -> (size <= block_words layout b)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "wide.trip.count") (locals s) = Some (index_value (Z.of_nat size)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout b) (block_provenance layout b)) ->
  exists c' s',
    cells_related layout c' (fst s') /\
    (forall k, (k < size)%nat ->
      Mem.load Mint32 c' b (4 * Z.of_nat k) = Some (Vint Int.zero)) /\
    block_steps (blks FullCFG.body) varargs (Name "if.end10.preheader")
      (Name "if.end10") s (Name "if.end10") (Name "if.end17.preheader") s' /\
    (forall id, initialize_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other k, other <> b \/ (size <= k)%nat ->
      Mem.load Mint32 c' other (4 * Z.of_nat k) =
        Mem.load Mint32 c other (4 * Z.of_nat k)).
Proof.
  intros [Positive Size] Capacity Relation Count Base.
  destruct (@initialize_loop layout b size varargs Size Capacity size 0
    (Name "if.end10.preheader") c s Positive eq_refl Relation
    (or_introl (conj eq_refl eq_refl)) Count Base)
    as [c' [s' [Stores [Related [Steps Locals]]]]].
  exists c', s'. split; [exact Related|]. split.
  - intros k Bound. eapply zero_stores_values; [exact Stores|lia].
  - split; [exact Steps|]. split; [exact Locals|].
    intros other k Outside. eapply zero_stores_frame; [exact Stores|].
    destruct Outside as [Different|Bound]; [now left|right; lia].
Qed.
