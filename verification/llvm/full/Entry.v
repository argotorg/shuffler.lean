(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Syntax TypToDtyp Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG.
Open Scope string_scope.
Open Scope Z_scope.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition pointer_value address provenance : dvalue :=
  DVALUE_Base (DVALUE_Pointer (address, provenance)).

Definition size_choice (n : Int.int) :=
  @LLVMInt.ltu 32 (LLVMInt.repr 1024) (LLVMInt.repr (Int.unsigned n)).

Lemma size_comparison n :
  eval_icmp false Ugt (word_value n) (word_value (Int.repr 1024)) =
    raise_ret (boolean_value (size_choice n)).
Proof.
  change (raise_ret (DVALUE_Base
    (if size_choice n then DVALUE_I 1 LLVMInt.one else DVALUE_I 1 LLVMInt.zero)) =
    raise_ret (boolean_value (size_choice n))).
  destruct (size_choice n); reflexivity.
Qed.

Lemma size_choice_unsigned n : size_choice n = (1024 <? Int.unsigned n).
Proof.
  unfold size_choice, LLVMInt.ltu.
  rewrite (LLVMInt.unsigned_repr (Int.unsigned n)) by
    (pose proof (Int.unsigned_range n) as Range;
     change (0 <= Int.unsigned n < 4294967296) in Range;
     change (0 <= Int.unsigned n <= 4294967295); lia).
  change ((if Vellvm.Numeric.Rocqlib.zlt 1024 (Int.unsigned n) then true else false) =
    (1024 <? Int.unsigned n)).
  unfold Vellvm.Numeric.Rocqlib.zlt.
  destruct (Z_lt_dec 1024 (Int.unsigned n));
    destruct (Z.ltb_spec 1024 (Int.unsigned n)); try lia; reflexivity.
Qed.

Definition entry_state s n address provenance m1 m2 m3 :=
  let s1 := with_memory s m1 in
  let s2 := set_local s1 (Name "arrayidx1") (pointer_value (address + 4) provenance) in
  let s3 := with_memory s2 m2 in
  let s4 := set_local s3 (Name "arrayidx2") (pointer_value (address + 8) provenance) in
  let s5 := with_memory s4 m3 in
  set_local s5 (Name "cmp") (boolean_value (size_choice n)).

Ltac entry_lookup :=
  lazymatch goal with
  | |- @runs _ (@denote_exp' _ _ ?operand) _ _ _ =>
      let syntax := eval hnf in operand in
      lazymatch syntax with
      | EXP_Ident ?id =>
          let id_syntax := eval hnf in id in
          lazymatch id_syntax with ID_Local _ => idtac end
      end
  end;
  apply runs_expression_local;
  repeat first [rewrite lookup_local_same
    | rewrite lookup_local_other by discriminate
    | rewrite locals_with_memory];
  first [eassumption | reflexivity].

Ltac resolve_types := repeat rewrite typ_to_dtyp_equation.

(* The three memory premises are atomic stores. CellRelation.related_store
   supplies them from the Clight memory relation in the theorem below. *)
Theorem entry_runs from varargs (s : FusedS) (n : Int.int)
    (address : Z) (provenance : prov) (m1 m2 m3 : Impl.State) :
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  Maps.lookup (Name "v7") (locals s) = Some (pointer_value address provenance) ->
  run_memory (Impl.write_dvalue (address, provenance) (DTYPE_I 32)
    (word_value Int.zero)) (fst s) = Ret (m1, tt) ->
  run_memory (Impl.write_dvalue (address + 4, provenance) (DTYPE_I 32)
    (word_value Int.zero)) m1 = Ret (m2, tt) ->
  run_memory (Impl.write_dvalue (address + 8, provenance) (DTYPE_I 32)
    (word_value Int.zero)) m2 = Ret (m3, tt) ->
  runs (denote_block (proj1_sig FullCFG.entry) from varargs) s
    (entry_state s n address provenance m1 m2 m3)
    (inl (Name (if size_choice n then "cleanup" else "if.end"))).
Proof.
  intros N Output W0 W1 W2.
  unfold entry_state.
  eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + eapply runs_instruction_store.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * entry_lookup.
      * resolve_types. exact W0.
    + eapply runs_code_cons.
      * apply runs_assign with (value := pointer_value (address + 4) provenance).
        eapply runs_expression_gep.
        -- entry_lookup.
        -- apply runs_expression_integer. resolve_types. reflexivity.
        -- resolve_types. reflexivity.
      * eapply runs_code_cons.
        -- eapply runs_instruction_store.
           ++ apply runs_expression_integer. resolve_types. reflexivity.
           ++ entry_lookup.
           ++ resolve_types. rewrite memory_set_local. exact W1.
        -- eapply runs_code_cons.
           ++ apply runs_assign with (value := pointer_value (address + 8) provenance).
              eapply runs_expression_gep.
              ** entry_lookup.
              ** apply runs_expression_integer. resolve_types. reflexivity.
              ** resolve_types. reflexivity.
           ++ eapply runs_code_cons.
              ** eapply runs_instruction_store.
                 --- apply runs_expression_integer. resolve_types. reflexivity.
                 --- entry_lookup.
                 --- resolve_types. rewrite memory_set_local. exact W2.
              ** eapply runs_code_cons.
                 --- apply runs_assign with (value := boolean_value (size_choice n)).
                     eapply runs_expression_icmp with (vb := word_value (Int.repr 1024)).
                     +++ entry_lookup.
                     +++ apply runs_expression_integer. resolve_types. reflexivity.
                     +++ apply size_comparison.
                 --- apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 3,
      TERM_Br ((typ_to_dtyp nil (TYPE_I 1)), EXP_Ident (ID_Local (Name "cmp")))
        (Name "cleanup") (Name "if.end"), nil))
      (entry_state s n address provenance m1 m2 m3)
      (entry_state s n address provenance m1 m2 m3)
      (inl (Name (if size_choice n then "cleanup" else "if.end")))).
    replace (Name (if size_choice n then "cleanup" else "if.end")) with
      (if size_choice n then Name "cleanup" else Name "if.end")
      by (destruct (size_choice n); reflexivity).
    resolve_types. apply runs_branch. unfold entry_state. entry_lookup.
Qed.

Lemma entry_state_memory s n address provenance m1 m2 m3 :
  fst (entry_state s n address provenance m1 m2 m3) = m3.
Proof. unfold entry_state; rewrite memory_set_local; reflexivity. Qed.

Definition entry_unmodified id : Prop :=
  id <> Name "arrayidx1" /\ id <> Name "arrayidx2" /\ id <> Name "cmp".

Lemma entry_state_other s n address provenance m1 m2 m3 id :
  entry_unmodified id ->
  Maps.lookup id (locals (entry_state s n address provenance m1 m2 m3)) =
    Maps.lookup id (locals s).
Proof.
  intros [A [B C]]. unfold entry_state.
  repeat first [rewrite lookup_local_other by assumption | rewrite locals_with_memory].
  reflexivity.
Qed.

Definition output_stores c b final : Prop :=
  exists c1 c2,
    Mem.store Mint32 c b 0 (Vint Int.zero) = Some c1 /\
    Mem.store Mint32 c1 b 4 (Vint Int.zero) = Some c2 /\
    Mem.store Mint32 c2 b 8 (Vint Int.zero) = Some final.

Record output_registers (layout : allocation_layout) (b : Values.block) (s : FusedS) : Prop := {
  output_position_local : Maps.lookup (Name "arrayidx1") (locals s) =
    Some (pointer_value (block_address layout b + 4) (block_provenance layout b));
  output_depth_local : Maps.lookup (Name "arrayidx2") (locals s) =
    Some (pointer_value (block_address layout b + 8) (block_provenance layout b))
}.

Lemma entry_output_registers layout b s n m1 m2 m3 :
  output_registers layout b (entry_state s n (block_address layout b)
    (block_provenance layout b) m1 m2 m3).
Proof.
  constructor; unfold entry_state;
    repeat first [rewrite lookup_local_other by discriminate | rewrite locals_with_memory];
    apply lookup_local_same.
Qed.

Theorem entry_related layout c s n b from varargs :
  cells_related layout c (fst s) ->
  (3 <= block_words layout b)%nat ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout b) (block_provenance layout b)) ->
  exists c' s',
    output_stores c b c' /\ cells_related layout c' (fst s') /\
    runs (denote_block (proj1_sig FullCFG.entry) from varargs) s s'
      (inl (Name (if 1024 <? Int.unsigned n then "cleanup" else "if.end"))) /\
    (forall id, entry_unmodified id ->
      Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    output_registers layout b s'.
Proof.
  intros Relation Size N Output.
  destruct (@related_store layout c (fst s) b 0 Int.zero Relation ltac:(lia))
    as [c1 [m1 [C0 [W0 [R1 _]]]]].
  destruct (@related_store layout c1 m1 b 1 Int.zero R1 ltac:(lia))
    as [c2 [m2 [C1 [W1 [R2 _]]]]].
  destruct (@related_store layout c2 m2 b 2 Int.zero R2 ltac:(lia))
    as [c3 [m3 [C2 [W2 [R3 _]]]]].
  exists c3, (entry_state s n (block_address layout b)
    (block_provenance layout b) m1 m2 m3).
  split.
  - exists c1, c2. repeat split; assumption.
  - split; [rewrite entry_state_memory; exact R3|].
    split; [|split; [intros; apply entry_state_other; assumption|apply entry_output_registers]].
    rewrite <- size_choice_unsigned.
    eapply entry_runs; [exact N|exact Output| |exact W1|exact W2].
    replace (cell_address layout b 0) with (block_address layout b) in W0
      by (unfold cell_address; lia).
    exact W0.
Qed.
