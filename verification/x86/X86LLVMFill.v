(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ClightFillLoop
  ClightNormalization ModelArrays SolcModel.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks Fixed SearchBlocks Search SearchModel FillBlocks Fill.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Pass.
Context (layout : allocation_layout) (count : nat)
    (source desired : 'I_count -> nat) (bd bt bp bu : Values.block).
Hypothesis Bound : (count <= 1024)%coq_nat.
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (TP : bt <> bp) (TU : bt <> bu) (PU : bp <> bu).
Hypotheses (CD : (count <= block_words layout bd)%coq_nat)
    (CT : (count <= block_words layout bt)%coq_nat)
    (CP : (count <= block_words layout bp)%coq_nat)
    (CU : (count <= block_words layout bu)%coq_nat).
Hypotheses (SourceUInt : forall x, uint (Z.of_nat (source x)))
    (TargetUInt : forall x, uint (Z.of_nat (desired x))).

Local Notation arrays := (fill_arrays count source desired bd bt bp bu).
Local Notation registers := (fill_registers layout count bd bt bp bu).
Local Notation frame := (fill_frame bp bu).

Lemma llvm_fill_assignment_stores from varargs c s (index chosen : 'I_count) assignment reserved :
  cells_related layout c (fst s) -> arrays assignment reserved c -> registers s ->
  Maps.lookup (Name "indvars.iv311") (locals s) = Some (index_value (Z.of_nat (nat_of_ord index))) ->
  Maps.lookup (Name "v9.0.lcssa") (locals s) = Some (word_value (Int.repr (Z.of_nat (nat_of_ord chosen)))) ->
  exists c1 c' s',
    Mem.store Mint32 c bp (4 * Z.of_nat (nat_of_ord index))
      (Vint (Int.repr (Z.of_nat (nat_of_ord chosen)))) = Some c1 /\
    Mem.store Mint32 c1 bu (4 * Z.of_nat (nat_of_ord chosen)) (Vint Int.one) = Some c' /\
    cells_related layout c' (fst s') /\
    arrays (write_index assignment index chosen) (chosen |: reserved) c' /\
    runs (denote_block (proj1_sig fill_assign) from varargs) s s' (inl (Name "if.end103")) /\
    Maps.lookup (Name "indvars.iv311") (locals s') = Some (index_value (Z.of_nat (nat_of_ord index))) /\
    registers s' /\
    (forall id, ~ In id fill_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    frame c c'.
Proof.
  intros Related [AD AT AP AU] [N Count SearchCount Data Target Perm Used] Index Chosen.
  assert (K : (nat_of_ord index < count)%coq_nat) by exact (elimT ltP (ltn_ord index)).
  assert (J : (nat_of_ord chosen < count)%coq_nat) by exact (elimT ltP (ltn_ord chosen)).
  destruct (@related_store layout c (fst s) bp (nat_of_ord index)
    (Int.repr (Z.of_nat (nat_of_ord chosen))) Related ltac:(lia))
    as [c1 [m1 [StorePerm [WritePerm [Related1 _]]]]].
  destruct (@related_store layout c1 m1 bu (nat_of_ord chosen) Int.one Related1 ltac:(lia))
    as [c2 [m2 [StoreUsed [WriteUsed [Related2 _]]]]].
  pose (s2 := fill_assign_state s (Z.of_nat (nat_of_ord index)) (Z.of_nat (nat_of_ord chosen))
    (block_address layout bp) (block_provenance layout bp)
    (block_address layout bu) (block_provenance layout bu) m1 m2).
  assert (Other : forall id, ~ In id fill_modified ->
      Maps.lookup id (locals s2) = Maps.lookup id (locals s)).
  { intros id Outside. apply fill_assign_other, Outside. }
  assert (P1 : array_at c1 bp (words (fun x => nat_of_ord (write_index assignment index chosen x)))).
  { rewrite <- destination_words_update. rewrite <- words_update.
    eapply array_store_same; eassumption. }
  assert (U1 : array_at c1 bu (words (used_flags reserved))).
  { eapply array_store_disjoint; [exact AU|exact (not_eq_sym PU)|exact StorePerm]. }
  exists c1, c2, s2. split; [exact StorePerm|]. split; [exact StoreUsed|]. split; [unfold s2; rewrite -> fill_assign_memory; exact Related2|].
  split.
  - constructor.
    + eapply array_store_disjoint; [|exact DU|exact StoreUsed].
      eapply array_store_disjoint; [exact AD|exact DP|exact StorePerm].
    + eapply array_store_disjoint; [|exact TU|exact StoreUsed].
      eapply array_store_disjoint; [exact AT|exact TP|exact StorePerm].
    + eapply array_store_disjoint; [exact P1|exact PU|exact StoreUsed].
    + rewrite <- used_flags_update. rewrite <- words_update.
      eapply array_store_same; eassumption.
  - split.
    + apply fill_assign_runs; try assumption; lia.
    + split.
      * unfold s2. rewrite -> fill_assign_index. exact Index.
      * split.
        -- constructor; rewrite -> Other by (unfold fill_modified; simpl; intuition discriminate); assumption.
        -- split; [exact Other|]. intros other values NotPerm NotUsed A.
           eapply array_store_disjoint; [|exact NotUsed|exact StoreUsed].
           eapply array_store_disjoint; [exact A|exact NotPerm|exact StorePerm].
Qed.

End Pass.

Print Assumptions llvm_fill_assignment_stores.

Lemma raw_fill_step_nat count (source desired : 'I_count -> nat)
    index tail assignment reserved :
  raw_fill source desired (index :: tail) assignment reserved =
    if Nat.eqb (source index) (desired index) then
      raw_fill source desired tail assignment reserved
    else
      match first_free desired (source index) reserved (enum 'I_count) with
      | Some chosen => raw_fill source desired tail
          (write_index assignment index chosen) (chosen |: reserved)
      | None => None
      end.
Proof. cbn [raw_fill]. rewrite /fixed_values inE nat_eqb_mathcomp. reflexivity. Qed.

Print Assumptions raw_fill_step_nat.
