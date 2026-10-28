(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightExchangeSuccess ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks Fixed Choose ExchangeBlocks ExchangePermutation ExchangeData MainPrefix MainInvariant ExchangeSuccess.
From X86 Require Import X86LLVMExchangePermutation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem llvm_exchange_data_array_stores layout bd trace output xs depths c s k top x y from varargs :
  bd <> trace -> bd <> output -> trace <> output ->
  (List.length xs <= 1024)%coq_nat ->
  (List.length xs <= block_words layout bd)%coq_nat ->
  (2 * List.length xs <= block_words layout trace)%coq_nat ->
  (3 <= block_words layout output)%coq_nat ->
  (List.length depths < 2 * List.length xs)%coq_nat ->
  List.nth_error xs k = Some x -> List.nth_error xs top = Some y ->
  cells_related layout c (fst s) -> array_at c bd xs -> array_at c trace depths ->
  array_at c output [Z.of_nat (List.length depths); 0; 0] ->
  Maps.lookup (Name "arrayidx135") (locals s) = Some
    (pointer_value (block_address layout bd + 4 * Z.of_nat k) (block_provenance layout bd)) ->
  Maps.lookup (Name "arrayidx137") (locals s) = Some
    (pointer_value (block_address layout bd + 4 * Z.of_nat top) (block_provenance layout bd)) ->
  Maps.lookup (Name "v6") (locals s) = Some
    (pointer_value (block_address layout trace) (block_provenance layout trace)) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  Maps.lookup (Anon 18) (locals s) = Some (word_value (Int.repr x)) ->
  Maps.lookup (Anon 19) (locals s) = Some (word_value (Int.repr y)) ->
  Maps.lookup (Name "sub140") (locals s) = Some
    (word_value (Int.repr (Z.of_nat top - Z.of_nat k))) ->
  exists c1 c2 c3 c' s',
    Mem.load Mint32 c output 0 = Some (Vint (Int.repr (Z.of_nat (List.length depths)))) /\
    Mem.store Mint32 c bd (4 * Z.of_nat k) (Vint (Int.repr y)) = Some c1 /\
    Mem.store Mint32 c1 bd (4 * Z.of_nat top) (Vint (Int.repr x)) = Some c2 /\
    Mem.store Mint32 c2 trace (4 * Z.of_nat (List.length depths))
      (Vint (Int.repr (Z.of_nat top - Z.of_nat k))) = Some c3 /\
    Mem.store Mint32 c3 output 0 (Vint (Int.repr (Z.of_nat (List.length depths) + 1))) = Some c' /\
    cells_related layout c' (fst s') /\
    array_at c' bd (replace_nth top x (replace_nth k y xs)) /\
    array_at c' trace (depths ++ [Z.of_nat top - Z.of_nat k]) /\
    array_at c' output [Z.of_nat (List.length depths) + 1; 0; 0] /\
    runs (denote_block (proj1_sig exchange_data) from varargs) s s' (inl (Name "if.end169")) /\
    (forall id, ~ In id exchange_data_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bd -> other <> trace -> other <> output ->
      array_at c other values -> array_at c' other values).
Proof.
  intros DT DO TO Size CD CT CO Capacity K T Related AD AT AO Selected Top Trace Output X Y Depth.
  assert (KB : (k < List.length xs)%coq_nat) by (apply List.nth_error_Some; rewrite K; discriminate).
  assert (TB : (top < List.length xs)%coq_nat) by (apply List.nth_error_Some; rewrite T; discriminate).
  destruct (@related_store layout c (fst s) bd k (Int.repr y) Related ltac:(lia))
    as [c1 [m1 [StoreSelected [WriteSelected [Related1 _]]]]].
  destruct (@related_store layout c1 m1 bd top (Int.repr x) Related1 ltac:(lia))
    as [c2 [m2 [StoreTop [WriteTop [Related2 _]]]]].
  assert (AD2 : array_at c2 bd (replace_nth top x (replace_nth k y xs))).
  { eapply array_store_same; [|exact StoreTop]. eapply array_store_same; eassumption. }
  assert (AT2 : array_at c2 trace depths).
  { eapply array_store_disjoint; [|exact (not_eq_sym DT)|exact StoreTop].
    eapply array_store_disjoint; [exact AT|exact (not_eq_sym DT)|exact StoreSelected]. }
  assert (AO2 : array_at c2 output [Z.of_nat (List.length depths); 0; 0]).
  { eapply array_store_disjoint; [|exact (not_eq_sym DO)|exact StoreTop].
    eapply array_store_disjoint; [exact AO|exact (not_eq_sym DO)|exact StoreSelected]. }
  assert (ReadCount1 : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (block_address layout output, block_provenance layout output)) m2 =
      Ret (m2, word_value (Int.repr (Z.of_nat (List.length depths))))).
  { replace (block_address layout output) with (CellRelation.cell_address layout output 0) by (unfold CellRelation.cell_address; ring).
    eapply related_load; [exact Related2|lia|]. exact (proj1 (AO2 0%nat _ Logic.eq_refl)). }
  destruct (@related_store layout c2 m2 trace (List.length depths)
    (Int.repr (Z.of_nat top - Z.of_nat k)) Related2 ltac:(lia))
    as [c3 [m3 [StoreTrace [WriteTrace [Related3 _]]]]].
  assert (AT3 : array_at c3 trace (depths ++ [Z.of_nat top - Z.of_nat k])).
  { eapply array_append_store; eassumption. }
  assert (AO3 : array_at c3 output [Z.of_nat (List.length depths); 0; 0]).
  { eapply array_store_disjoint; [exact AO2|exact (not_eq_sym TO)|exact StoreTrace]. }
  assert (ReadCount2 : run_memory (Impl.read_dvalue (DTYPE_I 32)
      (block_address layout output, block_provenance layout output)) m3 =
      Ret (m3, word_value (Int.repr (Z.of_nat (List.length depths))))).
  { replace (block_address layout output) with (CellRelation.cell_address layout output 0) by (unfold CellRelation.cell_address; ring).
    eapply related_load; [exact Related3|lia|]. exact (proj1 (AO3 0%nat _ Logic.eq_refl)). }
  destruct (@related_store layout c3 m3 output 0
    (Int.repr (Z.of_nat (List.length depths) + 1)) Related3 ltac:(lia))
    as [c4 [m4 [StoreCount [WriteCount [Related4 _]]]]].
  pose (s4 := exchange_data_state s (Z.of_nat (List.length depths))
    (block_address layout trace) (block_provenance layout trace) m1 m2 m3 m4).
  exists c1, c2, c3, c4, s4.
  split; [exact (proj1 (AO 0%nat _ Logic.eq_refl))|].
  split; [exact StoreSelected|]. split; [exact StoreTop|].
  split; [exact StoreTrace|]. split; [exact StoreCount|].
  split; [unfold s4; rewrite exchange_data_memory; exact Related4|].
  split.
  - eapply array_store_disjoint; [|exact DO|exact StoreCount].
    eapply array_store_disjoint; [exact AD2|exact DT|exact StoreTrace].
  - split.
    + eapply array_store_disjoint; [exact AT3|exact TO|exact StoreCount].
    + split.
      * exact (array_store_same _ _ _ _ _ _ AO3 StoreCount).
      * split.
        -- unfold CellRelation.cell_address in WriteCount. cbn [Z.of_nat Z.mul] in WriteCount.
           rewrite Z.add_0_r in WriteCount.
           apply exchange_data_runs with
             (selected := block_address layout bd + 4 * Z.of_nat k)
             (top := block_address layout bd + 4 * Z.of_nat top)
             (dp := block_provenance layout bd)
             (oa := block_address layout output) (op := block_provenance layout output)
             (x := Int.repr x) (y := Int.repr y)
             (depth := Z.of_nat top - Z.of_nat k); try assumption.
           unfold muln in Capacity. lia.
        -- split.
           ++ intros id Outside. apply exchange_data_other, Outside.
           ++ intros other values ND NT NO Other.
              eapply array_store_disjoint; [|exact NO|exact StoreCount].
              eapply array_store_disjoint; [|exact NT|exact StoreTrace].
              eapply array_store_disjoint; [|exact ND|exact StoreTop].
              eapply array_store_disjoint; [exact Other|exact ND|exact StoreSelected].
Qed.

Section Success.
Context (layout : allocation_layout) (d : nat) (bd bp trace output : Values.block).
Hypotheses (DP : bd <> bp) (DT : bd <> trace) (DO : bd <> output)
    (PT : bp <> trace) (PO : bp <> output) (TO : trace <> output).
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (2 * S d <= block_words layout trace)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Theorem llvm_successful_exchange_stores (source : 'I_(S d) -> nat) (p : 'S_(S d))
    (position : 'I_(S d)) depths c s from varargs :
  (forall x, uint (Z.of_nat (source x))) ->
  (nat_of_ord position < d)%coq_nat ->
  source position <> source ord_max ->
  (d <= nat_of_ord position + 16)%coq_nat ->
  (List.length depths < 2 * S d)%coq_nat ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  choose_binding from s (Some (nat_of_ord position)) ->
  exists c1 c2 c3 c4 c5 c' s',
    Mem.load Mint32 c bd (4 * Z.of_nat (nat_of_ord position)) =
      Some (Vint (Int.repr (Z.of_nat (source position)))) /\
    Mem.load Mint32 c bd (4 * Z.of_nat d) =
      Some (Vint (Int.repr (Z.of_nat (source ord_max)))) /\
    Mem.load Mint32 c output 0 = Some (Vint (Int.repr (Z.of_nat (List.length depths)))) /\
    Mem.store Mint32 c bd (4 * Z.of_nat (nat_of_ord position))
      (Vint (Int.repr (Z.of_nat (source ord_max)))) = Some c1 /\
    Mem.store Mint32 c1 bd (4 * Z.of_nat d)
      (Vint (Int.repr (Z.of_nat (source position)))) = Some c2 /\
    Mem.store Mint32 c2 trace (4 * Z.of_nat (List.length depths))
      (Vint (Int.repr (Z.of_nat d - Z.of_nat (nat_of_ord position)))) = Some c3 /\
    Mem.store Mint32 c3 output 0 (Vint (Int.repr (Z.of_nat (List.length depths) + 1))) = Some c4 /\
    Mem.load Mint32 c4 bp (4 * Z.of_nat (nat_of_ord position)) =
      Some (Vint (Int.repr (Z.of_nat (nat_of_ord (p position))))) /\
    Mem.load Mint32 c4 bp (4 * Z.of_nat d) =
      Some (Vint (Int.repr (Z.of_nat (nat_of_ord (p ord_max))))) /\
    Mem.store Mint32 c4 bp (4 * Z.of_nat (nat_of_ord position))
      (Vint (Int.repr (Z.of_nat (nat_of_ord (p ord_max))))) = Some c5 /\
    Mem.store Mint32 c5 bp (4 * Z.of_nat d)
      (Vint (Int.repr (Z.of_nat (nat_of_ord (p position))))) = Some c' /\
    cells_related layout c' (fst s') /\
    @ClightMain.loop_arrays d bd bp trace output c'
      (Legacy.Permute.swap_stack source position)
      (Legacy.Permute.exchange p ord_max position)
      (depths ++ [Legacy.Permute.depth position]) /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.end169") (Name "while.cond106") s' /\
    (forall id, success_unmodified id -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bd -> other <> bp -> other <> trace -> other <> output ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Values Position Different Near Capacity Related Arrays Registers Binding.
  destruct Arrays as [AD AP AT AO Writable].
  pose (s1 := exchange_compare_state s (Z.of_nat (nat_of_ord position))
    (block_address layout bd) (block_provenance layout bd)
    (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source ord_max)))).
  assert (Unequal : word_equal (Int.repr (Z.of_nat (source position)))
      (Int.repr (Z.of_nat (source ord_max))) = false).
  { rewrite -> natural_word_equal by auto. apply Nat.eqb_neq, Different. }
  assert (Compare : runs (denote_block (proj1_sig exchange_compare) from varargs)
      s s1 (inl (Name "if.then139"))).
  { pose proof (@exchange_compare_runs from varargs s (nat_of_ord position)
      (block_address layout bd) (block_provenance layout bd)
      (block_address layout bd + 4 * Z.of_nat d)
      (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source ord_max)))
      ltac:(lia) Binding (main_data _ _ _ _ _ _ _ Registers)
      (main_data_top _ _ _ _ _ _ _ Registers)) as Run.
    rewrite Unequal in Run. apply Run.
    - eapply related_load; [exact Related|lia|].
      exact (proj1 (AD _ _ (words_nth_error source position))).
    - eapply related_load; [exact Related|lia|].
      exact (proj1 (AD _ _ (words_nth_error source ord_max))). }
  assert (Memory1 : fst s1 = fst s) by apply exchange_compare_memory.
  assert (Registers1 : main_registers layout d bd bp trace output s1).
  { eapply exchange_main_registers; [exact Registers|]. intros id Outside.
    apply exchange_compare_other, Outside. }
  destruct (exchange_compare_bindings s (Z.of_nat (nat_of_ord position))
    (block_address layout bd) (block_provenance layout bd)
    (Int.repr (Z.of_nat (source position))) (Int.repr (Z.of_nat (source ord_max))))
    as [Pos1 [Index1 [Selected1 [X1 Y1]]]].
  pose (s2 := exchange_depth_state s1 (Z.of_nat d) (Z.of_nat (nat_of_ord position))).
  assert (Within : (16 <? Z.of_nat d - Z.of_nat (nat_of_ord position)) = false).
  { apply Z.ltb_ge. unfold addn in Near. lia. }
  assert (Depth : runs (denote_block (proj1_sig exchange_depth) (Name "if.end133") varargs)
      s1 s2 (inl (Name "if.end147"))).
  { pose proof (@exchange_depth_runs (Name "if.end133") varargs s1 (Z.of_nat d)
      (Z.of_nat (nat_of_ord position)) ltac:(lia) ltac:(lia)
      (main_top _ _ _ _ _ _ _ Registers1) Pos1) as Run.
    rewrite Within in Run. exact Run. }
  assert (Memory2 : fst s2 = fst s) by (unfold s2; rewrite exchange_depth_memory; exact Memory1).
  assert (Related2 : cells_related layout c (fst s2)) by (rewrite Memory2; exact Related).
  assert (Registers2 : main_registers layout d bd bp trace output s2).
  { eapply exchange_main_registers; [exact Registers1|]. intros id Outside.
    apply exchange_depth_other, Outside. }
  pose (s3 := exchange_capacity_state s2 (Int.repr (Z.of_nat (List.length depths)))
    (Int.repr (2 * Z.of_nat (S d)))).
  assert (Space : (Int.unsigned (Int.repr (Z.of_nat (List.length depths))) <?
      Int.unsigned (Int.repr (2 * Z.of_nat (S d)))) = true).
  { rewrite !trace_unsigned; try (unfold muln in Capacity; lia).
    apply Z.ltb_lt. unfold muln in Capacity. lia. }
  assert (Check : runs (denote_block (proj1_sig exchange_capacity) (Name "if.then139") varargs)
      s2 s3 (inl (Name "if.end153"))).
  { pose proof (@exchange_capacity_runs (Name "if.then139") varargs s2
      (block_address layout output) (block_provenance layout output)
      (Int.repr (Z.of_nat (List.length depths))) (Int.repr (2 * Z.of_nat (S d)))
      (main_output _ _ _ _ _ _ _ Registers2) (main_trace_capacity _ _ _ _ _ _ _ Registers2)) as Run.
    rewrite Space in Run. apply Run.
    replace (block_address layout output) with (CellRelation.cell_address layout output 0)
      by (unfold CellRelation.cell_address; ring).
    eapply related_load; [exact Related2|lia|]. exact (proj1 (AO 0%nat _ Logic.eq_refl)). }
  assert (Memory3 : fst s3 = fst s) by (unfold s3; rewrite exchange_capacity_memory; exact Memory2).
  assert (Related3 : cells_related layout c (fst s3)) by (rewrite Memory3; exact Related).
  assert (Registers3 : main_registers layout d bd bp trace output s3).
  { eapply exchange_main_registers; [exact Registers2|]. intros id Outside.
    apply exchange_capacity_other, Outside. }
  assert (Selected3 : Maps.lookup (Name "arrayidx135") (locals s3) = Some
      (pointer_value (block_address layout bd + 4 * Z.of_nat (nat_of_ord position))
        (block_provenance layout bd))).
  { unfold s3, exchange_capacity_state, s2, exchange_depth_state.
    rewrite -> !lookup_local_other by discriminate. exact Selected1. }
  assert (X3 : Maps.lookup (Anon 18) (locals s3) =
      Some (word_value (Int.repr (Z.of_nat (source position))))).
  { unfold s3, exchange_capacity_state, s2, exchange_depth_state.
    rewrite -> !lookup_local_other by discriminate. exact X1. }
  assert (Y3 : Maps.lookup (Anon 19) (locals s3) =
      Some (word_value (Int.repr (Z.of_nat (source ord_max))))).
  { unfold s3, exchange_capacity_state, s2, exchange_depth_state.
    rewrite -> !lookup_local_other by discriminate. exact Y1. }
  assert (Depth3 : Maps.lookup (Name "sub140") (locals s3) =
      Some (word_value (Int.repr (Z.of_nat d - Z.of_nat (nat_of_ord position))))).
  { unfold s3, exchange_capacity_state. rewrite -> !lookup_local_other by discriminate.
    apply exchange_depth_binding. }
  destruct (@llvm_exchange_data_array_stores layout bd trace output (words source) (trace_words depths)
    c s3 (nat_of_ord position) d (Z.of_nat (source position)) (Z.of_nat (source ord_max))
    (Name "if.end147") varargs DT DO TO
    ltac:(rewrite words_length; exact Size) ltac:(rewrite words_length; exact CD)
    ltac:(rewrite words_length; exact CT) CO
    ltac:(rewrite trace_words_length words_length; exact Capacity)
    (words_nth_error source position) (words_nth_error source ord_max)
    Related3 AD AT ltac:(rewrite trace_words_length; exact AO) Selected3
    (main_data_top _ _ _ _ _ _ _ Registers3) (main_trace _ _ _ _ _ _ _ Registers3)
    (main_output _ _ _ _ _ _ _ Registers3) X3 Y3 Depth3)
    as (c1 & c2 & c3 & c4 & s4 & CountLoad & StoreSelected & StoreTop & StoreTrace & StoreCount &
      Related4 & AD4 & AT4 & AO4 & Data & Other4 & Frame4).
  rewrite trace_words_length in CountLoad, StoreTrace, StoreCount.
  assert (Registers4 : main_registers layout d bd bp trace output s4).
  { eapply data_main_registers; eassumption. }
  assert (Index4 : Maps.lookup (Name "idxprom134") (locals s4) =
      Some (index_value (Z.of_nat (nat_of_ord position)))).
  { rewrite -> Other4 by (unfold exchange_data_modified; simpl; intuition discriminate).
    unfold s3, exchange_capacity_state, s2, exchange_depth_state.
    rewrite -> !lookup_local_other by discriminate. exact Index1. }
  assert (AP4 : array_at c4 bp (words (fun i => nat_of_ord (p i)))).
  { apply Frame4; [exact (not_eq_sym DP)|exact PT|exact PO|exact AP]. }
  destruct (@llvm_exchange_permutation_array_stores layout bp (words (fun i => nat_of_ord (p i)))
    c4 s4 (nat_of_ord position) d (Z.of_nat (nat_of_ord (p position)))
    (Z.of_nat (nat_of_ord (p ord_max))) (Name "if.end153") varargs
    ltac:(rewrite words_length; exact Size) ltac:(rewrite words_length; exact CP)
    (words_nth_error (fun i => nat_of_ord (p i)) position)
    (words_nth_error (fun i => nat_of_ord (p i)) ord_max)
    Related4 AP4 Index4 (main_permutation _ _ _ _ _ _ _ Registers4)
    (main_permutation_top _ _ _ _ _ _ _ Registers4))
    as (cp & c5 & s5 & PermLoadSelected & PermLoadTop & PermStoreSelected & PermStoreTop &
      Related5 & AP5 & Perm & Other5 & Frame5 & Writable5).
  exists c1, c2, c3, c4, cp, c5, s5.
  split; [exact (proj1 (AD _ _ (words_nth_error source position)))|].
  split; [exact (proj1 (AD _ _ (words_nth_error source ord_max)))|].
  split; [exact CountLoad|]. split; [exact StoreSelected|]. split; [exact StoreTop|].
  split; [exact StoreTrace|]. split; [exact StoreCount|].
  split; [exact PermLoadSelected|]. split; [exact PermLoadTop|].
  split; [exact PermStoreSelected|]. split; [exact PermStoreTop|].
  split; [exact Related5|]. split.
  - constructor.
    + apply Frame5; [exact DP|]. rewrite (@words_stack_swap d source position) in AD4. exact AD4.
    + rewrite (@words_permutation_swap d p position) in AP5. exact AP5.
    + apply Frame5; [exact (not_eq_sym PT)|].
      rewrite trace_words_append. replace (Z.of_nat (Legacy.Permute.depth position))
        with (Z.of_nat d - Z.of_nat (nat_of_ord position)).
      * exact AT4.
      * unfold Legacy.Permute.depth, subn. symmetry. apply Nat2Z.inj_sub.
        change (nat_of_ord position <= d)%coq_nat. lia.
    + apply Frame5; [exact (not_eq_sym PO)|].
      rewrite List.length_app. cbn [List.length]. rewrite Nat2Z.inj_add.
      rewrite trace_words_length in AO4. exact AO4.
    + intros k K. exact (proj1 (Related5 trace k ltac:(lia))).
  - split.
    + eapply exchange_main_registers; eassumption.
    + split.
      * eapply steps_next; [exact (proj2_sig exchange_compare)|exact Compare|].
        eapply steps_next; [exact (proj2_sig exchange_depth)|exact Depth|].
        eapply steps_next; [exact (proj2_sig exchange_capacity)|exact Check|].
        eapply steps_next; [exact (proj2_sig exchange_data)|exact Data|].
        eapply steps_next; [exact (proj2_sig exchange_permutation)|exact Perm|constructor].
      * split.
        -- intros id [Outside OutsideData]. rewrite -> Other5 by exact Outside.
           rewrite -> Other4 by exact OutsideData.
           unfold s3. rewrite -> exchange_capacity_other by exact Outside.
           unfold s2. rewrite -> exchange_depth_other by exact Outside.
           apply exchange_compare_other, Outside.
        -- intros other values ND NP NT NO Other. apply Frame5; [exact NP|].
           apply Frame4; assumption.
Qed.
End Success.

Print Assumptions llvm_exchange_data_array_stores.
Print Assumptions llvm_successful_exchange_stores.
