(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Legacy Require Import Permute.
Require Import ClightMemory ModelArrays ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  FixedBlocks Choose ExchangeBlocks MainPrefix MainInvariant ExchangePermutation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem llvm_exchange_permutation_array_stores layout bp xs c s k top xp xt from varargs :
  (List.length xs <= 1024)%coq_nat ->
  (List.length xs <= block_words layout bp)%coq_nat ->
  nth_error xs k = Some xp -> nth_error xs top = Some xt ->
  cells_related layout c (fst s) -> array_at c bp xs ->
  Maps.lookup (Name "idxprom134") (locals s) = Some (index_value (Z.of_nat k)) ->
  Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "arrayidx109") (locals s) =
    Some (pointer_value (block_address layout bp + 4 * Z.of_nat top) (block_provenance layout bp)) ->
  exists c1 c' s',
    Mem.load Mint32 c bp (4 * Z.of_nat k) = Some (Vint (Int.repr xp)) /\
    Mem.load Mint32 c bp (4 * Z.of_nat top) = Some (Vint (Int.repr xt)) /\
    Mem.store Mint32 c bp (4 * Z.of_nat k) (Vint (Int.repr xt)) = Some c1 /\
    Mem.store Mint32 c1 bp (4 * Z.of_nat top) (Vint (Int.repr xp)) = Some c' /\
    cells_related layout c' (fst s') /\
    array_at c' bp (replace_nth top xp (replace_nth k xt xs)) /\
    runs (denote_block (proj1_sig exchange_permutation) from varargs) s s'
      (inl (Name "while.cond106")) /\
    (forall id, ~ In id exchange_modified -> Maps.lookup id (locals s') = Maps.lookup id (locals s)) /\
    (forall other values, other <> bp -> array_at c other values -> array_at c' other values) /\
    (forall other count, writable_array c other count -> writable_array c' other count).
Proof.
  intros Size Capacity K T Related Array Index Perm Top.
  assert (KB : (k < List.length xs)%coq_nat) by (apply nth_error_Some; rewrite -> K; discriminate).
  assert (TB : (top < List.length xs)%coq_nat) by (apply nth_error_Some; rewrite -> T; discriminate).
  destruct (@related_store layout c (fst s) bp k (Int.repr xt) Related ltac:(lia))
    as [c1 [m1 [Store1 [Write1 [Related1 Rest1]]]]].
  destruct (@related_store layout c1 m1 bp top (Int.repr xp) Related1 ltac:(lia))
    as [c2 [m2 [Store2 [Write2 [Related2 Rest2]]]]].
  pose (s2 := exchange_permutation_state s (Z.of_nat k)
    (block_address layout bp) (block_provenance layout bp) (Int.repr xp) (Int.repr xt) m1 m2).
  exists c1, c2, s2.
  split; [exact (proj1 (Array _ _ K))|]. split; [exact (proj1 (Array _ _ T))|].
  split; [exact Store1|]. split; [exact Store2|]. split; [exact Related2|]. split.
  - eapply array_store_same; [|exact Store2]. eapply array_store_same; eassumption.
  - split.
    + apply exchange_permutation_runs with (top_address := block_address layout bp + 4 * Z.of_nat top);
        try assumption; [lia| |].
      * eapply related_load; [exact Related|lia|]. exact (proj1 (Array _ _ K)).
      * eapply related_load; [exact Related|lia|]. exact (proj1 (Array _ _ T)).
    + split; [intros id Outside; apply exchange_permutation_other, Outside|]. split.
      * intros other values Different A.
        eapply array_store_disjoint; [|exact Different|exact Store2].
        eapply array_store_disjoint; [exact A|exact Different|exact Store1].
      * intros other count A.
        eapply writable_array_store; [|exact Store2]. eapply writable_array_store; eassumption.
Qed.

Theorem llvm_exchange_equal_choice_stores layout d bd bp trace output source (p : 'S_(S d)) depths
    (position : 'I_(S d)) c s from varargs :
  (S d <= 1024)%coq_nat ->
  (S d <= block_words layout bd)%coq_nat -> (S d <= block_words layout bp)%coq_nat ->
  bd <> bp -> trace <> bp -> output <> bp ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  choose_binding from s (Some (nat_of_ord position)) ->
  source ord_max = source position ->
  exists c1 c' s',
    Mem.load Mint32 c bd (4 * Z.of_nat (nat_of_ord position)) =
      Some (Vint (Int.repr (Z.of_nat (source position)))) /\
    Mem.load Mint32 c bd (4 * Z.of_nat d) = Some (Vint (Int.repr (Z.of_nat (source ord_max)))) /\
    Mem.load Mint32 c bp (4 * Z.of_nat (nat_of_ord position)) =
      Some (Vint (Int.repr (Z.of_nat (nat_of_ord (p position))))) /\
    Mem.load Mint32 c bp (4 * Z.of_nat d) =
      Some (Vint (Int.repr (Z.of_nat (nat_of_ord (p ord_max))))) /\
    Mem.store Mint32 c bp (4 * Z.of_nat (nat_of_ord position))
      (Vint (Int.repr (Z.of_nat (nat_of_ord (p ord_max))))) = Some c1 /\
    Mem.store Mint32 c1 bp (4 * Z.of_nat d)
      (Vint (Int.repr (Z.of_nat (nat_of_ord (p position))))) = Some c' /\
    cells_related layout c' (fst s') /\
    @ClightMain.loop_arrays d bd bp trace output c' source
      (Legacy.Permute.exchange p ord_max position) depths /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.end169") (Name "while.cond106") s' /\
    (forall other values, other <> bp -> array_at c other values -> array_at c' other values).
Proof.
  intros Size CD CP DP TP OP Related Arrays Registers Input Equal.
  destruct Arrays as [DataArray PermArray TraceArray OutArray Writable].
  assert (K : (nat_of_ord position < S d)%coq_nat) by exact (elimT ltP (ltn_ord position)).
  pose (x := Int.repr (Z.of_nat (source position))).
  pose (s1 := exchange_compare_state s (Z.of_nat (nat_of_ord position))
    (block_address layout bd) (block_provenance layout bd) x x).
  assert (Comparison : runs (denote_block (proj1_sig exchange_compare) from varargs) s s1
      (inl (if word_equal x x then Name "if.end169" else Name "if.then139"))).
  { apply exchange_compare_runs with (top_address := block_address layout bd + 4 * Z.of_nat d).
    - lia.
    - exact Input.
    - exact (main_data _ _ _ _ _ _ _ Registers).
    - exact (main_data_top _ _ _ _ _ _ _ Registers).
    - eapply related_load; [exact Related|lia|].
      exact (proj1 (DataArray _ _ (words_nth_error source position))).
    - eapply related_load; [exact Related|lia|].
      pose proof (proj1 (DataArray _ _ (words_nth_error source ord_max))) as Load.
      rewrite -> Equal in Load. exact Load. }
  unfold word_equal in Comparison. rewrite -> Z.eqb_refl in Comparison.
  assert (Related1 : cells_related layout c (fst s1)).
  { unfold s1. rewrite -> exchange_compare_memory. exact Related. }
  assert (Other1 : forall id, ~ In id exchange_modified ->
      Maps.lookup id (locals s1) = Maps.lookup id (locals s)).
  { intros id Outside. apply exchange_compare_other, Outside. }
  assert (Registers1 : main_registers layout d bd bp trace output s1).
  { eapply main_registers_frame; [exact Registers|].
    intros id Inside. apply Other1. unfold main_register_ids in Inside. simpl in Inside.
    destruct Inside as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
      unfold exchange_modified; simpl; intuition discriminate. }
  pose proof (exchange_compare_bindings s (Z.of_nat (nat_of_ord position))
    (block_address layout bd) (block_provenance layout bd) x x) as Bindings.
  destruct Bindings as [Position [Index Rest]].
  destruct (@llvm_exchange_permutation_array_stores layout bp (words (fun i => nat_of_ord (p i))) c s1
    (nat_of_ord position) d (Z.of_nat (nat_of_ord (p position))) (Z.of_nat (nat_of_ord (p ord_max)))
    (Name "if.end133") varargs
    ltac:(rewrite -> words_length; exact Size) ltac:(rewrite -> words_length; exact CP)
    (words_nth_error (fun i => nat_of_ord (p i)) position)
    (words_nth_error (fun i => nat_of_ord (p i)) ord_max) Related1 PermArray Index
    (main_permutation _ _ _ _ _ _ _ Registers1) (main_permutation_top _ _ _ _ _ _ _ Registers1))
    as (middle & c' & s' & PermSelected & PermTop & StoreSelected & StoreTop &
      Related' & Perm' & Swap & Other2 & Frame & Writable').
  rewrite (@words_permutation_swap d p position) in Perm'.
  exists middle, c', s'.
  split; [exact (proj1 (DataArray _ _ (words_nth_error source position)))|].
  split; [exact (proj1 (DataArray _ _ (words_nth_error source ord_max)))|].
  split; [exact PermSelected|]. split; [exact PermTop|].
  split; [exact StoreSelected|]. split; [exact StoreTop|].
  split; [exact Related'|]. split.
  - constructor; try assumption.
    + apply Frame; assumption.
    + apply Frame; assumption.
    + apply Frame; assumption.
    + apply Writable', Writable.
  - split.
    + eapply main_registers_frame; [exact Registers1|].
      intros id Inside. apply Other2. unfold main_register_ids in Inside. simpl in Inside.
      destruct Inside as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
        unfold exchange_modified; simpl; intuition discriminate.
    + split; [|exact Frame].
      eapply steps_next; [exact (proj2_sig exchange_compare)|exact Comparison|].
      eapply steps_next; [exact (proj2_sig exchange_permutation)|exact Swap|constructor].
Qed.

Print Assumptions llvm_exchange_permutation_array_stores.
Print Assumptions llvm_exchange_equal_choice_stores.
