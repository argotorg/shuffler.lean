(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory.
From Legacy Require Import Permute Proofs.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix ChooseBlocks Choose ChoosePermutation ExchangeBlocks.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition main_register_ids : list raw_id :=
  [Name "v1"; Name "v2"; Name "v3"; Name "v6"; Name "v7"; Name "sub";
   Name "arrayidx109"; Name "arrayidx137"; Name "add149";
   Name "arrayidx1"; Name "arrayidx2"].

Lemma main_registers_frame layout d bd bp trace output s s' :
  main_registers layout d bd bp trace output s ->
  (forall id, In id main_register_ids ->
    Maps.lookup id (locals s') = Maps.lookup id (locals s)) ->
  main_registers layout d bd bp trace output s'.
Proof.
  intros Registers Frame. destruct Registers as [N D P T O Top PT DT TC Fields].
  destruct Fields as [OP OD]. constructor; try constructor;
    rewrite -> Frame by (unfold main_register_ids; simpl; tauto); assumption.
Qed.

Lemma choice_main_registers layout d bd bp trace output s s' :
  main_registers layout d bd bp trace output s ->
  (forall id, ~ In id choose_modified ->
    Maps.lookup id (locals s') = Maps.lookup id (locals s)) ->
  main_registers layout d bd bp trace output s'.
Proof.
  intros Registers Frame. eapply main_registers_frame; [exact Registers|].
  intros id Inside. apply Frame.
  unfold main_register_ids in Inside. simpl in Inside.
  destruct Inside as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
    unfold choose_modified; simpl; intuition discriminate.
Qed.

Lemma exchange_main_registers layout d bd bp trace output s s' :
  main_registers layout d bd bp trace output s ->
  (forall id, ~ In id exchange_modified ->
    Maps.lookup id (locals s') = Maps.lookup id (locals s)) ->
  main_registers layout d bd bp trace output s'.
Proof.
  intros Registers Frame. eapply main_registers_frame; [exact Registers|].
  intros id Inside. apply Frame.
  unfold main_register_ids in Inside. simpl in Inside.
  destruct Inside as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
    unfold exchange_modified; simpl; intuition discriminate.
Qed.

Theorem main_choose layout d bd bp trace output source (p : 'S_(S d)) depths c s from varargs :
  (S d <= 1024)%coq_nat -> (S d <= block_words layout bp)%coq_nat ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  exists previous s', cells_related layout c (fst s') /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs from (Name "while.cond106") s previous
      (choose_target (option_map (fun x : 'I_(S d) => nat_of_ord x)
        (Legacy.Permute.choose p ord_max))) s' /\
    choose_binding previous s' (option_map (fun x : 'I_(S d) => nat_of_ord x)
      (Legacy.Permute.choose p ord_max)).
Proof.
  intros Size Capacity Related Arrays Registers.
  destruct (@choose_permutation layout d p bp c s from varargs Size Capacity Related
    (ClightMain.loop_destinations Arrays) (main_permutation _ _ _ _ _ _ _ Registers)
    (main_top _ _ _ _ _ _ _ Registers) (main_permutation_top _ _ _ _ _ _ _ Registers))
    as [previous [s' [Memory [Steps [Binding Frame]]]]].
  exists previous, s'. split; [rewrite Memory; exact Related|]. split.
  - eapply choice_main_registers; eassumption.
  - split; assumption.
Qed.

Lemma main_selected_bounds d (p : 'S_(S d)) position fuel :
  Legacy.Permute.choose p ord_max = Some position ->
  (Legacy.Permute.rank p ord_max < S fuel)%coq_nat ->
  (nat_of_ord position < d)%coq_nat /\
  (Legacy.Permute.rank (Legacy.Permute.exchange p ord_max position) ord_max < fuel)%coq_nat.
Proof.
  intros Selected Rank. split.
  - pose proof (chosen_depth Selected) as Positive.
    rewrite /Legacy.Permute.depth subn_gt0 in Positive.
    exact (elimT ltP Positive).
  - pose proof (choose_rank Selected) as Smaller.
    unfold addn, muln, subn in *. lia.
Qed.
