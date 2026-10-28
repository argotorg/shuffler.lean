(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree ITreeFacts.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  Initialize Prefix ValidationBlocks CheckedPrefix FixedBlocks Fixed FixedPrefix
  SearchBlocks FillBlocks Fill FillLoop NormalizedPrefix MainSetup.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Record main_registers layout d bd bp trace output s : Prop := {
  main_size : Maps.lookup (Name "v1") (locals s) =
    Some (word_value (Int.repr (Z.of_nat (S d))));
  main_data : Maps.lookup (Name "v2") (locals s) =
    Some (pointer_value (block_address layout bd) (block_provenance layout bd));
  main_permutation : Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp));
  main_trace : Maps.lookup (Name "v6") (locals s) =
    Some (pointer_value (block_address layout trace) (block_provenance layout trace));
  main_output : Maps.lookup (Name "v7") (locals s) =
    Some (pointer_value (block_address layout output) (block_provenance layout output));
  main_top : Maps.lookup (Name "sub") (locals s) =
    Some (word_value (Int.repr (Z.of_nat d)));
  main_permutation_top : Maps.lookup (Name "arrayidx109") (locals s) =
    Some (pointer_value (block_address layout bp + 4 * Z.of_nat d) (block_provenance layout bp));
  main_data_top : Maps.lookup (Name "arrayidx137") (locals s) =
    Some (pointer_value (block_address layout bd + 4 * Z.of_nat d) (block_provenance layout bd));
  main_trace_capacity : Maps.lookup (Name "add149") (locals s) =
    Some (word_value (Int.repr (2 * Z.of_nat (S d))));
  main_output_fields : output_registers layout output s
}.

Ltac normalized_unchanged :=
  unfold normalized_prefix_unmodified, fixed_prefix_unmodified, check_unmodified,
    prefix_unmodified, entry_unmodified, initialize_unmodified, validation_modified,
    fixed_unmodified, fixed_modified, fill_unmodified, fill_body_unmodified,
    fill_modified, search_modified;
  simpl; intuition discriminate.

Section Prefix.
Context (layout : allocation_layout) (d : nat) (source : 'I_(S d) -> nat) (p : 'S_(S d))
    (bd bp bt bu trace output : Values.block).
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypothesis Values : forall x, uint (Z.of_nat (source x)).
Hypotheses (DP : bd <> bp) (DU : bd <> bu) (DT : bd <> bt)
    (PU : bp <> bu) (PT : bp <> bt) (TU : bt <> bu)
    (DO : bd <> output) (PO : bp <> output) (OU : output <> bu) (OT : output <> bt).
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (S d <= block_words layout bt)%coq_nat)
    (CU : (S d <= block_words layout bu)%coq_nat)
    (CR : (2 * S d <= block_words layout trace)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Theorem main_prefix varargs c s :
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun x => nat_of_ord (p x))) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value (Int.repr (Z.of_nat (S d)))) ->
  Maps.lookup (Name "v2") (locals s) = Some
    (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v3") (locals s) = Some
    (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v4") (locals s) = Some
    (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v5") (locals s) = Some
    (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  Maps.lookup (Name "v6") (locals s) = Some
    (pointer_value (block_address layout trace) (block_provenance layout trace)) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  exists q c' s', SolcModel.normalize source p = Some q /\
    cells_related layout c' (fst s') /\
    @ClightMain.loop_arrays d bd bp trace output c' source q [] /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs (Name "entry") (Name "entry") s
      (Name "while.end105") (Name "while.cond106") s' /\
    (forall other values, other <> output -> other <> bu -> other <> bt -> other <> bp ->
      array_at c other values -> array_at c' other values).
Proof.
  intros Related AD AP N Data Perm Target Used Trace Output.
  destruct (@normalized_prefix layout d source p bd bp bt bu output Size Values
    DP DU DT PU PT TU DO PO CD CP CT CU CO varargs c s Related AD AP
    N Data Perm Target Used Output)
    as [q [c' [s1 [Normalized [Related1 [Data1 [Perm1 [Steps1 [Other1 [Frame [Fields Zeros]]]]]]]]]]].
  assert (Registers : forall id value, normalized_prefix_unmodified id ->
      Maps.lookup id (locals s) = Some value -> Maps.lookup id (locals s1) = Some value).
  { intros id value Outside At. rewrite -> Other1 by exact Outside. exact At. }
  pose (s2 := main_preheader_state s1 (Z.of_nat (S d))
    (block_address layout bp) (block_provenance layout bp)
    (block_address layout bd) (block_provenance layout bd)).
  assert (Setup : runs (denote_block (proj1_sig main_preheader) (Name "if.end103") varargs)
      s1 s2 (inl (Name "while.cond106"))).
  { apply main_preheader_runs; [lia| | |]; apply Registers;
      try normalized_unchanged; assumption. }
  assert (Memory : fst s2 = fst s1) by apply main_preheader_memory.
  pose proof (main_preheader_bindings s1 (Z.of_nat (S d))
    (block_address layout bp) (block_provenance layout bp)
    (block_address layout bd) (block_provenance layout bd)) as Bindings.
  replace (Z.of_nat (S d) - 1) with (Z.of_nat d) in Bindings by lia.
  destruct Bindings as [Top [PermTop [DataTop TraceCapacity]]].
  exists q, c', s2. split; [exact Normalized|].
  split; [rewrite Memory; exact Related1|]. split.
  - constructor; try assumption.
    + intros k value At. destruct k; discriminate.
    + apply Zeros; congruence.
    + intros k K. exact (proj1 (Related1 trace k ltac:(lia))).
  - split.
    + constructor; try assumption.
      all: try (unfold s2; rewrite -> main_preheader_other by
        (unfold main_preheader_modified; simpl; intuition discriminate);
        apply Registers; [normalized_unchanged|assumption]).
      destruct Fields. constructor; unfold s2; rewrite -> main_preheader_other by
        (unfold main_preheader_modified; simpl; intuition discriminate); assumption.
    + split; [|exact Frame].
      eapply block_steps_append; [exact Steps1|].
      eapply steps_next; [exact (proj2_sig main_preheader)|exact Setup|constructor].
Qed.
End Prefix.
