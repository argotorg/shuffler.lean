(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory ClightScalar ClightFill ModelArrays SolcModel ModelProofs FirstFree.
Require Import CellRelation FixedBlocks Fixed.
From ASCommon Require Import Common Exec.
From mathcomp Require Import ssrbool eqtype fintype finset.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Execution X86Compare X86Search X86SearchLoop.
Open Scope Z_scope.
Local Notation nat_of_ord := fintype.nat_of_ord.

Definition search_words {count} (values : fintype.ordinal count -> nat) index :=
  Int.repr (List.nth index (words values) 0).

Lemma search_words_at count (values : fintype.ordinal count -> nat) index :
  search_words values (nat_of_ord index) = Int.repr (Z.of_nat (values index)).
Proof. unfold search_words. exact (f_equal Int.repr (words_nth values index)). Qed.

Lemma search_words_load count (values : fintype.ordinal count -> nat) c b index :
  array_at c b (words values) -> (index < count)%nat ->
  Mem.load Mint32 c b (4 * Z.of_nat index) = Some (Vint (search_words values index)).
Proof.
  intros Array Bound.
  pose (position := (fintype.Ordinal (ssrbool.introT ssrnat.ltP Bound) : fintype.ordinal count)).
  change (Mem.load Mint32 c b (4 * Z.of_nat (nat_of_ord position)) =
    Some (Vint (search_words values (nat_of_ord position)))).
  rewrite search_words_at. exact (proj1 (Array _ _ (words_nth_error values position))).
Qed.

Lemma search_nat_word_match value target flag :
  uint (Z.of_nat value) -> uint (Z.of_nat target) -> uint (Z.of_nat flag) ->
  search_word_match (Int.repr (Z.of_nat value)) (Int.repr (Z.of_nat target))
    (Int.repr (Z.of_nat flag)) = andb (Nat.eqb flag 0) (Nat.eqb value target).
Proof.
  intros Value Target Flag.
  change (andb (word_equal (Int.repr (Z.of_nat flag)) (Int.repr (Z.of_nat 0)))
    (word_equal (Int.repr (Z.of_nat value)) (Int.repr (Z.of_nat target))) =
    andb (Nat.eqb flag 0) (Nat.eqb value target)).
  rewrite !natural_word_equal by (try assumption; unfold uint; change Int.max_unsigned with 4294967295; lia).
  reflexivity.
Qed.

Theorem first_free_machine_search nondet layout (frame : call_frame layout program_bytes)
    count value (desired : fintype.ordinal count -> nat)
    reserved (bt bu : Values.block)
    c machine (chosen : fintype.ordinal count) source_old size_old :
  (count <= 1024)%nat ->
  (count <= block_words (cell_layout layout) bt)%nat ->
  (count <= block_words (cell_layout layout) bu)%nat ->
  uint (Z.of_nat value) -> (forall x, uint (Z.of_nat (desired x))) ->
  @first_free _ ssrnat.Datatypes_nat__canonical__eqtype_Equality desired value reserved
    (fintype.enum (fintype.ordinal count)) = Some chosen ->
  array_at c bt (words desired) -> array_at c bu (words (used_flags reserved)) ->
  machine_cells_related layout c (archState.memory (sst machine)) ->
  code_at machine (entry_pc frame) program_bytes -> registers_present machine ->
  read_reg_seq_state rip machine = Some (machine_address (entry_pc frame + 201)) ->
  read_reg_seq_state r11 machine = Some source_old ->
  low_register32 11 source_old = machine_word (Int.repr (Z.of_nat value)) ->
  read_reg_seq_state rcx machine = Some (pointer_to_block layout bt) ->
  read_reg_seq_state r8 machine = Some (pointer_to_block layout bu) ->
  read_reg_seq_state rdi machine = Some size_old ->
  low_register32 7 size_old = Z_to_bv 32 (Z.of_nat count) ->
  exists steps final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) steps machine final /\
    search_frame machine final /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 243)) /\
    read_reg_seq_state r13 final = Some (machine_address (Z.of_nat (nat_of_ord chosen))).
Proof.
  intros Bound CT CU ValueUInt TargetUInt Choice TargetArray FlagArray Related Code Present PC
    SourceRead SourceLow TargetRead UsedRead SizeRead SizeLow.
  assert (ChosenBound : (nat_of_ord chosen < count)%nat)
    by exact (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord chosen)).
  destruct (first_free_some Choice) as [_ [Free Match]].
  assert (FreeFlag : used_flags reserved chosen = 0%nat).
  { unfold used_flags.
    pose proof (ssrbool.negbTE Free) as NotUsed.
    match type of NotUsed with ?flag = false =>
      change ((if flag then 1 else 0) = 0)%nat
    end.
    rewrite NotUsed. reflexivity. }
  assert (Found : search_word_match (Int.repr (Z.of_nat value))
    (search_words desired (nat_of_ord chosen))
    (search_words (used_flags reserved) (nat_of_ord chosen)) = true).
  { rewrite !search_words_at, search_nat_word_match by (auto using used_flags_uint).
    rewrite FreeFlag, Match, !Nat.eqb_refl. reflexivity. }
  assert (Minimum : forall index, (0 <= index < nat_of_ord chosen)%nat ->
    search_word_match (Int.repr (Z.of_nat value)) (search_words desired index)
      (search_words (used_flags reserved) index) = false).
  { intros index Between. assert (IndexBound : (index < count)%nat) by lia.
    pose (position := (fintype.Ordinal (ssrbool.introT ssrnat.ltP IndexBound) : fintype.ordinal count)).
    change (search_word_match (Int.repr (Z.of_nat value))
      (search_words desired (nat_of_ord position))
      (search_words (used_flags reserved) (nat_of_ord position)) = false).
    rewrite !search_words_at, search_nat_word_match by (auto using used_flags_uint).
    destruct (first_free_minimum Choice (x := position) ltac:(exact (proj2 Between)))
      as [Used|Different].
    - unfold used_flags. unfold is_true in Used.
      match type of Used with ?flag = true =>
        change (andb (Nat.eqb (if flag then 1 else 0) 0)
          (Nat.eqb value (desired position)) = false)
      end.
      rewrite Used. reflexivity.
    - assert (Miss : Nat.eqb value (desired position) = false) by (apply Nat.eqb_neq; congruence).
      rewrite Miss, Bool.andb_false_r. reflexivity. }
  destruct (search_preheader nondet layout frame machine Code Present PC)
    as [scan [Entry [EntryFrame [ScanCode [ScanPresent [ScanPC ScanIndex]]]]]].
  assert (ScanRelated : machine_cells_related layout c (archState.memory (sst scan))).
  { rewrite (proj1 EntryFrame). exact Related. }
  assert (ScanSource : read_reg_seq_state r11 scan = Some source_old).
  { rewrite (proj2 EntryFrame r11) by (unfold search_clobbered; cbn; intuition discriminate).
    exact SourceRead. }
  assert (ScanTarget : read_reg_seq_state rcx scan = Some (pointer_to_block layout bt)).
  { rewrite (proj2 EntryFrame rcx) by (unfold search_clobbered; cbn; intuition discriminate).
    exact TargetRead. }
  assert (ScanUsed : read_reg_seq_state r8 scan = Some (pointer_to_block layout bu)).
  { rewrite (proj2 EntryFrame r8) by (unfold search_clobbered; cbn; intuition discriminate).
    exact UsedRead. }
  assert (ScanSize : read_reg_seq_state rdi scan = Some size_old).
  { rewrite (proj2 EntryFrame rdi) by (unfold search_clobbered; cbn; intuition discriminate).
    exact SizeRead. }
  destruct (search_found_loop nondet layout frame scan count 0 (nat_of_ord chosen) bt bu
    (Int.repr (Z.of_nat value)) source_old size_old (search_words desired)
    (search_words (used_flags reserved)) c ltac:(lia) Bound CT CU Found Minimum
    ltac:(intros index Between; apply search_words_load; [exact TargetArray|lia])
    ltac:(intros index Between; apply search_words_load; [exact FlagArray|lia])
    ScanCode ScanPresent ScanPC ScanIndex ScanSource SourceLow ScanTarget ScanUsed ScanSize SizeLow ScanRelated)
    as [rest [final [Search [SearchFrame [FinalCode [FinalPresent [FinalPC FinalIndex]]]]]]].
  exists (1 + rest)%nat, final. split.
  - eapply instruction_steps_append; [exact Entry|exact Search].
  - split; [eapply search_frame_trans; [exact EntryFrame|exact SearchFrame]|].
    split; [exact FinalCode|]. split; [exact FinalPresent|]. split; assumption.
Qed.

Print Assumptions first_free_machine_search.
