(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
Require Import CellRelation.
From X86 Require Import X86Layout X86Memory.
Open Scope Z_scope.

Lemma mem_insert_bytes_frame contents addr other machine :
  (forall k, (k < List.length contents)%nat ->
    addr_addN addr (N.of_nat k) <> other) ->
  (mem_insert_bytes addr contents machine) !! other = machine !! other.
Proof.
  revert addr machine. induction contents as [|byte rest IH]; intros addr machine Frame.
  - reflexivity.
  - cbn [mem_insert_bytes]. rewrite IH.
    + apply memory_insert_elsewhere. specialize (Frame 0%nat ltac:(cbn; lia)).
      now rewrite addr_addN_zero in Frame.
    + intros k K. rewrite addr_addN_assoc.
      replace (1 + N.of_nat k)%N with (N.of_nat (S k)) by lia.
      apply Frame. cbn. lia.
Qed.

Definition memory_mapping_preserved (before after : memoryMap) : Prop :=
  forall addr, is_Some (before !! addr) -> is_Some (after !! addr).

Lemma memory_insert_mapping machine addr byte :
  memory_mapping_preserved machine (<[addr := byte]> machine).
Proof.
  intros other Present. destruct (decide (addr = other)) as [Same|Different].
  - subst other. rewrite memory_insert_here. eexists. reflexivity.
  - rewrite memory_insert_elsewhere by exact Different. exact Present.
Qed.

Lemma memory_insert_bytes_mapping contents addr machine :
  memory_mapping_preserved machine (mem_insert_bytes addr contents machine).
Proof.
  revert addr machine. induction contents as [|byte rest IH]; intros addr machine.
  - intros other Present. exact Present.
  - intros other Present. cbn [mem_insert_bytes]. apply IH.
    exact (memory_insert_mapping machine addr byte other Present).
Qed.

Lemma mem_present_mapping addr size before after :
  memory_mapping_preserved before after ->
  mem_present addr size before = true -> mem_present addr size after = true.
Proof.
  intro Preserve. unfold mem_present. generalize (N.to_nat size) as count.
  intros count. revert addr. induction count as [|count IH]; intros addr Present.
  - reflexivity.
  - cbn [mem_present_nat] in Present |- *.
    apply andb_true_iff in Present as [Head Tail]. apply andb_true_iff. split.
    + apply bool_decide_eq_true_2, Preserve.
      now apply bool_decide_eq_true_1 in Head.
    + apply IH, Tail.
Qed.

Lemma machine_address_offset base index :
  addr_addN (machine_address base) (N.of_nat index) =
    machine_address (base + Z.of_nat index).
Proof.
  unfold addr_addN, machine_address. apply bv_eq.
  rewrite bv_add_Z_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

Lemma different_cell_addresses layout b k b' j byte byte' :
  (k < block_words (cell_layout layout) b)%nat ->
  (j < block_words (cell_layout layout) b')%nat ->
  b <> b' \/ k <> j -> (byte < 4)%nat -> (byte' < 4)%nat ->
  addr_addN (machine_address (cell_address (cell_layout layout) b k)) (N.of_nat byte) <>
    addr_addN (machine_address (cell_address (cell_layout layout) b' j)) (N.of_nat byte').
Proof.
  intros K J Different Byte Byte'. rewrite !machine_address_offset.
  intro Equal. apply (f_equal bv_unsigned) in Equal.
  change ((cell_address (cell_layout layout) b k + Z.of_nat byte) mod address_modulus =
    (cell_address (cell_layout layout) b' j + Z.of_nat byte') mod address_modulus)
    in Equal.
  exact (different_cells_mod layout b k b' j (Z.of_nat byte) (Z.of_nat byte')
    K J Different ltac:(lia) ltac:(lia) Equal).
Qed.

Lemma mem_insert_word_frame addr other (value : bv 32) machine :
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    addr_addN addr (N.of_nat i) <> addr_addN other (N.of_nat j)) ->
  mem_lookup other 4 (mem_insert addr 4 value machine) = mem_lookup other 4 machine.
Proof.
  intro Frame. apply mem_lookup_frame. intros location At.
  unfold addr_range, seqN in At.
  apply List.in_map_iff in At as [n [Address At]].
  apply List.in_map_iff in At as [j [Number At]].
  apply List.in_seq in At. change (0 <= j < 0 + 4)%nat in At. subst n location.
  unfold mem_insert. apply mem_insert_bytes_frame. intros i I.
  rewrite length_bv_to_bytes in I. change (i < 4)%nat in I.
  apply Frame; lia.
Qed.

Theorem machine_cells_related_store layout c machine b k x c' :
  machine_cells_related layout c machine ->
  (k < block_words (cell_layout layout) b)%nat ->
  Mem.store Mint32 c b (4 * Z.of_nat k) (Vint x) = Some c' ->
  machine_cells_related layout c'
    (mem_insert (machine_address (cell_address (cell_layout layout) b k)) 4
      (machine_word x) machine).
Proof.
  intros Related K Store b' j J.
  destruct (Related b' j J) as [Mapped Value]. split.
  - eapply mem_present_mapping; [apply memory_insert_bytes_mapping|exact Mapped].
  - intros y Load.
    destruct (Pos.eq_dec b b') as [BlockSame|BlockOther];
      destruct (Nat.eq_dec k j) as [CellSame|CellOther].
    { subst b' j.
      rewrite (Mem.load_store_same Mint32 c b (4 * Z.of_nat k) (Vint x) c' Store)
        in Load. inversion Load; subst y. apply read_insert_word. }
    all: assert (Different : b <> b' \/ k <> j) by auto.
    all: unfold machine_word_at; rewrite mem_insert_word_frame.
    all: try (intros i l I L; apply different_cell_addresses; assumption).
    all: apply Value.
    all: rewrite (Mem.load_store_other Mint32 c b (4 * Z.of_nat k) (Vint x) c' Store)
      in Load; [exact Load|].
    all: destruct Different as [D|D]; [now left|right].
    all: change (4 * Z.of_nat j + 4 <= 4 * Z.of_nat k \/
      4 * Z.of_nat k + 4 <= 4 * Z.of_nat j)%Z.
    all: destruct (Nat.lt_trichotomy k j) as [Less|[Same|Greater]]; lia.
Qed.

Print Assumptions mem_insert_bytes_frame.
Print Assumptions mem_present_mapping.
Print Assumptions machine_cells_related_store.

Theorem machine_cells_related_write layout c state b k x c' :
  machine_cells_related layout c (archState.memory (sst state)) ->
  (k < block_words (cell_layout layout) b)%nat ->
  Mem.store Mint32 c b (4 * Z.of_nat k) (Vint x) = Some c' ->
  let addr := machine_address (cell_address (cell_layout layout) b k) in
  let final := stored_bytes_state state addr (bv_to_bytes 8 (machine_word x)) in
  sequential_model_outcome None
    (MemWrite (MemReq.make (Tiny_x86.create_writeAccessDescriptor tt) addr tt 4 0)
      (machine_word x) (bv_0 0)) state = Exec.make [(final, Ok tt)] [] /\
  machine_cells_related layout c' (archState.memory (sst final)).
Proof.
  intros Related K Store addr final. split.
  - apply explicit_write_seq. exact (proj1 (Related b k K)).
  - unfold final. rewrite stored_bytes_memory.
    exact (machine_cells_related_store layout c (archState.memory (sst state))
      b k x c' Related K Store).
Qed.

Print Assumptions machine_cells_related_write.

Lemma read_insert_doubleword machine addr (value : bv 64) :
  mem_lookup addr 8 (mem_insert addr 8 value machine) = Some value.
Proof.
  change (mem_lookup addr 8 (mem_insert_bytes addr (@bv_to_bytes 8 64 value) machine) = Some value).
  remember (bv_to_bytes 8 value) as contents eqn:Contents.
  assert (Length : List.length contents = 8%nat).
  { rewrite Contents, length_bv_to_bytes. reflexivity. }
  destruct contents as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]];
    cbn in Length; try discriminate.
  destruct rest; [|discriminate].
  set (after := mem_insert_bytes addr [b0; b1; b2; b3; b4; b5; b6; b7] machine).
  change (option_map (bv_of_bytes 64) (list_of_options
    [after !! addr_addN addr 0; after !! addr_addN addr 1;
     after !! addr_addN addr 2; after !! addr_addN addr 3;
     after !! addr_addN addr 4; after !! addr_addN addr 5;
     after !! addr_addN addr 6; after !! addr_addN addr 7]) = Some value).
  unfold after. cbn [mem_insert_bytes].
  repeat rewrite addr_addN_assoc. repeat rewrite addr_addN_zero.
  repeat first [rewrite memory_insert_here |
    rewrite memory_insert_elsewhere by
      (unfold addr_addN; intro Equal;
       lazymatch type of Equal with
       | @eq _ (bv_add_Z ?a ?i) ?a =>
           rewrite <- (bv_add_Z_0 a) in Equal at 2
       | _ => idtac
       end;
       apply bv_add_Z_inj_l in Equal;
       [discriminate |
        lazymatch goal with |- 0 <= ?i < _ =>
          change (0 <= i < 18446744073709551616); lia end |
        lazymatch goal with |- 0 <= ?i < _ =>
          change (0 <= i < 18446744073709551616); lia end])].
  change (Some (bv_of_bytes 64 [b0; b1; b2; b3; b4; b5; b6; b7]) = Some value).
  rewrite Contents, bv_of_bytes_bv_to_bytes by discriminate. reflexivity.
Qed.

Print Assumptions read_insert_doubleword.
