(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite Interfaces.Memory
  Implementations.Memory.
Require Import MemoryRelation WordMemory.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

(* A Clight block maps to a flat LLVM address and a provenance token.
   Blocks with no mapped cells have size zero. Disjointness is part of the
   layout type; callers cannot supply overlapping mapped arrays. *)
Record allocation_layout := {
  block_address : Values.block -> Z;
  block_provenance : Values.block -> prov;
  block_words : Values.block -> nat;
  blocks_disjoint : forall b b', b <> b' ->
    (0 < block_words b)%nat -> (0 < block_words b')%nat ->
    (block_address b + 4 * Z.of_nat (block_words b) <= block_address b' \/
     block_address b' + 4 * Z.of_nat (block_words b') <= block_address b)%Z
}.

Definition cell_address layout b k :=
  (block_address layout b + 4 * Z.of_nat k)%Z.

Definition cells_related layout (c : Mem.mem) (llvm : Impl.State) : Prop :=
  forall b k, (k < block_words layout b)%nat ->
    Mem.valid_access c Mint32 b (4 * Z.of_nat k) Writable /\
    writable_word llvm (cell_address layout b k) (block_provenance layout b) /\
    (forall x, Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x) ->
      word_at llvm (cell_address layout b k) (block_provenance layout b) x).

Lemma distinct_cells_disjoint layout b k b' j :
  (k < block_words layout b)%nat -> (j < block_words layout b')%nat ->
  b <> b' \/ k <> j ->
  (cell_address layout b k + 4 <= cell_address layout b' j \/
   cell_address layout b' j + 4 <= cell_address layout b k)%Z.
Proof.
  intros K J Different. unfold cell_address.
  destruct (Pos.eq_dec b b') as [E|E].
  - subst b'. destruct Different as [H|H]; [contradiction|].
    destruct (Nat.lt_trichotomy k j) as [Hlt|[Heq|Hgt]]; lia.
  - pose proof (blocks_disjoint layout b b' E ltac:(lia) ltac:(lia)) as D.
    lia.
Qed.

Lemma related_load layout c llvm b k x :
  cells_related layout c llvm -> (k < block_words layout b)%nat ->
  Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32)
    (cell_address layout b k, block_provenance layout b)) llvm =
    Ret (llvm, word_value x).
Proof.
  intros Relation K Load. apply load_word_correct.
  exact (proj2 (proj2 (Relation b k K)) x Load).
Qed.

Theorem related_store layout c llvm b k x :
  cells_related layout c llvm -> (k < block_words layout b)%nat ->
  exists c' llvm',
    Mem.store Mint32 c b (4 * Z.of_nat k) (Vint x) = Some c' /\
    run_memory (Impl.write_dvalue
      (cell_address layout b k, block_provenance layout b)
      (DTYPE_I 32) (word_value x)) llvm = Ret (llvm', tt) /\
    cells_related layout c' llvm' /\
    (forall a, (a < cell_address layout b k \/
      cell_address layout b k + 4 <= a)%Z ->
      IntMaps.IM.find a (bytes llvm') = IntMaps.IM.find a (bytes llvm)) /\
    Impl.Memory_stack_frame_stack (Impl.state_memory_stack llvm') =
      Impl.Memory_stack_frame_stack (Impl.state_memory_stack llvm) /\
    Impl.Memory_stack_heap (Impl.state_memory_stack llvm') =
      Impl.Memory_stack_heap (Impl.state_memory_stack llvm) /\
    Impl.state_provenance llvm' = Impl.state_provenance llvm.
Proof.
  intros Relation K.
  destruct (Relation b k K) as [Valid [Writable Value]].
  destruct (Mem.valid_access_store c Mint32 b (4 * Z.of_nat k) (Vint x) Valid)
    as [c' Store].
  destruct (@store_word_correct llvm (cell_address layout b k)
    (block_provenance layout b) x Writable)
    as [llvm' [Write [NewValue [Frame Rest]]]].
  exists c', llvm'. split; [exact Store|]. split; [exact Write|].
  split; [|exact (conj Frame Rest)].
  intros b' j J. destruct (Relation b' j J) as [Valid' [Writable' Value']].
  split; [eapply Mem.store_valid_access_1; eassumption|].
  destruct (Pos.eq_dec b b') as [BlockSame|BlockOther];
    destruct (Nat.eq_dec k j) as [CellSame|CellOther].
  { subst b' j. split; [eapply word_at_writable; exact NewValue|].
    intros y Load.
    rewrite (Mem.load_store_same Mint32 c b (4 * Z.of_nat k) (Vint x) c' Store)
      in Load.
    inversion Load; subst y. exact NewValue. }
  all: assert (Different : b <> b' \/ k <> j) by auto.
  all: assert (Outside : forall a,
      (cell_address layout b' j <= a < cell_address layout b' j + 4)%Z ->
      (a < cell_address layout b k \/ cell_address layout b k + 4 <= a)%Z).
  all: try (intros a A;
    pose proof (@distinct_cells_disjoint layout b k b' j K J Different); lia).
  all: split.
  all: try (eapply writable_word_unchanged; [intros; apply Frame, Outside; eassumption
      |exact Writable']).
  all: intros y Load; eapply word_at_unchanged;
    [intros; apply Frame, Outside; eassumption|apply Value'].
  all: rewrite (Mem.load_store_other Mint32 c b (4 * Z.of_nat k) (Vint x) c' Store)
    in Load; [exact Load|].
  all: destruct Different as [D|D]; [now left|right];
    change (4 * Z.of_nat j + 4 <= 4 * Z.of_nat k \/
      4 * Z.of_nat k + 4 <= 4 * Z.of_nat j)%Z;
    destruct (Nat.lt_trichotomy k j) as [Hlt|[Heq|Hgt]]; lia.
Qed.
