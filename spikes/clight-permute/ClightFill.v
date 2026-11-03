(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar
  ClightChoose ClightLoop ClightNormalize ClightSearch ModelArrays SolcModel
  ModelProofs FirstFree.
Import ListNotations.

Definition fill_body : statement :=
  when (ne (cell data (reg i)) (cell target (reg i))) (seq [
    Permute.set j (lit 0);
    search_scan;
    when (Permute.eq (reg j) (reg n)) (ret 2);
    put permutation (reg i) (reg j);
    put used (reg j) (lit 1)
  ]).

Definition used_flags {count} (reserved : {set 'I_count}) (x : 'I_count) : nat :=
  if x \in reserved then 1%nat else 0%nat.

Lemma used_flags_uint count (reserved : {set 'I_count}) x :
  uint (Z.of_nat (used_flags reserved x)).
Proof.
  unfold used_flags. destruct (x \in reserved); unfold uint;
    change Int.max_unsigned with 4294967295%Z; cbn; lia.
Qed.

Lemma used_flags_update count (reserved : {set 'I_count}) chosen :
  words (update_value (used_flags reserved) chosen 1%nat) =
  words (used_flags (chosen |: reserved)).
Proof.
  apply words_ext. intro x. unfold update_value, used_flags.
  rewrite !inE. destruct (x == chosen) eqn:E; rewrite E; reflexivity.
Qed.

Lemma destination_words_update count (assignment : 'I_count -> 'I_count) x y :
  words (update_value (fun z => nat_of_ord (assignment z)) x (nat_of_ord y)) =
  words (fun z => nat_of_ord (write_index assignment x y z)).
Proof.
  apply words_ext. intro z. unfold update_value, write_index.
  destruct (z == x) eqn:E; rewrite E; reflexivity.
Qed.

Theorem fill_body_found ge e le m count bd bt bp bu
    (source desired : 'I_count -> nat) (assignment : 'I_count -> 'I_count)
    (reserved : {set 'I_count}) (origin chosen : 'I_count) :
  bd <> bp -> bd <> bu -> bt <> bp -> bt <> bu -> bp <> bu ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat count))) ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat (nat_of_ord origin)))) ->
  (count <= 1024)%coq_nat ->
  (forall x, uint (Z.of_nat (source x))) ->
  (forall x, uint (Z.of_nat (desired x))) ->
  source origin <> desired origin ->
  first_free desired (source origin) reserved (enum 'I_count) = Some chosen ->
  array_at m bd (words source) -> array_at m bt (words desired) ->
  array_at m bp (words (fun x => nat_of_ord (assignment x))) ->
  array_at m bu (words (used_flags reserved)) ->
  exists m',
    exec_stmt function_entry2 ge e le m fill_body E0
      (PTree.set j (Vint (Int.repr (Z.of_nat (nat_of_ord chosen)))) le) m' Out_normal /\
    array_at m' bd (words source) /\ array_at m' bt (words desired) /\
    array_at m' bp (words (fun x => nat_of_ord (write_index assignment origin chosen x))) /\
    array_at m' bu (words (used_flags (chosen |: reserved))) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros DP DU TP TU PU Data TargetBase Perm Used N Origin Bound SourceUInt TargetUInt
    Different Choice Source Target Assignment Flags.
  assert (OK : (0 <= Z.of_nat (nat_of_ord origin) <= 2048)%Z)
    by (have H := elimT ltP (ltn_ord origin); lia).
  assert (RSource : expression ge le m (cell data (reg i)) =
    Some (Vint (Int.repr (Z.of_nat (source origin))))).
  { eapply cell_expression; eauto. exact (proj1 (Source _ _ (words_nth_error source origin))). }
  assert (RTarget : expression ge le m (cell target (reg i)) =
    Some (Vint (Int.repr (Z.of_nat (desired origin))))).
  { eapply cell_expression; eauto. exact (proj1 (Target _ _ (words_nth_error desired origin))). }
  assert (Cond : expression ge le m (ne (cell data (reg i)) (cell target (reg i))) = Some Vtrue).
  { pose proof (expression_compare ge le m Cne (cell data (reg i)) (cell target (reg i))
      _ _ Logic.eq_refl Logic.eq_refl (SourceUInt origin) (TargetUInt origin) RSource RTarget) as C.
    unfold zcompare in C.
    destruct (Coqlib.zeq (Z.of_nat (source origin)) (Z.of_nat (desired origin)));
      [exfalso; apply Different; lia|exact C]. }
  set (le0 := PTree.set j (Vint (Int.repr 0)) le).
  set (le1 := PTree.set j (Vint (Int.repr (Z.of_nat (nat_of_ord chosen)))) le).
  assert (Binding0 : forall id, id <> j -> PTree.get id le0 = PTree.get id le)
    by (intros id D; unfold le0; rewrite -> PTree.gso by exact D; reflexivity).
  assert (Binding1 : forall id, id <> j -> PTree.get id le1 = PTree.get id le)
    by (intros id D; unfold le1; rewrite -> PTree.gso by exact D; reflexivity).
  destruct (first_free_some Choice) as [_ [Free Match]].
  assert (FreeFlag : used_flags reserved chosen = 0%nat).
  { unfold used_flags. by move/negbTE: Free=> ->. }
  assert (Minimum : forall x : 'I_count, (0 <= nat_of_ord x)%coq_nat ->
    (nat_of_ord x < nat_of_ord chosen)%coq_nat ->
    used_flags reserved x <> 0%nat \/ desired x <> source origin).
  { intros x Lower Upper. destruct (first_free_minimum Choice Upper) as [In|No].
    - left. unfold used_flags. rewrite In. discriminate.
    - now right. }
  pose proof (search_scan_found ge e m count bd bt bu source desired
    (used_flags reserved) origin chosen Bound (SourceUInt origin) TargetUInt
    (used_flags_uint count reserved) Source Target Flags FreeFlag Match 0 le0
    ltac:(lia) Minimum
    ltac:(rewrite -> Binding0 by discriminate; exact Data)
    ltac:(rewrite -> Binding0 by discriminate; exact TargetBase)
    ltac:(rewrite -> Binding0 by discriminate; exact Used)
    ltac:(rewrite -> Binding0 by discriminate; exact N)
    ltac:(rewrite -> Binding0 by discriminate; exact Origin)
    ltac:(unfold le0; apply PTree.gss)) as Search.
  unfold le0 in Search. rewrite PTree.set2 in Search.
  assert (ChosenReg : PTree.get j le1 = Some (Vint (Int.repr (Z.of_nat (nat_of_ord chosen)))))
    by (unfold le1; apply PTree.gss).
  assert (NotMissing : expression ge le1 m (Permute.eq (reg j) (reg n)) = Some Vfalse).
  { assert (N1 : PTree.get n le1 = Some (Vint (Int.repr (Z.of_nat count)))).
    { rewrite -> Binding1 by discriminate. exact N. }
    assert (UC : uint (Z.of_nat (nat_of_ord chosen))).
    { unfold uint. change Int.max_unsigned with 4294967295%Z.
      have H := elimT ltP (ltn_ord chosen). lia. }
    assert (UN : uint (Z.of_nat count)).
    { unfold uint. change Int.max_unsigned with 4294967295%Z. lia. }
    pose proof (expression_nat_equal ge le1 m (reg j) (reg n) (nat_of_ord chosen) count
      Logic.eq_refl Logic.eq_refl UC UN ChosenReg N1) as C.
    assert (E : Nat.eqb (nat_of_ord chosen) count = false).
    { apply Nat.eqb_neq. have H := elimT ltP (ltn_ord chosen). lia. }
    rewrite E in C. exact C. }
  destruct (store_word_array ge e le1 m permutation bp count
    (fun x => nat_of_ord (assignment x)) origin (reg i) (reg j) (nat_of_ord chosen)
    ltac:(rewrite -> Binding1 by discriminate; exact Perm) Bound Logic.eq_refl
    ltac:(change (PTree.get i le1 = Some (Vint (Int.repr (Z.of_nat (nat_of_ord origin)))));
      rewrite -> Binding1 by discriminate; exact Origin) Logic.eq_refl ChosenReg Assignment)
    as [m1 [StorePerm [Assignment1 [Frame1 Writable1]]]].
  assert (Flags1 : array_at m1 bu (words (used_flags reserved)))
    by (apply Frame1; [congruence|exact Flags]).
  destruct (store_word_array ge e le1 m1 used bu count (used_flags reserved) chosen
    (reg j) (lit 1) 1%nat ltac:(rewrite -> Binding1 by discriminate; exact Used)
    Bound Logic.eq_refl ChosenReg Logic.eq_refl Logic.eq_refl Flags1)
    as [m2 [StoreUsed [Flags2 [Frame2 Writable2]]]].
  exists m2. split.
  - unfold fill_body, when at 1.
    eapply exec_Sifthenelse with (v1 := Vtrue) (b := true);
      [eapply expression_sound; exact Cond|reflexivity|].
    unfold seq. cbn [fold_right].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
    + apply exec_Sset. constructor.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [exact Search|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * unfold when at 1. eapply exec_if_test with (b := false); [exact NotMissing|reflexivity|constructor].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact StorePerm|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact StoreUsed|constructor].
  - split; [apply Frame2; [exact DU|apply Frame1; assumption]|].
    split; [apply Frame2; [exact TU|apply Frame1; assumption]|]. split.
    + rewrite <- destination_words_update. apply Frame2; [exact PU|exact Assignment1].
    + rewrite <- used_flags_update. split; [exact Flags2|]. split.
      * intros other xs OP OU Other. apply Frame2; [exact OU|apply Frame1; assumption].
      * intros other capacity Other. apply Writable2, Writable1, Other.
Qed.

Print Assumptions fill_body_found.
