(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar
  ClightEntry ClightExchangeSuccess ClightLoop ModelArrays.
Import ListNotations.

Definition fixed_body : statement :=
  Sifthenelse (Permute.eq (cell data (reg i)) (cell target (reg i)))
    (seq [put permutation (reg i) (reg i); put used (reg i) (lit 1)])
    (put used (reg i) (lit 0)).

Lemma store_word_array ge e le m a b count (f : 'I_count -> nat)
    (index : 'I_count) offset rhs value :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  (count <= 1024)%coq_nat ->
  typeof offset = u32 ->
  expression ge le m offset = Some (Vint (Int.repr (Z.of_nat (nat_of_ord index)))) ->
  typeof rhs = u32 ->
  expression ge le m rhs = Some (Vint (Int.repr (Z.of_nat value))) ->
  array_at m b (words f) ->
  exists m',
    exec_stmt function_entry2 ge e le m (Sassign (cell a offset) rhs) E0 le m' Out_normal /\
    array_at m' b (words (update_value f index value)) /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros Base Bound OffsetTy Offset RhsTy Rhs Array.
  assert (K : (nat_of_ord index < List.length (words f))%coq_nat).
  { rewrite words_length. exact (elimT ltP (ltn_ord index)). }
  destruct (array_store_exists m b (words f) (nat_of_ord index) (Z.of_nat value) Array K)
    as [m' Store].
  assert (RunStore : store ge le m (cell a offset) rhs = Some m').
  { eapply cell_store; eauto. rewrite words_length in K. lia. }
  exists m'. split.
  - now apply exec_store.
  - split.
    + rewrite <- words_update. eapply array_store_same; eauto.
    + split.
      * intros other xs Separate Other. eapply array_store_disjoint; eauto.
      * intros other capacity Other. eapply writable_array_store; eauto.
Qed.

Lemma store_prefix_word ge e le m a b prefix count offset value :
  PTree.get a le = Some (Vptr b Ptrofs.zero) ->
  ((List.length prefix < count)%coq_nat /\ (count <= 1024)%coq_nat) ->
  typeof offset = u32 ->
  expression ge le m offset = Some (Vint (Int.repr (Z.of_nat (List.length prefix)))) ->
  array_at m b prefix -> writable_array m b count ->
  exists m',
    exec_stmt function_entry2 ge e le m
      (Sassign (cell a offset) (lit (Z.of_nat value))) E0 le m' Out_normal /\
    array_at m' b (prefix ++ [Z.of_nat value]) /\
    (forall other xs, other <> b -> array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros Base Bounds OffsetTy Offset Prefix Writable.
  destruct (Mem.valid_access_store m Mint32 b (4 * Z.of_nat (List.length prefix))
    (Vint (Int.repr (Z.of_nat value))) (Writable _ (proj1 Bounds))) as [m' Store].
  assert (RunStore : store ge le m (cell a offset) (lit (Z.of_nat value)) = Some m').
  { eapply cell_store; eauto; try reflexivity; lia. }
  exists m'. split; [now apply exec_store|]. split.
  - eapply array_append_store; eauto.
  - split.
    + intros other xs Separate Other. eapply array_store_disjoint; eauto.
    + intros other capacity Other. eapply writable_array_store; eauto.
Qed.

(* One iteration of the first normalization pass. This statement is exactly
   the body of the first [each] in [Permute.normalize]. *)
Theorem fixed_body_correct ge e le m count bd bt bp bu
    (source desired assignment : 'I_count -> nat) flag_prefix (index : 'I_count) :
  bd <> bp -> bd <> bu -> bt <> bp -> bt <> bu -> bp <> bu ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat (nat_of_ord index)))) ->
  (count <= 1024)%coq_nat ->
  uint (Z.of_nat (source index)) -> uint (Z.of_nat (desired index)) ->
  array_at m bd (words source) -> array_at m bt (words desired) ->
  array_at m bp (words assignment) -> array_at m bu flag_prefix ->
  writable_array m bu count -> List.length flag_prefix = nat_of_ord index ->
  exists m',
    exec_stmt function_entry2 ge e le m fixed_body E0 le m' Out_normal /\
    array_at m' bd (words source) /\
    array_at m' bt (words desired) /\
    array_at m' bp (words (if Nat.eqb (source index) (desired index)
      then update_value assignment index (nat_of_ord index) else assignment)) /\
    array_at m' bu (flag_prefix ++
      [if Nat.eqb (source index) (desired index) then 1%Z else 0%Z]) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros DP DU TP TU PU Data Target Perm Used Index Bound SourceUInt TargetUInt
    Source TargetArray Assignment Flags WritableFlags PrefixLength.
  assert (K : (0 <= Z.of_nat (nat_of_ord index) <= 2048)%Z).
  { have H := elimT ltP (ltn_ord index). lia. }
  assert (RSource : expression ge le m (cell data (reg i)) =
    Some (Vint (Int.repr (Z.of_nat (source index))))).
  { eapply cell_expression; eauto. exact (proj1 (Source _ _ (words_nth_error source index))). }
  assert (RTarget : expression ge le m (cell target (reg i)) =
    Some (Vint (Int.repr (Z.of_nat (desired index))))).
  { eapply cell_expression; eauto. exact (proj1 (TargetArray _ _ (words_nth_error desired index))). }
  pose proof (expression_compare ge le m Ceq (cell data (reg i)) (cell target (reg i))
    _ _ Logic.eq_refl Logic.eq_refl SourceUInt TargetUInt RSource RTarget) as Compare.
  destruct (Nat.eqb (source index) (desired index)) eqn:Equal.
  - apply Nat.eqb_eq in Equal.
    assert (Cond : expression ge le m (Permute.eq (cell data (reg i)) (cell target (reg i))) = Some Vtrue).
    { unfold zcompare in Compare.
      destruct (Coqlib.zeq (Z.of_nat (source index)) (Z.of_nat (desired index)));
        [exact Compare|congruence]. }
    destruct (store_word_array ge e le m permutation bp count assignment index
      (reg i) (reg i) (nat_of_ord index) Perm Bound Logic.eq_refl Index Logic.eq_refl Index Assignment)
      as [m1 [WritePerm [Assignment1 [Frame1 Writable1]]]].
    assert (Flags1 : array_at m1 bu flag_prefix) by (apply Frame1; [congruence|exact Flags]).
    assert (PrefixBound : (List.length flag_prefix < count)%coq_nat /\ (count <= 1024)%coq_nat).
    { rewrite PrefixLength. have H := elimT ltP (ltn_ord index). lia. }
    destruct (store_prefix_word ge e le m1 used bu flag_prefix count (reg i) 1%nat
      Used PrefixBound Logic.eq_refl ltac:(rewrite PrefixLength; exact Index)
      Flags1 (Writable1 _ _ WritableFlags))
      as [m2 [WriteUsed [Flags2 [Frame2 Writable2]]]].
    exists m2. split.
    + unfold fixed_body. eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      * eapply expression_sound. exact Cond.
      * reflexivity.
      * unfold seq. cbn [fold_right].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact WritePerm|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact WriteUsed|constructor].
    + split; [apply Frame2; [exact DU|apply Frame1; assumption]|].
      split; [apply Frame2; [exact TU|apply Frame1; assumption]|].
      split; [apply Frame2; [exact PU|exact Assignment1]|].
      split; [exact Flags2|]. split.
      * intros other xs OP OU Other. apply Frame2; [exact OU|apply Frame1; assumption].
      * intros other capacity Other. apply Writable2, Writable1, Other.
  - apply Nat.eqb_neq in Equal.
    assert (Cond : expression ge le m (Permute.eq (cell data (reg i)) (cell target (reg i))) = Some Vfalse).
    { unfold zcompare in Compare.
      destruct (Coqlib.zeq (Z.of_nat (source index)) (Z.of_nat (desired index)));
        [exfalso; apply Equal; lia|exact Compare]. }
    assert (PrefixBound : (List.length flag_prefix < count)%coq_nat /\ (count <= 1024)%coq_nat).
    { rewrite PrefixLength. have H := elimT ltP (ltn_ord index). lia. }
    destruct (store_prefix_word ge e le m used bu flag_prefix count (reg i) 0%nat
      Used PrefixBound Logic.eq_refl ltac:(rewrite PrefixLength; exact Index) Flags WritableFlags)
      as [m1 [WriteUsed [Flags1 [Frame1 Writable1]]]].
    exists m1. split.
    + unfold fixed_body. eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      * eapply expression_sound. exact Cond.
      * reflexivity.
      * exact WriteUsed.
    + split; [apply Frame1; assumption|]. split; [apply Frame1; assumption|].
      split; [apply Frame1; assumption|]. split; [exact Flags1|]. split.
      * intros other xs OP OU Other. apply Frame1; assumption.
      * exact Writable1.
Qed.

Print Assumptions fixed_body_correct.

Definition fixed_assignment {count} (source desired original : 'I_count -> nat)
    (processed : nat) (x : 'I_count) :=
  if Nat.ltb (nat_of_ord x) processed then
    if Nat.eqb (source x) (desired x) then nat_of_ord x else original x
  else original x.

Definition fixed_flags {count} (source desired : 'I_count -> nat) (x : 'I_count) : nat :=
  if Nat.eqb (source x) (desired x) then 1%nat else 0%nat.

Lemma ltb_succ_neq j k : j <> k -> Nat.ltb j k = Nat.ltb j (S k).
Proof.
  intro H. destruct (Nat.ltb j k) eqn:A, (Nat.ltb j (S k)) eqn:B; auto;
    apply Nat.ltb_lt in A || apply Nat.ltb_ge in A;
    apply Nat.ltb_lt in B || apply Nat.ltb_ge in B; lia.
Qed.

Lemma fixed_assignment_step count (source desired original : 'I_count -> nat)
    (index : 'I_count) :
  words (if Nat.eqb (source index) (desired index)
    then update_value (fixed_assignment source desired original (nat_of_ord index))
      index (nat_of_ord index)
    else fixed_assignment source desired original (nat_of_ord index)) =
  words (fixed_assignment source desired original (S (nat_of_ord index))).
Proof.
  apply words_ext. intro x.
  assert (Other : x == index = false -> nat_of_ord x <> nat_of_ord index).
  { intros E H. have Ex : x = index by apply val_inj.
    subst x. rewrite eqxx in E. discriminate. }
  destruct (Nat.eqb (source index) (desired index)) eqn:G;
    unfold fixed_assignment, update_value; cbv beta;
    destruct (x == index) eqn:E.
  - have Ex : x = index := elimT eqP E. subst x. rewrite G.
    assert (B : Nat.ltb (nat_of_ord index) (S (nat_of_ord index)) = true)
      by (apply Nat.ltb_lt; lia).
    rewrite B. reflexivity.
  - rewrite <- ltb_succ_neq by (now apply Other). reflexivity.
  - have Ex : x = index := elimT eqP E. subst x. rewrite G.
    destruct (Nat.ltb (nat_of_ord index) (nat_of_ord index)),
      (Nat.ltb (nat_of_ord index) (S (nat_of_ord index))); reflexivity.
  - rewrite <- ltb_succ_neq by (now apply Other). reflexivity.
Qed.

Lemma firstn_step {A} (xs : list A) k x :
  List.nth_error xs k = Some x ->
  List.firstn (S k) xs = List.firstn k xs ++ [x].
Proof.
  revert k. induction xs as [|a xs IH]; intros [|k] H; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - f_equal. now apply IH.
Qed.

Lemma increment_index ge e le m k :
  (k <= 1024)%coq_nat ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat k))) ->
  exec_stmt function_entry2 ge e le m (inc i) E0
    (PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) le) m Out_normal.
Proof.
  intros K I. apply exec_Sset. apply expression_sound.
  replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
  eapply expression_add; eauto; try reflexivity;
    unfold uint; change Int.max_unsigned with 4294967295%Z; lia.
Qed.

Theorem fixed_pass_correct ge e le m count bd bt bp bu
    (source desired original : 'I_count -> nat) :
  bd <> bp -> bd <> bu -> bt <> bp -> bt <> bu -> bp <> bu ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat count))) ->
  (count <= 1024)%coq_nat ->
  (forall x, uint (Z.of_nat (source x))) ->
  (forall x, uint (Z.of_nat (desired x))) ->
  array_at m bd (words source) -> array_at m bt (words desired) ->
  array_at m bp (words original) -> writable_array m bu count ->
  exists le' m',
    exec_stmt function_entry2 ge e le m (each i fixed_body) E0 le' m' Out_normal /\
    array_at m' bd (words source) /\ array_at m' bt (words desired) /\
    array_at m' bp (words (fun x => if Nat.eqb (source x) (desired x)
      then nat_of_ord x else original x)) /\
    array_at m' bu (words (fixed_flags source desired)) /\
    (forall id, id <> i -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros DP DU TP TU PU Data Target Perm Used N Bound SourceUInt TargetUInt
    Source TargetArray Original Writable.
  set (I := fun k env memory =>
    (k <= count)%coq_nat /\
    PTree.get i env = Some (Vint (Int.repr (Z.of_nat k))) /\
    (forall id, id <> i -> PTree.get id env = PTree.get id le) /\
    array_at memory bd (words source) /\ array_at memory bt (words desired) /\
    array_at memory bp (words (fixed_assignment source desired original k)) /\
    array_at memory bu (List.firstn k (words (fixed_flags source desired))) /\
    writable_array memory bu count /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at m other xs -> array_at memory other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array memory other capacity)).
  assert (Registers : forall k env memory, I k env memory ->
    PTree.get i env = Some (Vint (Int.repr (Z.of_nat k))) /\
    PTree.get n env = Some (Vint (Int.repr (Z.of_nat count)))).
  { intros k env memory [K [Index [Frame Rest]]]. split; [exact Index|].
    rewrite -> Frame by discriminate. exact N. }
  assert (Step : forall k env memory, (k < count)%coq_nat -> I k env memory ->
    exists env' memory', exec_stmt function_entry2 ge e env memory
      (seq [fixed_body; inc i]) E0 env' memory' Out_normal /\ I (S k) env' memory').
  { intros k env memory K [KB [Index [EnvFrame [D [T [P [U [W [Frame WFrame]]]]]]]]].
    pose index : 'I_count := Ordinal (introT ltP K).
    destruct (fixed_body_correct ge e env memory count bd bt bp bu source desired
      (fixed_assignment source desired original k)
      (List.firstn k (words (fixed_flags source desired))) index DP DU TP TU PU
      ltac:(rewrite -> EnvFrame by discriminate; exact Data)
      ltac:(rewrite -> EnvFrame by discriminate; exact Target)
      ltac:(rewrite -> EnvFrame by discriminate; exact Perm)
      ltac:(rewrite -> EnvFrame by discriminate; exact Used)
      Index Bound (SourceUInt index) (TargetUInt index) D T P U W
      ltac:(rewrite List.firstn_length words_length Nat.min_l; [reflexivity|lia]))
      as [memory' [Body [D' [T' [P' [U' [Frame' WFrame']]]]]]].
    exists (PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) env), memory'. split.
    - unfold seq. cbn [fold_right].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Body|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      + eapply increment_index with (k := k); [lia|exact Index].
      + constructor.
    - unfold I. split; [lia|]. split; [apply PTree.gss|]. split.
      + intros id Different. rewrite -> PTree.gso by exact Different. now apply EnvFrame.
      + split; [exact D'|]. split; [exact T'|]. split.
        * change k with (nat_of_ord index) in P'.
          rewrite fixed_assignment_step in P'. exact P'.
        * split.
          -- rewrite (firstn_step _ k (Z.of_nat (fixed_flags source desired index))).
             ++ unfold fixed_flags. destruct (Nat.eqb (source index) (desired index)); exact U'.
             ++ exact (words_nth_error (fixed_flags source desired) index).
          -- split; [apply WFrame'; exact W|]. split.
             ++ intros other xs OP OU Other. apply Frame'; [exact OP|exact OU|].
                apply Frame; assumption.
             ++ intros other capacity Other. apply WFrame', WFrame, Other. }
  assert (Initial : I 0%nat (PTree.set i (Vint (Int.repr 0)) le) m).
  { unfold I. split; [lia|]. split; [apply PTree.gss|]. split.
    - intros id Different. now rewrite PTree.gso.
    - split; [exact Source|]. split; [exact TargetArray|]. split.
      + assert (E : words (fixed_assignment source desired original 0) = words original).
        { apply words_ext. intro x. unfold fixed_assignment. now rewrite Nat.ltb_irrefl ||
            destruct (nat_of_ord x); reflexivity. }
        rewrite E. exact Original.
      + split.
        * intros k v H. destruct k; discriminate.
        * split; [exact Writable|]. split; auto. }
  destruct (each_invariant ge e i count fixed_body I Bound Registers Step le m Initial)
    as [le' [m' [Run [K [Index [RegFrame [D [T [P [U [W [Frame WFrame]]]]]]]]]]]].
  exists le', m'. split; [exact Run|]. split; [exact D|]. split; [exact T|]. split.
  - assert (E : words (fixed_assignment source desired original count) =
      words (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else original x)).
    { apply words_ext. intro x. unfold fixed_assignment.
      assert (B : Nat.ltb (nat_of_ord x) count = true).
      { apply Nat.ltb_lt. exact (elimT ltP (ltn_ord x)). }
      now rewrite B. }
    now rewrite <- E.
  - rewrite -> List.firstn_all2 in U by (rewrite words_length; lia).
    split; [exact U|]. split; [exact RegFrame|]. split; assumption.
Qed.

Print Assumptions fixed_pass_correct.
