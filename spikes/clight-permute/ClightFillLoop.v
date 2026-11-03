(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar
  ClightChoose ClightLoop ClightNormalize ClightFill ModelArrays SolcModel.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma skipn_at {A} (xs : list A) k x :
  List.nth_error xs k = Some x ->
  List.skipn k xs = x :: List.skipn (S k) xs.
Proof.
revert k. induction xs as [|a rest IH]; intros [|k] H; cbn in *; try discriminate.
- inversion H; reflexivity.
- apply IH; exact H.
Qed.

Lemma ordinal_enum_step count (origin : 'I_count) :
  List.skipn (val origin) (enum 'I_count) =
    origin :: List.skipn (S (val origin)) (enum 'I_count).
Proof.
apply skipn_at.
have N : List.nth (val origin) (enum 'I_count) origin = origin.
{ by rewrite nth_compat nth_ord_enum. }
rewrite -{2}N. apply List.nth_error_nth'.
change (val origin < size (enum 'I_count))%coq_nat.
rewrite size_enum_ord. exact (elimT ltP (ltn_ord origin)).
Qed.

Lemma ordinal_enum_end count : List.skipn count (enum 'I_count) = [::].
Proof.
apply List.skipn_all2. change (size (enum 'I_count) <= count)%coq_nat.
rewrite size_enum_ord. reflexivity.
Qed.

Lemma fill_body_equal ge e le memory count bd bt
    (source desired : 'I_count -> nat) (origin : 'I_count) :
  PTree.get Permute.data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get Permute.target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get Permute.i le = Some (Vint (Int.repr (Z.of_nat (val origin)))) ->
  (count <= 1024)%coq_nat ->
  uint (Z.of_nat (source origin)) -> uint (Z.of_nat (desired origin)) ->
  source origin = desired origin ->
  array_at memory bd (words source) -> array_at memory bt (words desired) ->
  exec_stmt function_entry2 ge e le memory fill_body E0 le memory Out_normal.
Proof.
intros Data Target Index Bound SourceUInt TargetUInt Same Source TargetArray.
have K : (0 <= Z.of_nat (val origin) <= 2048)%Z.
{ have H : (val origin < count)%coq_nat := elimT ltP (ltn_ord origin). lia. }
have ReadSource : expression ge le memory (cell data (reg i)) =
  Some (Vint (Int.repr (Z.of_nat (source origin)))).
{ eapply cell_expression; eauto. exact (proj1 (Source _ _ (words_nth_error source origin))). }
have ReadTarget : expression ge le memory (cell target (reg i)) =
  Some (Vint (Int.repr (Z.of_nat (desired origin)))).
{ eapply cell_expression; eauto. exact (proj1 (TargetArray _ _ (words_nth_error desired origin))). }
have Compare := expression_compare ge le memory Cne (cell data (reg i)) (cell target (reg i))
  _ _ Logic.eq_refl Logic.eq_refl SourceUInt TargetUInt ReadSource ReadTarget.
have Test : expression ge le memory (ne (cell data (reg i)) (cell target (reg i))) = Some Vfalse.
{ unfold zcompare in Compare.
  destruct (Coqlib.zeq (Z.of_nat (source origin)) (Z.of_nat (desired origin)));
    [exact Compare|congruence]. }
unfold fill_body, when. eapply exec_if_test with (b := false);
  [exact Test|reflexivity|constructor].
Qed.

(* The raw model gives the rest of the greedy scan. Its successful result
   ensures that each required search finds a destination. The invariant
   also records all current array contents and register values. *)
Theorem fill_pass_correct ge e le memory count bd bt bp bu
    (source desired : 'I_count -> nat) (initial final : 'I_count -> 'I_count)
    (reserved : {set 'I_count}) :
  bd <> bp -> bd <> bu -> bt <> bp -> bt <> bu -> bp <> bu ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat count))) ->
  (count <= 1024)%coq_nat ->
  (forall x, uint (Z.of_nat (source x))) ->
  (forall x, uint (Z.of_nat (desired x))) ->
  raw_fill source desired (enum 'I_count) initial reserved = Some final ->
  array_at memory bd (words source) -> array_at memory bt (words desired) ->
  array_at memory bp (words (fun x => val (initial x))) ->
  array_at memory bu (words (used_flags reserved)) ->
  exists le' memory' (reserved' : {set 'I_count}),
    exec_stmt function_entry2 ge e le memory (each i fill_body) E0 le' memory' Out_normal /\
    array_at memory' bd (words source) /\ array_at memory' bt (words desired) /\
    array_at memory' bp (words (fun x => val (final x))) /\
    array_at memory' bu (words (used_flags reserved')) /\
    (forall id, id <> i -> id <> j -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at memory other xs -> array_at memory' other xs) /\
    (forall other capacity, writable_array memory other capacity -> writable_array memory' other capacity).
Proof.
intros DP DU TP TU PU Data Target Perm Used N Bound SourceUInt TargetUInt Model
  Source TargetArray Assignment Flags.
set (I := fun k env mem =>
  (k <= count)%coq_nat /\
  PTree.get i env = Some (Vint (Int.repr (Z.of_nat k))) /\
  (forall id, id <> i -> id <> j -> PTree.get id env = PTree.get id le) /\
  exists assignment flags,
    raw_fill source desired (List.skipn k (enum 'I_count)) assignment flags = Some final /\
    array_at mem bd (words source) /\ array_at mem bt (words desired) /\
    array_at mem bp (words (fun x => val (assignment x))) /\
    array_at mem bu (words (used_flags flags)) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at memory other xs -> array_at mem other xs) /\
    (forall other capacity, writable_array memory other capacity -> writable_array mem other capacity)).
have Registers : forall k env mem, I k env mem ->
  PTree.get i env = Some (Vint (Int.repr (Z.of_nat k))) /\
  PTree.get n env = Some (Vint (Int.repr (Z.of_nat count))).
{ intros k env mem [K [Index [Frame Rest]]]. split; [exact Index|].
  rewrite Frame; try discriminate. exact N. }
have Step : forall k env mem, (k < count)%coq_nat -> I k env mem ->
  exists env' mem', exec_stmt function_entry2 ge e env mem
    (Permute.seq [:: fill_body; inc i]) E0 env' mem' Out_normal /\ I (S k) env' mem'.
{ intros k env mem K [KB [Index [EnvFrame [assignment [flags
    [Remaining [D [T [P [U [Frame WFrame]]]]]]]]]]].
  pose origin : 'I_count := Ordinal (introT ltP K).
  change k with (val origin) in Remaining.
  rewrite ordinal_enum_step /= /fixed_values inE in Remaining.
  case Equal: (source origin == desired origin) in Remaining.
  - have Same : source origin = desired origin := elimT eqP Equal.
    have Body := @fill_body_equal ge e env mem count bd bt source desired origin
      ltac:(rewrite EnvFrame; try discriminate; exact Data)
      ltac:(rewrite EnvFrame; try discriminate; exact Target)
      Index Bound (SourceUInt origin) (TargetUInt origin) Same D T.
    exists (PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) env), mem. split.
    + cbn [Permute.seq fold_right].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Body|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply increment_index with (k := k); [lia|exact Index].
      * constructor.
    + unfold I. split; [lia|]. split; [apply PTree.gss|]. split.
      * intros id DifferentI DifferentJ. rewrite PTree.gso; [apply EnvFrame|]; assumption.
      * exists assignment, flags. split; [exact Remaining|].
        split; [exact D|]. split; [exact T|]. split; [exact P|].
        split; [exact U|]. split; assumption.
  - have Different : source origin <> desired origin.
    { intro H. rewrite H eqxx in Equal. discriminate. }
    case Choice: (first_free desired (source origin) flags (enum 'I_count))=> [chosen|] in Remaining;
      last discriminate.
    destruct (fill_body_found ge e env mem count bd bt bp bu source desired assignment
      flags origin chosen DP DU TP TU PU
      ltac:(rewrite EnvFrame; try discriminate; exact Data)
      ltac:(rewrite EnvFrame; try discriminate; exact Target)
      ltac:(rewrite EnvFrame; try discriminate; exact Perm)
      ltac:(rewrite EnvFrame; try discriminate; exact Used)
      ltac:(rewrite EnvFrame; try discriminate; exact N)
      Index Bound SourceUInt TargetUInt Different Choice D T P U)
      as [mem1 [Body [D1 [T1 [P1 [U1 [Frame1 WFrame1]]]]]]].
    set (env1 := PTree.set j (Vint (Int.repr (Z.of_nat (val chosen)))) env) in *.
    have Index1 : PTree.get i env1 = Some (Vint (Int.repr (Z.of_nat k))).
    { unfold env1. rewrite PTree.gso; [exact Index|discriminate]. }
    exists (PTree.set i (Vint (Int.repr (Z.of_nat (S k)))) env1), mem1. split.
    + cbn [Permute.seq fold_right].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Body|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply increment_index with (k := k); [lia|exact Index1].
      * constructor.
    + unfold I. split; [lia|]. split; [apply PTree.gss|]. split.
      * intros id DifferentI DifferentJ. unfold env1.
        rewrite !PTree.gso; [apply EnvFrame| |]; assumption.
      * exists (write_index assignment origin chosen), (chosen |: flags).
        split; [exact Remaining|]. split; [exact D1|]. split; [exact T1|].
        split; [exact P1|]. split; [exact U1|]. split.
        -- intros other xs OP OU A. apply Frame1; [exact OP|exact OU|].
           apply Frame; assumption.
        -- intros other capacity A. apply WFrame1, WFrame, A. }
have Initial : I 0%nat (PTree.set i (Vint (Int.repr 0)) le) memory.
{ unfold I. split; [lia|]. split; [apply PTree.gss|]. split.
  - intros id DifferentI DifferentJ. now rewrite PTree.gso.
  - exists initial, reserved. split; [exact Model|].
    split; [exact Source|]. split; [exact TargetArray|]. split; [exact Assignment|].
    split; [exact Flags|]. split; auto. }
destruct (each_invariant ge e i count fill_body I Bound Registers Step le memory Initial)
  as [le' [memory' [Run [K [Index [RegFrame [assignment [flags
    [Remaining [D [T [P [U [Frame WFrame]]]]]]]]]]]]]].
rewrite ordinal_enum_end /= in Remaining. inversion Remaining; subst assignment.
exists le', memory', flags. split; [exact Run|]. split; [exact D|]. split; [exact T|].
split; [exact P|]. split; [exact U|]. split; [exact RegFrame|]. split; assumption.
Qed.

Print Assumptions fill_pass_correct.
