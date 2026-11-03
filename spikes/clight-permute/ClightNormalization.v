(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightMemory ClightScalar ClightNormalize
  ClightSearch ClightFill ClightFillLoop ModelArrays SolcModel ModelProofs.
Import ListNotations.

Lemma nat_eqb_mathcomp x y : Nat.eqb x y = (x == y).
Proof.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. now rewrite eqxx.
  - apply Nat.eqb_neq in E. destruct (x == y) eqn:F; [|reflexivity].
    have Eq : x = y := elimT eqP F. contradiction.
Qed.

Lemma normalization_ast : Permute.normalize =
  Permute.seq [each i fixed_body; each i fill_body].
Proof. reflexivity. Qed.

Lemma fixed_initial_words count (source desired : 'I_count -> nat) (p : 'S_count) :
  words (fun x => if Nat.eqb (source x) (desired x) then nat_of_ord x else nat_of_ord (p x)) =
  words (fun x => nat_of_ord (if x \in fixed_values source desired then x else p x)).
Proof.
  apply words_ext. intro x. unfold fixed_values. rewrite inE nat_eqb_mathcomp.
  destruct (source x == desired x); reflexivity.
Qed.

Lemma fixed_flag_words count (source desired : 'I_count -> nat) :
  words (fixed_flags source desired) = words (used_flags (fixed_values source desired)).
Proof.
  apply words_ext. intro x. unfold fixed_flags, used_flags, fixed_values.
  rewrite inE nat_eqb_mathcomp. reflexivity.
Qed.

Theorem normalize_correct ge e le m count bd bt bp bu
    (source : 'I_count -> nat) (p : 'S_count) :
  bd <> bp -> bd <> bu -> bt <> bp -> bt <> bu -> bp <> bu ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get permutation le = Some (Vptr bp Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat count))) ->
  (count <= 1024)%coq_nat ->
  (forall x, uint (Z.of_nat (source x))) ->
  array_at m bd (words source) ->
  array_at m bt (words (target_of source p)) ->
  array_at m bp (words (fun x => nat_of_ord (p x))) ->
  writable_array m bu count ->
  exists q le' m',
    SolcModel.normalize source p = Some q /\
    exec_stmt function_entry2 ge e le m Permute.normalize E0 le' m' Out_normal /\
    array_at m' bd (words source) /\
    array_at m' bp (words (fun x => nat_of_ord (q x))) /\
    (forall id, id <> i -> id <> j -> PTree.get id le' = PTree.get id le) /\
    (forall other xs, other <> bp -> other <> bu ->
      array_at m other xs -> array_at m' other xs) /\
    (forall other capacity, writable_array m other capacity -> writable_array m' other capacity).
Proof.
  intros DP DU TP TU PU Data Target Perm Used N Bound Values Source TargetArray Assignment Writable.
  set (desired := target_of source p).
  set (good := fixed_values source desired).
  set (initial := fun x : 'I_count => if x \in good then x else p x).
  assert (DesiredUInt : forall x, uint (Z.of_nat (desired x))).
  { intro x. apply Values. }
  destruct (raw_normalize_complete source p)
    as [q [result [Normalized [Raw [Result [Compatible Fixed]]]]]].
  change (raw_fill source desired (enum 'I_count) initial good = Some result) in Raw.
  destruct (fixed_pass_correct ge e le m count bd bt bp bu source desired
    (fun x => nat_of_ord (p x)) DP DU TP TU PU Data Target Perm Used N Bound Values
    DesiredUInt Source TargetArray Assignment Writable)
    as [le1 [m1 [Fix [D1 [T1 [P1 [U1 [Reg1 [Frame1 WFrame1]]]]]]]]].
  rewrite fixed_initial_words in P1. rewrite fixed_flag_words in U1.
  change (array_at m1 bp (words (fun x => nat_of_ord (initial x)))) in P1.
  change (array_at m1 bu (words (used_flags good))) in U1.
  destruct (@fill_pass_correct ge e le1 m1 count bd bt bp bu source desired initial result good
    DP DU TP TU PU
    ltac:(rewrite -> Reg1 by discriminate; exact Data)
    ltac:(rewrite -> Reg1 by discriminate; exact Target)
    ltac:(rewrite -> Reg1 by discriminate; exact Perm)
    ltac:(rewrite -> Reg1 by discriminate; exact Used)
    ltac:(rewrite -> Reg1 by discriminate; exact N)
    Bound Values DesiredUInt Raw D1 T1 P1 U1)
    as [le2 [m2 [reserved [Fill [D2 [T2 [P2 [U2 [Reg2 [Frame2 WFrame2]]]]]]]]]].
  exists q, le2, m2. split; [exact Normalized|]. split.
  - rewrite normalization_ast. unfold Permute.seq. cbn [fold_right].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Fix|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Fill|constructor].
  - split; [exact D2|]. split.
    + assert (E : words (fun x => nat_of_ord (result x)) = words (fun x => nat_of_ord (q x))).
      { apply words_ext. intro x. now rewrite Result. }
      now rewrite <- E.
    + split.
      * intros id DI DJ. rewrite -> Reg2 by assumption. now apply Reg1.
      * split.
        -- intros other xs OP OU Other. apply Frame2; [exact OP|exact OU|].
           apply Frame1; assumption.
        -- intros other capacity Other. apply WFrame2, WFrame1, Other.
Qed.

Print Assumptions normalize_correct.
