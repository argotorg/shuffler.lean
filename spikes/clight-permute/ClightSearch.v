(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.
Require Import Permute ClightEval ClightEvalProofs ClightMemory ClightScalar
  ClightChoose ClightLoop ModelArrays.
Import ListNotations.

Definition search_scan : statement :=
  loop (Permute.lt (reg j) (reg n)) (seq [
    when (Permute.eq (cell used (reg j)) (lit 0))
      (when (Permute.eq (cell data (reg i)) (cell target (reg j))) Sbreak);
    inc j
  ]).

Lemma expression_nat_equal ge le m a b x y :
  typeof a = u32 -> typeof b = u32 ->
  uint (Z.of_nat x) -> uint (Z.of_nat y) ->
  expression ge le m a = Some (Vint (Int.repr (Z.of_nat x))) ->
  expression ge le m b = Some (Vint (Int.repr (Z.of_nat y))) ->
  expression ge le m (Permute.eq a b) = Some (Val.of_bool (Nat.eqb x y)).
Proof.
  intros A B X Y Ex Ey.
  pose proof (expression_compare ge le m Ceq a b _ _ A B X Y Ex Ey) as C.
  unfold zcompare in C.
  destruct (Coqlib.zeq (Z.of_nat x) (Z.of_nat y));
    destruct (Nat.eqb x y) eqn:E; try exact C;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; exfalso; lia.
Qed.

Lemma increment_search ge e le m k :
  (k <= 1024)%coq_nat ->
  PTree.get j le = Some (Vint (Int.repr (Z.of_nat k))) ->
  exec_stmt function_entry2 ge e le m (inc j) E0
    (PTree.set j (Vint (Int.repr (Z.of_nat (S k)))) le) m Out_normal.
Proof.
  intros K J. apply exec_Sset. apply expression_sound.
  replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
  eapply expression_add; eauto; try reflexivity;
    unfold uint; change Int.max_unsigned with 4294967295%Z; lia.
Qed.

Theorem search_scan_found ge e m count bd bt bu
    (source desired flags : 'I_count -> nat) (origin found : 'I_count) :
  (count <= 1024)%coq_nat ->
  uint (Z.of_nat (source origin)) ->
  (forall x, uint (Z.of_nat (desired x))) ->
  (forall x, uint (Z.of_nat (flags x))) ->
  array_at m bd (words source) -> array_at m bt (words desired) ->
  array_at m bu (words flags) ->
  flags found = 0%nat -> desired found = source origin ->
  forall start le,
  (start <= nat_of_ord found)%coq_nat ->
  (forall x, (start <= nat_of_ord x)%coq_nat ->
    (nat_of_ord x < nat_of_ord found)%coq_nat ->
    flags x <> 0%nat \/ desired x <> source origin) ->
  PTree.get data le = Some (Vptr bd Ptrofs.zero) ->
  PTree.get target le = Some (Vptr bt Ptrofs.zero) ->
  PTree.get used le = Some (Vptr bu Ptrofs.zero) ->
  PTree.get n le = Some (Vint (Int.repr (Z.of_nat count))) ->
  PTree.get i le = Some (Vint (Int.repr (Z.of_nat (nat_of_ord origin)))) ->
  PTree.get j le = Some (Vint (Int.repr (Z.of_nat start))) ->
  exec_stmt function_entry2 ge e le m search_scan E0
    (PTree.set j (Vint (Int.repr (Z.of_nat (nat_of_ord found)))) le) m Out_normal.
Proof.
  intros Bound SourceUInt TargetUInt FlagsUInt Source Target Flags Free Match start.
  remember (nat_of_ord found - start)%coq_nat as remaining eqn:Remaining.
  revert start Remaining.
  induction remaining as [|remaining IH]; intros start Remaining le Before Minimal
    Data TargetBase Used N Origin J.
  all: assert (FoundBound : (nat_of_ord found < count)%coq_nat)
    by exact (elimT ltP (ltn_ord found)).
  all: assert (StartBound : (start < count)%coq_nat) by lia.
  all: pose current : 'I_count := Ordinal (introT ltP StartBound).
  all: assert (K : (0 <= Z.of_nat start <= 2048)%Z) by lia.
  all: assert (OK : (0 <= Z.of_nat (nat_of_ord origin) <= 2048)%Z)
    by (have H := elimT ltP (ltn_ord origin); lia).
  all: assert (U0 : uint 0) by (unfold uint; change (0 <= 0 <= 4294967295)%Z; lia).
  all: assert (Guard : expression ge le m (Permute.lt (reg j) (reg n)) = Some Vtrue) by (
    rewrite -> (counted_test ge le m j (Z.of_nat count) (Z.of_nat start))
      by (try assumption; lia);
    destruct (Coqlib.zlt (Z.of_nat start) (Z.of_nat count)); [reflexivity|lia]).
  all: assert (RSource : expression ge le m (cell data (reg i)) =
    Some (Vint (Int.repr (Z.of_nat (source origin))))).
  all: try solve [eapply cell_expression; eauto; exact (proj1 (Source _ _ (words_nth_error source origin)))].
  all: assert (RTarget : expression ge le m (cell target (reg j)) =
    Some (Vint (Int.repr (Z.of_nat (desired current))))).
  all: try solve [eapply cell_expression; eauto; exact (proj1 (Target _ _ (words_nth_error desired current)))].
  all: assert (RFlags : expression ge le m (cell used (reg j)) =
    Some (Vint (Int.repr (Z.of_nat (flags current))))).
  all: try solve [eapply cell_expression; eauto; exact (proj1 (Flags _ _ (words_nth_error flags current)))].
  all: assert (UsedZero : expression ge le m (Permute.eq (cell used (reg j)) (lit 0)) =
    Some (Val.of_bool (Nat.eqb (flags current) 0))).
  all: try solve [eapply expression_nat_equal; eauto; reflexivity].
  all: assert (Matches : expression ge le m
    (Permute.eq (cell data (reg i)) (cell target (reg j))) =
    Some (Val.of_bool (Nat.eqb (source origin) (desired current)))).
  all: try solve [eapply expression_nat_equal; eauto; reflexivity].
  - assert (Start : start = nat_of_ord found) by lia.
    assert (Current : current = found) by (apply val_inj; exact Start).
    rewrite -> Current, Free in UsedZero.
    rewrite -> Current, Match, Nat.eqb_refl in Matches.
    rewrite <- Start. rewrite (PTree.gsident j le J).
    unfold search_scan, loop. eapply exec_Sloop_stop1 with (out' := Out_break).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
      * eapply exec_if_test with (b := true); [exact Guard|reflexivity|constructor].
      * unfold seq. cbn [fold_right]. eapply exec_Sseq_2; [|discriminate].
        unfold when. eapply exec_if_test with (b := true); [exact UsedZero|reflexivity|].
        eapply exec_if_test with (b := true); [exact Matches|reflexivity|constructor].
    + constructor.
  - assert (BeforeFound : (start < nat_of_ord found)%coq_nat) by lia.
    assert (Miss : flags current <> 0%nat \/ desired current <> source origin).
    { apply Minimal; [reflexivity|exact BeforeFound]. }
    assert (MissWhen : exec_stmt function_entry2 ge e le m
      (when (Permute.eq (cell used (reg j)) (lit 0))
        (when (Permute.eq (cell data (reg i)) (cell target (reg j))) Sbreak))
      E0 le m Out_normal).
    { destruct (Nat.eqb (flags current) 0) eqn:F.
      - destruct (Nat.eqb (source origin) (desired current)) eqn:M.
        + apply Nat.eqb_eq in F, M. destruct Miss; congruence.
        + unfold when. eapply exec_if_test with (b := true); [exact UsedZero|reflexivity|].
          eapply exec_if_test with (b := false); [exact Matches|reflexivity|constructor].
      - unfold when at 1. eapply exec_if_test with (b := false); [exact UsedZero|reflexivity|constructor]. }
    set (le1 := PTree.set j (Vint (Int.repr (Z.of_nat (S start)))) le).
    assert (Body : exec_stmt function_entry2 ge e le m
      (Ssequence (Sifthenelse (Permute.lt (reg j) (reg n)) Sskip Sbreak)
        (seq [when (Permute.eq (cell used (reg j)) (lit 0))
          (when (Permute.eq (cell data (reg i)) (cell target (reg j))) Sbreak); inc j]))
      E0 le1 m Out_normal).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
      - eapply exec_if_test with (b := true); [exact Guard|reflexivity|constructor].
      - unfold seq. cbn [fold_right].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m); [exact MissWhen|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|constructor].
        eapply increment_search with (k := start); [lia|exact J]. }
    assert (Continue : exec_stmt function_entry2 ge e le1 m search_scan E0
      (PTree.set j (Vint (Int.repr (Z.of_nat (nat_of_ord found)))) le1) m Out_normal).
    { apply (IH (S start)); try lia.
      - intros x Lower Upper. apply Minimal; [lia|exact Upper].
      - unfold le1. rewrite -> PTree.gso by discriminate. exact Data.
      - unfold le1. rewrite -> PTree.gso by discriminate. exact TargetBase.
      - unfold le1. rewrite -> PTree.gso by discriminate. exact Used.
      - unfold le1. rewrite -> PTree.gso by discriminate. exact N.
      - unfold le1. rewrite -> PTree.gso by discriminate. exact Origin.
      - unfold le1. apply PTree.gss. }
    unfold le1 in Continue. rewrite PTree.set2 in Continue.
    unfold search_scan, loop in *.
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0);
      [exact Body|constructor|constructor|exact Continue].
Qed.

Print Assumptions search_scan_found.
