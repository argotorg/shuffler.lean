(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes
  Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Proofs.
Require Import Permute SolcModel ModelProofs ModelArrays ChooseModel
  ClightMemory ClightScalar ClightChoose ClightExchange ClightExchangeSuccess.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Ltac nat_lia := unfold addn, muln, subn in *; lia.

Definition main_loop :=
  Sloop (Permute.seq [:: Permute.choose_position; Permute.exchange]) Sskip.

Record loop_registers le count bd bp bt bo : Prop := {
  loop_n : PTree.get Permute.n le = Some (Vint (Int.repr (Z.of_nat count)));
  loop_top : PTree.get Permute.top le = Some (Vint (Int.repr (Z.of_nat count.-1)));
  loop_data : PTree.get Permute.data le = Some (Vptr bd Ptrofs.zero);
  loop_permutation : PTree.get Permute.permutation le = Some (Vptr bp Ptrofs.zero);
  loop_trace : PTree.get Permute.trace le = Some (Vptr bt Ptrofs.zero);
  loop_out : PTree.get Permute.out le = Some (Vptr bo Ptrofs.zero)
}.

Lemma loop_registers_frame le le' count bd bp bt bo :
  loop_registers le count bd bp bt bo ->
  (forall id, id <> Permute.pos -> id <> Permute.tmp -> id <> Permute.depth ->
    PTree.get id le' = PTree.get id le) ->
  loop_registers le' count bd bp bt bo.
Proof.
intros R F. destruct R. constructor; rewrite F; try discriminate; assumption.
Qed.

Definition trace_words (depths : list nat) := List.map Z.of_nat depths.

Lemma trace_words_length depths : List.length (trace_words depths) = List.length depths.
Proof. exact: List.length_map. Qed.

Lemma trace_words_append depths depth :
  trace_words (depths ++ [:: depth]) = trace_words depths ++ [:: Z.of_nat depth].
Proof. exact: List.map_app. Qed.

Section Main.
Variable d : nat.
Variables bd bp bt bo : block.
Hypotheses (DP : bd <> bp) (DT : bd <> bt) (DO : bd <> bo)
  (PT : bp <> bt) (PO : bp <> bo) (TO : bt <> bo).
Hypothesis Size : (d.+1 <= 1024)%coq_nat.

Record loop_arrays memory (s : 'I_d.+1 -> nat) (p : 'S_d.+1) depths : Prop := {
  loop_stack : array_at memory bd (words s);
  loop_destinations : array_at memory bp (words (fun i => val (p i)));
  loop_depths : array_at memory bt (trace_words depths);
  loop_output : array_at memory bo [:: Z.of_nat (List.length depths); 0%Z; 0%Z];
  loop_capacity : writable_array memory bt (2 * d.+1)
}.

Definition result_arrays (result : SolcResult nat d.+1) memory outcome :=
  match result with
  | SolcDone s p depths =>
      outcome = Out_return (Some (Vint Int.zero, Permute.u32)) /\
      array_at memory bd (words s) /\
      array_at memory bp (words (fun i => val (p i))) /\
      array_at memory bt (trace_words depths) /\
      array_at memory bo [:: Z.of_nat (List.length depths); 0%Z; 0%Z]
  | SolcBlocked s p depths position excess =>
      outcome = Out_return (Some (Vint (Int.repr 1), Permute.u32)) /\
      array_at memory bd (words s) /\
      array_at memory bp (words (fun i => val (p i))) /\
      array_at memory bt (trace_words depths) /\
      array_at memory bo
        [:: Z.of_nat (List.length depths); Z.of_nat (val position); Z.of_nat excess]
  | SolcExhausted => False
  end.

Definition main_frame memory memory' := forall other xs,
  other <> bd -> other <> bp -> other <> bt -> other <> bo ->
  array_at memory other xs -> array_at memory' other xs.

Theorem main_loop_refines ge e fuel s p depths le memory :
  (Legacy.Permute.rank p ord_max < fuel)%coq_nat ->
  (List.length depths + fuel <= 2 * d.+1)%coq_nat ->
  (forall i, uint (Z.of_nat (s i))) ->
  loop_registers le d.+1 bd bp bt bo ->
  loop_arrays memory s p depths ->
  exists le' memory' outcome,
    exec_stmt function_entry2 ge e le memory main_loop E0 le' memory' outcome /\
    result_arrays (@solc_run _ d fuel s p depths) memory' outcome /\
    main_frame memory memory'.
Proof.
revert s p depths le memory.
induction fuel as [|fuel IH]; intros s p depths le memory Rank Capacity Values Registers Arrays.
- nat_lia.
- destruct Arrays as [DataArray PermArray TraceArray OutArray Writable].
  have PermValues := permutation_words_uint p Size.
  have Choose := choose_position_array ge e le memory bp
    (words (fun i => val (p i))) d PermArray
    ltac:(rewrite words_length; nat_lia) PermValues
    (loop_permutation Registers) (loop_top Registers).
  case Choice: (Legacy.Permute.choose p ord_max)=> [position|].
  + have Selected := @choose_result_some d p (words (fun i => val (p i)))
      (fun i => words_nth (fun j => val (p j)) i) position Choice.
    rewrite Selected /= in Choose.
    set (le1 := PTree.set Permute.pos
      (Vint (Int.repr (Z.of_nat (val position)))) le) in *.
    have Registers1 : loop_registers le1 d.+1 bd bp bt bo.
    { eapply loop_registers_frame; [exact Registers|].
      intros id P T D. unfold le1. now rewrite PTree.gso. }
    have Position : PTree.get Permute.pos le1 =
      Some (Vint (Int.repr (Z.of_nat (val position)))).
    { unfold le1. apply PTree.gss. }
    have PositionBound : (val position < d)%coq_nat.
    { have H := chosen_depth Choice.
      rewrite /Legacy.Permute.depth subn_gt0 in H. exact (elimT ltP H). }
    have NextRank : (Legacy.Permute.rank
      (Legacy.Permute.exchange p ord_max position) ord_max < fuel)%coq_nat.
    { have H := choose_rank Choice. nat_lia. }
    have WordPosition := words_nth_error s position.
    have WordTop := words_nth_error s (ord_max : 'I_d.+1).
    have PermPosition := words_nth_error (fun i => val (p i)) position.
    have PermTop := words_nth_error (fun i => val (p i)) (ord_max : 'I_d.+1).
    cbn [val] in WordTop, PermTop.
    case Equal: (s ord_max == s position).
    * have EqualValue : s ord_max = s position := elimT eqP Equal.
      rewrite EqualValue in WordTop.
      destruct (equal_values_exchange ge e le1 memory bd bp
        (words s) (words (fun i => val (p i))) (val position) d
        (Z.of_nat (s position)) (Z.of_nat (val (p position)))
        (Z.of_nat (val (p ord_max))) DP
        (loop_data Registers1) (loop_permutation Registers1) Position
        (loop_top Registers1) ltac:(rewrite words_length; exact Size)
        ltac:(rewrite words_length; exact Size)
        WordPosition WordTop PermPosition PermTop DataArray PermArray)
        as [memory1 [Exchange [Data1 [Perm1 [Frame1 Writable1]]]]].
      rewrite words_permutation_swap in Perm1.
      set (le2 := PTree.set Permute.tmp
        (Vint (Int.repr (Z.of_nat (val (p position))))) le1) in *.
      have Registers2 : loop_registers le2 d.+1 bd bp bt bo.
      { eapply loop_registers_frame; [exact Registers1|].
        intros id P T D. unfold le2. now rewrite PTree.gso. }
      have Arrays1 : loop_arrays memory1 s
        (Legacy.Permute.exchange p ord_max position) depths.
      { constructor; try assumption.
        - apply Frame1; [congruence|exact TraceArray].
        - apply Frame1; [congruence|exact OutArray].
        - apply Writable1; exact Writable. }
      have NextCapacity : (List.length depths + fuel <= 2 * d.+1)%coq_nat.
      { eapply Nat.le_trans; [|exact Capacity].
        apply Nat.add_le_mono_l. apply Nat.le_succ_diag_r. }
      destruct (IH s (Legacy.Permute.exchange p ord_max position) depths le2 memory1
        NextRank NextCapacity Values Registers2 Arrays1)
        as [le' [memory' [outcome [Run [Result Frame]]]]].
      exists le', memory', outcome. split.
      { unfold main_loop in *. change E0 with (E0 ** E0 ** E0).
        eapply exec_Sloop_loop; [|constructor|constructor|exact Run].
        cbn [Permute.seq fold_right]. change E0 with (E0 ** E0).
        eapply exec_Sseq_1; [exact Choose|].
        change E0 with (E0 ** E0). eapply exec_Sseq_1; [exact Exchange|constructor]. }
      split.
      { cbn [solc_run]. rewrite Choice Equal. exact Result. }
      intros other xs BData BPerm BTrace BOut A.
      apply Frame; try assumption. apply Frame1; assumption.
    * have Different : Z.of_nat (s position) <> Z.of_nat (s ord_max).
      { intro H. apply Nat2Z.inj in H. rewrite H eqxx in Equal. discriminate. }
      case Near: (Legacy.Permute.depth position <= 16)%N.
      -- have NearNat : (d <= val position + 16)%coq_nat.
         { have H := elimT leP Near.
           change ((d - val position)%coq_nat <= 16)%coq_nat in H.
           clear -H. nat_lia. }
         have TraceCapacity : (List.length (trace_words depths) < 2 * List.length (words s))%coq_nat.
         { rewrite trace_words_length words_length. clear -Capacity. nat_lia. }
         have OutArray' : array_at memory bo
           [:: Z.of_nat (List.length (trace_words depths)); 0%Z; 0%Z].
         { by rewrite trace_words_length. }
         have Writable' : writable_array memory bt (2 * List.length (words s)).
         { by rewrite words_length. }
         have SizeRegister : PTree.get Permute.n le1 =
           Some (Vint (Int.repr (Z.of_nat (List.length (words s))))).
         { rewrite words_length. exact (loop_n Registers1). }
         destruct (successful_exchange ge e le1 memory bd bp bt bo
           (words s) (words (fun i => val (p i))) (trace_words depths)
           (val position) d (Z.of_nat (s position)) (Z.of_nat (s ord_max))
           (Z.of_nat (val (p position))) (Z.of_nat (val (p ord_max)))
           DP DT DO PT PO TO (loop_data Registers1) (loop_permutation Registers1)
           (loop_trace Registers1) (loop_out Registers1) SizeRegister Position
           (loop_top Registers1) ltac:(rewrite words_length; exact Size)
           ltac:(rewrite words_length; exact Size) WordPosition WordTop PermPosition PermTop
           (Values position) (Values ord_max) Different ltac:(nat_lia) TraceCapacity
           DataArray PermArray OutArray' TraceArray Writable')
           as [le2 [memory1 [Exchange [Data1 [Perm1 [Out1 [Trace1 [Writable1 [Regs1 Frame1]]]]]]]]].
         rewrite words_stack_swap in Data1.
         rewrite words_permutation_swap in Perm1.
         have DepthZ : Z.of_nat (Legacy.Permute.depth position) =
           (Z.of_nat d - Z.of_nat (val position))%Z.
         { change (Z.of_nat (d - val position)%coq_nat =
             (Z.of_nat d - Z.of_nat (val position))%Z).
           rewrite Nat2Z.inj_sub; nat_lia. }
         have Registers2 : loop_registers le2 d.+1 bd bp bt bo.
         { eapply loop_registers_frame; [exact Registers1|].
           intros id P T D. apply Regs1; assumption. }
         have Arrays1 : loop_arrays memory1 (Legacy.Permute.swap_stack s position)
           (Legacy.Permute.exchange p ord_max position)
           (depths ++ [:: Legacy.Permute.depth position]).
         { constructor; try assumption.
           - rewrite trace_words_append DepthZ. exact Trace1.
           - rewrite List.length_app /= Nat2Z.inj_add /=.
             rewrite trace_words_length in Out1. exact Out1.
           - rewrite words_length in Writable1. exact Writable1. }
         have Values1 : forall i, uint (Z.of_nat (Legacy.Permute.swap_stack s position i)).
         { intro i. apply Values. }
         destruct (IH (Legacy.Permute.swap_stack s position)
           (Legacy.Permute.exchange p ord_max position)
           (depths ++ [:: Legacy.Permute.depth position]) le2 memory1 NextRank
           ltac:(rewrite List.length_app /=; nat_lia) Values1 Registers2 Arrays1)
           as [le' [memory' [outcome [Run [Result Frame]]]]].
         exists le', memory', outcome. split.
         { unfold main_loop in *. change E0 with (E0 ** E0 ** E0).
           eapply exec_Sloop_loop; [|constructor|constructor|exact Run].
           cbn [Permute.seq fold_right]. change E0 with (E0 ** E0).
           eapply exec_Sseq_1; [exact Choose|].
           change E0 with (E0 ** E0). eapply exec_Sseq_1; [exact Exchange|constructor]. }
         split.
         { cbn [solc_run]. rewrite Choice Equal Near. exact Result. }
         intros other xs BData BPerm BTrace BOut A.
         apply Frame; try assumption. apply Frame1; assumption.
      -- have Far : (val position + 16 < d)%coq_nat.
         { have H : (16 < Legacy.Permute.depth position)%N by rewrite ltnNge Near.
           have H' := elimT ltP H.
           change (16 < (d - val position)%coq_nat)%coq_nat in H'. nat_lia. }
         destruct (blocked_exchange ge e le1 memory bd bo (words s) (val position) d
           (Z.of_nat (s position)) (Z.of_nat (s ord_max)) (Z.of_nat (List.length depths))
           0%Z 0%Z DO (loop_data Registers1) (loop_out Registers1) Position
           (loop_top Registers1) ltac:(rewrite words_length; exact Size) WordPosition WordTop
           (Values position) (Values ord_max) Different Far DataArray OutArray)
           as [memory1 [Exchange [Data1 [Out1 Frame1]]]].
         exists (PTree.set Permute.depth
           (Vint (Int.repr (Z.of_nat d - Z.of_nat (val position)))) le1), memory1,
           (Out_return (Some (Vint (Int.repr 1), Permute.u32))). split.
         { unfold main_loop. eapply exec_Sloop_stop1; [|constructor].
           cbn [Permute.seq fold_right]. change E0 with (E0 ** E0).
           eapply exec_Sseq_1; [exact Choose|].
           eapply exec_Sseq_2; [exact Exchange|discriminate]. }
         split.
         { cbn [solc_run]. rewrite Choice Equal Near. cbn [result_arrays].
           split; [reflexivity|]. split; [exact Data1|]. split.
           - apply Frame1; [exact PO|exact PermArray].
           - split; [apply Frame1; [exact TO|exact TraceArray]|].
             have Excess : Z.of_nat (Legacy.Permute.depth position - 16)%N =
               (Z.of_nat d - Z.of_nat (val position) - 16)%Z.
             { change (Z.of_nat ((d - val position) - 16)%coq_nat =
                 (Z.of_nat d - Z.of_nat (val position) - 16)%Z).
               rewrite !Nat2Z.inj_sub; nat_lia. }
             rewrite Excess. exact Out1. }
         intros other xs BData BPerm BTrace BOut A. apply Frame1; assumption.
  + have Finished := @choose_result_none d p (words (fun i => val (p i)))
      (fun i => words_nth (fun j => val (p j)) i) Choice.
    rewrite Finished in Choose.
    exists (PTree.set Permute.pos
      (Vint (Int.repr (fst (choose_result (words (fun i => val (p i))) d)))) le),
      memory, (Out_return (Some (Vint Int.zero, Permute.u32))). split.
    { unfold main_loop. eapply exec_Sloop_stop1; [|constructor].
      cbn [Permute.seq fold_right]. eapply exec_Sseq_2; [exact Choose|discriminate]. }
    split.
    { cbn [solc_run]. rewrite Choice. cbn [result_arrays].
      split; [reflexivity|]. split; [exact DataArray|].
      split; [exact PermArray|]. split; assumption. }
    intros other xs BData BPerm BTrace BOut A. exact A.
Qed.

Corollary main_loop_nonempty ge e s p le memory :
  (forall i, uint (Z.of_nat (s i))) ->
  loop_registers le d.+1 bd bp bt bo ->
  loop_arrays memory s p [::] ->
  exists le' memory' outcome,
    exec_stmt function_entry2 ge e le memory main_loop E0 le' memory' outcome /\
    result_arrays (solc_nonempty s p) memory' outcome /\
    main_frame memory memory'.
Proof.
intros Values Registers Arrays.
apply main_loop_refines; try assumption.
- exact: Nat.lt_succ_diag_r.
- have Bound := rank_bound p. exact (elimT leP Bound).
Qed.

Lemma result_arrays_return result memory outcome :
  result_arrays result memory outcome ->
  exists code, outcome = Out_return (Some (Vint (Int.repr code), Permute.u32)) /\
    (code = 0%Z \/ code = 1%Z).
Proof.
destruct result; cbn [result_arrays]; try contradiction;
  intros [Return Rest].
- exists 0%Z. split; [exact Return|now left].
- exists 1%Z. split; [exact Return|now right].
Qed.
End Main.

Print Assumptions main_loop_refines.
