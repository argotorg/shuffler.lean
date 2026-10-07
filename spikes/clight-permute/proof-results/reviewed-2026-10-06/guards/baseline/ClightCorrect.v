(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes
  Clight ClightBigstep.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute SolcModel ModelProofs ModelArrays ClightMemory
  ClightScalar ClightCall ClightMain ClightValidation ClightNormalization.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

(* Extend an ordinal permutation to natural indices for the validation
   loop. The extension is read only for indices below the array length. *)
Definition destination_at {d} (p : 'S_d.+1) k := val (p (inord k)).

Lemma destination_at_ordinal d (p : 'S_d.+1) (index : 'I_d.+1) :
  destination_at p (val index) = val (p index).
Proof. by rewrite /destination_at inord_val. Qed.

Lemma destination_at_bound d (p : 'S_d.+1) k :
  (destination_at p k < d.+1)%coq_nat.
Proof. exact (elimT ltP (ltn_ord (p (inord k)))). Qed.

Lemma destination_at_injective d (p : 'S_d.+1) k q :
  (k < d.+1)%coq_nat -> (q < d.+1)%coq_nat ->
  destination_at p k = destination_at p q -> k = q.
Proof.
move=> K Q E.
have H : p (inord k) = p (inord q) by apply: val_inj.
have H' := perm_inj H.
have H'' := congr1 val H'.
change (nat_of_ord (@inord d k) = nat_of_ord (@inord d q)) in H''.
by rewrite !inordK in H''; [exact H''|apply/ltP|apply/ltP].
Qed.



Lemma destination_at_words d (p : 'S_d.+1) k :
  (k < d.+1)%coq_nat ->
  List.nth_error (words (fun index => val (p index))) k =
    Some (Z.of_nat (destination_at p k)).
Proof.
move=> K.
have H := words_nth_error (fun index => val (p index)) (inord k).
change (List.nth_error (words (fun index => val (p index))) (nat_of_ord (@inord d k)) = Some (Z.of_nat (destination_at p k))) in H.
by rewrite inordK in H; [exact H|apply/ltP].
Qed.

Lemma target_array_from_destinations d (s : 'I_d.+1 -> nat) (p : 'S_d.+1)
    memory bt :
  writable_array memory bt d.+1 ->
  (forall k value, (k < d.+1)%coq_nat ->
    List.nth_error (words s) k = Some value ->
    Mem.load Mint32 memory bt (4 * Z.of_nat (destination_at p k)) =
      Some (Vint (Int.repr value))) ->
  array_at memory bt (words (target_of s p)).
Proof.
move=> Writable Loads k value At.
have K : (k < d.+1)%coq_nat.
{ have H := List.nth_error_Some (words (target_of s p)) k.
  rewrite words_length in H. apply H. by rewrite At. }
pose index : 'I_d.+1 := inord k.
have Index : val index = k by apply inordK; apply/ltP.
have Value := words_nth_error (target_of s p) index.
rewrite Index At in Value. inversion Value; subst value.
split; last exact (Writable k K).
have L := Loads (val (p^-1 index)) (Z.of_nat (s (p^-1 index)))
  (elimT ltP (ltn_ord (p^-1 index))) (words_nth_error s (p^-1 index)).
rewrite destination_at_ordinal permKV Index in L. exact L.
Qed.

Record input_registers le count bd bp bt bu btrace bo : Prop := {
  input_n : PTree.get Permute.n le = Some (Vint (Int.repr (Z.of_nat count)));
  input_data : PTree.get Permute.data le = Some (Vptr bd Ptrofs.zero);
  input_permutation : PTree.get Permute.permutation le = Some (Vptr bp Ptrofs.zero);
  input_target : PTree.get Permute.target le = Some (Vptr bt Ptrofs.zero);
  input_used : PTree.get Permute.used le = Some (Vptr bu Ptrofs.zero);
  input_trace : PTree.get Permute.trace le = Some (Vptr btrace Ptrofs.zero);
  input_out : PTree.get Permute.out le = Some (Vptr bo Ptrofs.zero)
}.

Lemma input_registers_frame le le' count bd bp bt bu btrace bo :
  input_registers le count bd bp bt bu btrace bo ->
  (forall id, id <> Permute.i -> id <> Permute.j ->
    PTree.get id le' = PTree.get id le) ->
  input_registers le' count bd bp bt bu btrace bo.
Proof.
intros R F. destruct R. constructor; rewrite F; try discriminate; assumption.
Qed.


Lemma check_input_model d ge e le memory bd bp bt bu btrace bo
    (source : 'I_d.+1 -> nat) (p : 'S_d.+1) :
  (d.+1 <= 1024)%coq_nat -> separate_arrays bd bp bt bu btrace bo ->
  input_registers le d.+1 bd bp bt bu btrace bo ->
  array_at memory bd (words source) ->
  array_at memory bp (words (fun x => val (p x))) ->
  writable_array memory bt d.+1 -> writable_array memory bu d.+1 ->
  exists le' memory',
    exec_stmt function_entry2 ge e le memory Permute.check_input E0 le' memory' Out_normal /\
    input_registers le' d.+1 bd bp bt bu btrace bo /\
    array_at memory' bd (words source) /\
    array_at memory' bp (words (fun x => val (p x))) /\
    array_at memory' bt (words (target_of source p)) /\
    writable_array memory' bu d.+1 /\
    (forall other xs, other <> bu -> other <> bt ->
      array_at memory other xs -> array_at memory' other xs) /\
    (forall other count, writable_array memory other count ->
      writable_array memory' other count).
Proof.
intros Size Separate Registers Data Permutation Target Used.
destruct (@check_input_valid d.+1 (words source) (words (fun x => val (p x)))
  (destination_at p) bd bp bt bu Size (words_length source)
  (@destination_at_words d p) (fun k _ => @destination_at_bound d p k)
  (@destination_at_injective d p)
  (separate_data_used Separate) (separate_data_target Separate)
  (separate_permutation_used Separate) (separate_permutation_target Separate)
  (separate_target_used Separate) ge e le memory
  (input_n Registers) (input_data Registers) (input_permutation Registers)
  (input_target Registers) (input_used Registers) Data Permutation Target Used)
  as [le' [memory' [Run [Arrays [RegisterFrame [Frame WritableFrame]]]]]].
destruct Arrays as [Data' Permutation' Target' Used' Loads Unused].
exists le', memory'. split; [exact Run|]. split.
- eapply input_registers_frame; eauto.
- split; [exact Data'|]. split; [exact Permutation'|]. split.
  + exact (@target_array_from_destinations d source p memory' bt Target' Loads).
  + split; [exact Used'|]. split; assumption.
Qed.

Lemma initial_loop_registers d le bd bp bt bu btrace bo :
  input_registers le d.+1 bd bp bt bu btrace bo ->
  loop_registers
    (PTree.set Permute.top (Vint (Int.repr (Z.of_nat d))) le)
    d.+1 bd bp btrace bo.
Proof.
intros Registers. destruct Registers. constructor.
- rewrite PTree.gso; [assumption|discriminate].
- apply PTree.gss.
- rewrite PTree.gso; [assumption|discriminate].
- rewrite PTree.gso; [assumption|discriminate].
- rewrite PTree.gso; [assumption|discriminate].
- rewrite PTree.gso; [assumption|discriminate].
Qed.

(* Defined execution of the complete Clight body. Only the input data and
   permutation need initialized contents. All other buffers need capacity.
   A valid finite permutation is the domain of this refinement theorem. *)
Theorem permute_body_correct d ge e le memory bd bp bt bu btrace bo
    (source : 'I_d.+1 -> nat) (p : 'S_d.+1) :
  (d.+1 <= 1024)%coq_nat -> separate_arrays bd bp bt bu btrace bo ->
  (forall x, uint (Z.of_nat (source x))) ->
  input_registers le d.+1 bd bp bt bu btrace bo ->
  array_at memory bd (words source) ->
  array_at memory bp (words (fun x => val (p x))) ->
  writable_array memory bt d.+1 -> writable_array memory bu d.+1 ->
  writable_array memory btrace (2 * d.+1) -> writable_array memory bo 3 ->
  exists le' memory' code result,
    exec_stmt function_entry2 ge e le memory (fn_body Permute.permute) E0 le' memory'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    solc_permute source p = Some result /\
    result_arrays bd bp btrace bo result memory'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    solc_result_spec source p result /\ (code = 0%Z \/ code = 1%Z).
Proof.
intros Size Separate Values Registers Data Permutation Target Used Trace Output.
destruct (initialize_output_frame ge le memory bo (input_out Registers) Output)
  as [ma [mb [m0 [S1 [S2 [S3 [Output0 [Frame0 Writable0]]]]]]]].
have Data0 : array_at m0 bd (words source).
{ apply Frame0; [exact (separate_data_out Separate)|exact Data]. }
have Permutation0 : array_at m0 bp (words (fun x => val (p x))).
{ apply Frame0; [exact (separate_permutation_out Separate)|exact Permutation]. }
destruct (@check_input_model d ge e le m0 bd bp bt bu btrace bo source p
  Size Separate Registers Data0 Permutation0 (Writable0 _ _ Target) (Writable0 _ _ Used))
  as [le1 [m1 [Validate [Registers1 [Data1 [Permutation1 [Target1 [Used1 [Frame1 Writable1]]]]]]]]].
destruct (normalize_correct ge e le1 m1 d.+1 bd bt bp bu source p
  (separate_data_permutation Separate) (separate_data_used Separate)
  ltac:(pose proof (separate_permutation_target Separate); congruence)
  (separate_target_used Separate) (separate_permutation_used Separate)
  (input_data Registers1) (input_target Registers1) (input_permutation Registers1)
  (input_used Registers1) (input_n Registers1) Size Values Data1 Target1 Permutation1 Used1)
  as [q [le2 [m2 [Normalized [Normalize [Data2 [Permutation2 [RegisterFrame2 [Frame2 Writable2]]]]]]]]].
have Registers2 : input_registers le2 d.+1 bd bp bt bu btrace bo.
{ eapply input_registers_frame; eauto. }
set (le3 := PTree.set Permute.top (Vint (Int.repr (Z.of_nat d))) le2).
have Top : exec_stmt function_entry2 ge e le2 m2
    (Permute.set Permute.top (Permute.sub (Permute.reg Permute.n) (Permute.lit 1)))
    E0 le3 m2 Out_normal.
{ unfold le3. replace (Z.of_nat d) with (Z.of_nat d.+1 - 1)%Z by lia.
  apply set_top_value; [lia|exact (input_n Registers2)]. }
have LoopArrays : loop_arrays bd bp btrace bo m2 source q [::].
{ constructor; try assumption.
  - intros k value H. destruct k; discriminate.
  - apply Frame2.
    + pose proof (separate_permutation_out Separate). congruence.
    + pose proof (separate_used_out Separate). congruence.
    + apply Frame1.
      * pose proof (separate_used_out Separate). congruence.
      * pose proof (separate_target_out Separate). congruence.
      * exact Output0.
  - apply Writable2, Writable1, Writable0, Trace. }
destruct (@main_loop_nonempty d bd bp btrace bo
  (separate_data_permutation Separate) (separate_data_trace Separate)
  (separate_data_out Separate) (separate_permutation_trace Separate)
  (separate_permutation_out Separate) (separate_trace_out Separate) Size
  ge e source q le3 m2 Values (initial_loop_registers Registers2) LoopArrays)
  as [le' [memory' [outcome [Main [Result MainFrame]]]]].
destruct (result_arrays_return Result) as [code [Return Codes]].
subst outcome.
have Tail : exec_stmt function_entry2 ge e le m0 nonempty_tail E0 le' memory'
    (Out_return (Some (Vint (Int.repr code), Permute.u32))).
{ unfold nonempty_tail. cbn [Permute.seq fold_right].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Validate|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Normalize|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Top|].
  eapply exec_Sseq_2; [exact Main|discriminate]. }
have ModelResult : solc_permute source p = Some (solc_nonempty source q).
{ by rewrite /solc_permute Normalized. }
have [verified [Verified Spec]] := solc_permute_verified source p.
rewrite ModelResult in Verified. inversion Verified; subst verified.
exists le', memory', code, (solc_nonempty source q). split.
- eapply permute_nonempty_body with (count := Z.of_nat d.+1); [lia|exact (input_n Registers)|
    exact S1|exact S2|exact S3|exact Tail].
- split; [exact ModelResult|]. split; [exact Result|]. split; assumption.
Qed.

(* The exported theorem includes parameter binding, return conversion,
   and function cleanup in the original Clight call semantics. *)
Theorem permute_call_correct d ge memory bd bp bt bu btrace bo
    (source : 'I_d.+1 -> nat) (p : 'S_d.+1) :
  (d.+1 <= 1024)%coq_nat -> separate_arrays bd bp bt bu btrace bo ->
  (forall x, uint (Z.of_nat (source x))) ->
  array_at memory bd (words source) ->
  array_at memory bp (words (fun x => val (p x))) ->
  writable_array memory bt d.+1 -> writable_array memory bu d.+1 ->
  writable_array memory btrace (2 * d.+1) -> writable_array memory bo 3 ->
  exists memory' code result,
    eval_funcall function_entry2 ge memory (Internal Permute.permute)
      (call_arguments (Int.repr (Z.of_nat d.+1)) (Vptr bd Ptrofs.zero)
        (Vptr bp Ptrofs.zero) (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
        (Vptr btrace Ptrofs.zero) (Vptr bo Ptrofs.zero)) E0 memory' (Vint (Int.repr code)) /\
    solc_permute source p = Some result /\
    result_arrays bd bp btrace bo result memory'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    solc_result_spec source p result /\ (code = 0%Z \/ code = 1%Z).
Proof.
intros Size Separate Values Data Permutation Target Used Trace Output.
pose le := call_temps (Int.repr (Z.of_nat d.+1)) (Vptr bd Ptrofs.zero)
  (Vptr bp Ptrofs.zero) (Vptr bt Ptrofs.zero) (Vptr bu Ptrofs.zero)
  (Vptr btrace Ptrofs.zero) (Vptr bo Ptrofs.zero).
have Registers : input_registers le d.+1 bd bp bt bu btrace bo.
{ constructor; reflexivity. }
destruct (@permute_body_correct d ge empty_env le memory bd bp bt bu btrace bo
  source p Size Separate Values Registers Data Permutation Target Used Trace Output)
  as [le' [memory' [code [result [Body [Model [Arrays [Spec Codes]]]]]]]].
exists memory', code, result. split.
- apply permute_call with (le' := le'). exact Body.
- split; [exact Model|]. split; [exact Arrays|]. split; assumption.
Qed.

Print Assumptions permute_body_correct.
Print Assumptions permute_call_correct.
