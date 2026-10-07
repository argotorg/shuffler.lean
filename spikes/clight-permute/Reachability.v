(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Proofs.
Require Import SolcModel ModelProofs.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Section ReachabilityProofs.
Variable A : eqType.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.


Definition deep_fixed (p : 'S_m.+1) : Prop :=
  forall i, (16 < depth i)%N -> p i = i.

Lemma deep_not_top (i : 'I_m.+1) : (16 < depth i)%N -> top != i.
Proof.
move=> Deep; apply/eqP=> E; subst i.
by rewrite /depth /top subnn in Deep.
Qed.

Lemma trace_preserves_deep start result trace :
  @SwapTrace A m start result trace ->
  forall i, (16 < depth i)%N -> result i = start i.
Proof.
move=> Trace; elim: Trace=> [s|s current pos out Positive Range Previous IH] i Deep //.
have TopNe := deep_not_top Deep.
have PosNe : pos != i.
{ apply/eqP=> E; subst pos.
  have Bad := leq_ltn_trans Range Deep.
  by rewrite ltnn in Bad. }
by rewrite /swap_stack /comp (tpermD TopNe PosNe) IH.
Qed.

Lemma chosen_in_range p pos :
  deep_fixed p -> choose p top = Some pos -> (depth pos <= 16)%N.
Proof.
move=> Fixed Choice.
have [_ Moved] := choose_some Choice.
case Range: (depth pos <= 16)%N=> //.
have Deep : (16 < depth pos)%N by rewrite ltnNge Range.
by rewrite (Fixed pos Deep) eqxx in Moved.
Qed.

Lemma exchange_keeps_deep p pos :
  deep_fixed p -> choose p top = Some pos -> deep_fixed (exchange p top pos).
Proof.
move=> Fixed Choice i Deep.
have TopNe := deep_not_top Deep.
have [_ Moved] := choose_some Choice.
have PosNe : pos != i.
{ apply/eqP=> E; subst pos. by rewrite (Fixed i Deep) eqxx in Moved. }
by rewrite exchangeE (tpermD TopNe PosNe) Fixed.
Qed.

Lemma run_cannot_block fuel s p trace result finalp out pos excess :
  deep_fixed p ->
  @solc_run A m fuel s p trace <> SolcBlocked result finalp out pos excess.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace Fixed //=.
case Choice: (choose p ord_max)=> [selected|] //.
have Next := exchange_keeps_deep Fixed Choice.
case: ifP=> Equal; first exact: IH Next.
rewrite (chosen_in_range Fixed Choice).
exact: IH Next.
Qed.

Lemma success_requires_reachable s p result finalp trace :
  @solc_permute A m.+1 s p = Some (SolcDone result finalp trace) ->
  values_reachable s p.
Proof.
move=> Run.
have [r [Model Spec]] := solc_permute_verified s p.
rewrite Run in Model. injection Model=> E; subst r.
move: Spec=> [_ [Values [Trace Bound]]] i Deep.
rewrite -(trace_preserves_deep Trace Deep).
exact: Values.
Qed.

Lemma reachable_succeeds s p :
  values_reachable s p ->
  exists result finalp trace,
    @solc_permute A m.+1 s p = Some (SolcDone result finalp trace).
Proof.
move=> Reachable.
have [q [Normalize [Compatible Fixed]]] := normalize_complete s p.
have DeepFixed : deep_fixed q by move=> i Deep; apply: Fixed; exact: Reachable.
case Run: (solc_nonempty s q)=> [result finalp trace|result finalp trace pos excess|].
- exists result, finalp, trace. by rewrite /solc_permute Normalize Run.
- have Bad := @run_cannot_block (rank q top).+1 s q [::]
    result finalp trace pos excess DeepFixed.
  exact: False_ind _ (Bad Run).
- exact: False_ind _ (solc_nonempty_no_exhaustion Run).
Qed.

Theorem solc_success_iff_reachable s p :
  (exists result finalp trace,
    @solc_permute A m.+1 s p = Some (SolcDone result finalp trace)) <->
  values_reachable s p.
Proof.
split; last exact: reachable_succeeds.
by move=> [result [finalp [trace Run]]]; exact: success_requires_reachable Run.
Qed.

Theorem solc_blocked_iff_unreachable s p :
  (exists result finalp trace pos excess,
    @solc_permute A m.+1 s p = Some (SolcBlocked result finalp trace pos excess)) <->
  ~ values_reachable s p.
Proof.
split.
- move=> [result [finalp [trace [pos [excess Blocked]]]]] Reachable.
  have [done [donep [out Success]]] := reachable_succeeds Reachable.
  by rewrite Success in Blocked.
- move=> Unreachable.
  have [r [Run Spec]] := solc_permute_verified s p.
  case E: r Run Spec=> [result finalp trace|result finalp trace pos excess|] Run Spec.
  + exact: False_ind _ (Unreachable (success_requires_reachable Run)).
  + by exists result, finalp, trace, pos, excess.
  + exact: False_ind _ Spec.
Qed.

Theorem reachable_has_verified_trace s p :
  values_reachable s p ->
  exists result finalp trace,
    @solc_permute A m.+1 s p = Some (SolcDone result finalp trace) /\
    SwapTrace s result trace /\
    (forall i, result i = target_of s p i) /\ (size trace <= 2 * m.+1)%N.
Proof.
move=> Reachable.
have [result [finalp [trace Run]]] := reachable_succeeds Reachable.
have [r [Model Spec]] := solc_permute_verified s p.
rewrite Run in Model. injection Model=> E; subst r.
move: Spec=> [_ [Values [Trace Bound]]].
by exists result, finalp, trace; repeat split.
Qed.
End ReachabilityProofs.

Print Assumptions solc_success_iff_reachable.
Print Assumptions solc_blocked_iff_unreachable.
