(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Lia PeanoNat.
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Section Measure.
Variable T : finType.
Implicit Types p : {perm T}.

Lemma moved_place_top p top : p top != top ->
  moved (exchange p top (p top)) :\ top = (moved p :\ top) :\ (p top).
Proof.
move=> Htop; apply/setP=> x.
rewrite !inE /exchange permM.
case Hxt: (x == top); first by rewrite ?andbF.
have Htx : top != x by rewrite eq_sym Hxt.
case Hxp: (x == p top).
- move/eqP: Hxp=> ->; by rewrite tpermR eqxx !andbF.
- have Hpx : p top != x by rewrite eq_sym Hxp.
  by rewrite tpermD // Hxt Hxp.
Qed.

Lemma moved_open_cycle p top pos : p top = top -> p pos != pos ->
  moved (exchange p top pos) :\ top = moved p :\ top.
Proof.
move=> Htop Hpos; apply/setP=> x.
rewrite !inE /exchange permM.
case Hxt: (x == top); first by rewrite ?andbF.
have Htx : top != x by rewrite eq_sym Hxt.
case Hxp: (x == pos).
- move/eqP: Hxp=> E; subst x; by rewrite tpermR Htop eq_sym Hxt Hpos.
- have Hpx : pos != x by rewrite eq_sym Hxp.
  by rewrite tpermD.
Qed.

Lemma rank_place_top p top : p top != top ->
  (rank (exchange p top (p top)) top < rank p top)%coq_nat.
Proof.
move=> Htop.
have Hmem : p top \in moved p :\ top.
  by rewrite !inE Htop (inj_eq perm_inj).
have Hcard := cardsD1 (p top) (moved p :\ top).
rewrite Hmem /= -moved_place_top // in Hcard.
rewrite /rank (negbTE Htop).
case: ifP=> Hfixed; rewrite /addn /muln /= in Hcard *; lia.
Qed.

Lemma rank_open_cycle p top pos : p top = top -> p pos != pos ->
  (rank (exchange p top pos) top < rank p top)%coq_nat.
Proof.
move=> Htop Hpos.
have Hmove : p pos != top.
  apply/eqP=> E.
  have Epos : pos = top := perm_inj (eq_trans E (esym Htop)).
  by rewrite Epos Htop eqxx in Hpos.
rewrite /rank (moved_open_cycle Htop Hpos) /exchange permM tpermL.
rewrite Htop eqxx (negbTE Hmove) /addn /muln /=; lia.
Qed.

Lemma choose_rank p top pos : choose p top = Some pos ->
  (rank (exchange p top pos) top < rank p top)%coq_nat.
Proof.
rewrite /choose; case: ifP=> Htop.
- move=> [<-]; exact: rank_place_top.
- move/last_moved_some=> [_ Hpos].
  apply: rank_open_cycle=> //; by move/negPn/eqP: Htop.
Qed.
End Measure.

Section Runs.
Variable A : Type.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.

Lemma run_no_exhaustion fuel s p trace :
  (rank p top < fuel)%coq_nat -> @run A m fuel s p trace <> Exhausted.
Proof.
elim: fuel s p trace => [|fuel IH] s p trace Hfuel; first by lia.
rewrite /=; case Hchoose: (choose p ord_max)=> [pos|] //.
case: ifP=> _ //.
apply: IH.
have Hrank := choose_rank Hchoose.
exact (Nat.lt_le_trans _ _ _ Hrank (proj1 (Nat.lt_succ_r _ _) Hfuel)).
Qed.

Lemma run_correct fuel s p trace result out :
  @run A m fuel s p trace = Done result out ->
  forall i, result i = s (p^-1 i).
Proof.
elim: fuel s p trace => [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [pos|].
- case: ifP=> Hdepth // Hrun i.
  rewrite (IH _ _ _ Hrun i).
  exact: apply_exchange.
- move=> [<- _] i.
  by rewrite (choose_none Hchoose) invg1 perm1.
Qed.

(* This is the swap-only part of Lean's indexed Trace. *)
Inductive SwapTrace : ('I_m.+1 -> A) -> ('I_m.+1 -> A) -> seq nat -> Prop :=
  | Trace_refl s : SwapTrace s s [::]
  | Trace_step s current pos trace :
      (0 < depth pos)%N -> (depth pos <= 16)%N ->
      SwapTrace s current trace ->
      SwapTrace s (swap_stack current pos) (trace ++ [:: depth pos]).

Lemma chosen_depth p pos : choose p top = Some pos -> (0 < depth pos)%N.
Proof.
move/choose_some=> [Hne _].
rewrite /depth subn_gt0.
have Hle := ltn_ord pos.
have Hval : val pos != m.
  by rewrite -[m]/(val top) (inj_eq val_inj).
by rewrite ltn_neqAle Hval -ltnS.
Qed.

Lemma run_trace fuel start s p trace result out :
  SwapTrace start s trace ->
  @run A m fuel s p trace = Done result out -> SwapTrace start result out.
Proof.
elim: fuel s p trace => [|fuel IH] s p trace Htrace //=.
case Hchoose: (choose p ord_max)=> [pos|].
- case: ifP=> Hdepth // Hrun; apply: IH Hrun.
  apply: Trace_step Htrace=> //; exact: chosen_depth Hchoose.
- by move=> [<- <-].
Qed.

Lemma run_blocked_positive fuel s p trace excess :
  @run A m fuel s p trace = Blocked excess -> (0 < excess)%N.
Proof.
elim: fuel s p trace => [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [pos|] //.
case: ifP=> Hdepth; first exact: IH.
move=> [<-]; by rewrite subn_gt0 ltnNge Hdepth.
Qed.

Theorem permute_nonempty_no_exhaustion s p :
  @permute_nonempty A m s p <> Exhausted.
Proof. apply: run_no_exhaustion; exact: Nat.lt_succ_diag_r. Qed.

Theorem permute_nonempty_correct s p result out :
  @permute_nonempty A m s p = Done result out ->
  (forall i, result i = s (p^-1 i)) /\ SwapTrace s result out.
Proof.
move=> Hrun; split; first exact: run_correct Hrun.
exact: run_trace (Trace_refl s) Hrun.
Qed.

(* The caller can use this proof-carrying result. Exhaustion has no constructor
   that can satisfy the postcondition. This retains the Lean API's guarantee
   that each successful result has a trace of permitted swaps. *)
Definition result_spec (s : 'I_m.+1 -> A) (p : 'S_m.+1)
    (r : Result A m.+1) : Prop :=
  match r with
  | Done result out =>
      (forall i, result i = s (p^-1 i)) /\ SwapTrace s result out
  | Blocked excess => (0 < excess)%N
  | Exhausted => False
  end.

Definition certified_permute s p : {r | result_spec s p r}.
Proof.
exists (permute_nonempty s p).
case Hrun: (permute_nonempty s p)=> [result out|excess|] /=.
- exact: permute_nonempty_correct Hrun.
- exact: run_blocked_positive Hrun.
- exact: permute_nonempty_no_exhaustion Hrun.
Defined.
End Runs.

Print Assumptions apply_exchange.
Print Assumptions choose_rank.
Print Assumptions run_no_exhaustion.
Print Assumptions run_correct.
Print Assumptions run_trace.
Print Assumptions certified_permute.
