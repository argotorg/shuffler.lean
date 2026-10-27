(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Lia PeanoNat.
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Proofs.
Require Import SolcModel.
Require Export ModelSpec.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope group_scope.

Section NormalizationProofs.
Variable T : finType.
Variable A : eqType.

Lemma target_compatible (s : T -> A) p : compatible s (target_of s p) p.
Proof. by move=> i; rewrite /target_of /comp permK. Qed.

Lemma compatible_inverse (s target : T -> A) p : compatible s target p ->
  forall i, s (p^-1 i) = target i.
Proof. by move=> H i; rewrite H permKV. Qed.

Lemma set_destination_here (p : {perm T}) i j :
  set_destination p i j i = j.
Proof. by rewrite /set_destination exchangeE tpermL permKV. Qed.

Lemma set_destination_other (p : {perm T}) i j x :
  x != i -> p x != j -> set_destination p i j x = p x.
Proof.
move=> Hxi Hxj; rewrite /set_destination exchangeE tpermD //.
- by rewrite eq_sym.
- apply/eqP=> E; subst x; by rewrite permKV eqxx in Hxj.
Qed.

Lemma set_destination_compatible (s target : T -> A) p i j :
  compatible s target p -> s i = target j ->
  compatible s target (set_destination p i j).
Proof.
move=> Hp Hi x; rewrite /set_destination exchangeE.
case Hxi: (x == i).
- move/eqP: Hxi=> ->; by rewrite tpermL permKV.
case Hxj: (x == p^-1 j).
- move/eqP: Hxj=> ->; rewrite tpermR -Hp Hp permKV; exact: esym Hi.
- rewrite tpermD; first exact: Hp.
  + by rewrite eq_sym Hxi.
  + by rewrite eq_sym Hxj.
Qed.

Lemma fix_one_compatible (s target : T -> A) p i :
  compatible s target p -> compatible s target (fix_one s target p i).
Proof.
move=> Hp; rewrite /fix_one; case: ifP=> Hi //.
apply: set_destination_compatible Hp _.
by move: Hi; rewrite inE=> /eqP.
Qed.

Lemma fix_one_keeps_fixed (s target : T -> A) (p : {perm T}) i x :
  p x = x -> fix_one s target p i x = x.
Proof.
move=> Hx; rewrite /fix_one; case: ifP=> _ //.
case Hxi: (x == i).
- by move/eqP: Hxi=> ->; rewrite set_destination_here.
- have Hxi' : x != i by rewrite Hxi.
  have Hpx : p x != i by rewrite Hx Hxi.
  by rewrite (set_destination_other Hxi' Hpx).
Qed.

Lemma fix_fold_compatible (s target : T -> A) xs p :
  compatible s target p ->
  compatible s target (foldl (fix_one s target) p xs).
Proof.
elim: xs p=> [|i xs IH] p Hp //=.
apply: IH; exact: fix_one_compatible.
Qed.

Lemma fix_fold_keeps_fixed (s target : T -> A) xs (p : {perm T}) x :
  p x = x -> foldl (fix_one s target) p xs x = x.
Proof.
elim: xs p=> [|i xs IH] p Hx //=.
apply: IH; exact: fix_one_keeps_fixed.
Qed.

Lemma fix_fold_fixes (s target : T -> A) xs p x :
  x \in xs -> x \in fixed_values s target ->
  foldl (fix_one s target) p xs x = x.
Proof.
elim: xs p=> [|i xs IH] p //=.
rewrite in_cons=> /orP[/eqP ->|Hx] Hgood.
- apply: fix_fold_keeps_fixed.
  by rewrite /fix_one Hgood set_destination_here.
- exact: IH Hx Hgood.
Qed.

Lemma first_free_some (target : T -> A) value used xs j :
  first_free target value used xs = Some j ->
  j \in xs /\ j \notin used /\ target j = value.
Proof.
elim: xs=> [|x xs IH] //=.
case: ifP=> [/andP[Hfree /eqP Hvalue]|Hno].
- move=> [<-]; by rewrite in_cons eqxx.
- move/IH=> [Hj [Hfree Hvalue]]; split; first by rewrite in_cons Hj orbT.
  by split.
Qed.

Lemma first_free_none (target : T -> A) value used xs :
  first_free target value used xs = None ->
  forall j, j \in xs -> j \notin used -> target j != value.
Proof.
elim: xs=> [|x xs IH] //=.
case: ifP=> Hno // Hnone j.
rewrite in_cons=> /orP[/eqP ->|Hj] Hfree.
- by move: Hno; rewrite Hfree /= => ->.
- exact: IH Hnone _ Hj Hfree.
Qed.

Lemma set_destination_keeps (p : {perm T}) (done : {set T}) i j x :
  i \notin done -> j \notin p @: done -> x \in done ->
  set_destination p i j x = p x.
Proof.
move=> Hi Hj Hx; apply: set_destination_other.
- apply/eqP=> E; subst x; by rewrite Hx in Hi.
- apply/eqP=> E.
  have Himage : p x \in p @: done := imset_f p Hx.
  rewrite E in Himage; by rewrite Himage in Hj.
Qed.

Lemma set_destination_image (p : {perm T}) (done : {set T}) i j :
  i \notin done -> j \notin p @: done ->
  set_destination p i j @: (i |: done) = j |: (p @: done).
Proof.
move=> Hi Hj; rewrite imsetU1 set_destination_here.
congr (_ |: _); apply: eq_in_imset=> x Hx.
exact: set_destination_keeps Hi Hj Hx.
Qed.

Lemma fill_complete (s target : T -> A) xs p used (done : {set T}) :
  compatible s target p -> used = p @: done -> uniq xs ->
  (forall i, i \in xs -> i \notin fixed_values s target -> i \notin done) ->
  exists q, fill_destinations s target xs p used = Some q /\
    compatible s target q /\ (forall i, i \in done -> q i = p i).
Proof.
elim: xs p used done=> [|i xs IH] p used done Hp Hused Huniq Hfresh.
- exists p; by repeat split.
- move/andP: Huniq=> [Hixs Huniq].
  rewrite /=; case Hgood: (i \in fixed_values s target).
  + apply: IH Hp Hused Huniq _.
    move=> x Hx Hnot; apply: Hfresh Hnot.
    by rewrite in_cons Hx orbT.
  + have Hinot : i \notin done.
      apply: Hfresh; by rewrite ?in_cons ?eqxx ?Hgood.
    have Hpi : p i \notin used.
      rewrite Hused mem_imset; [exact Hinot | exact: perm_inj].
    case E: (first_free target (s i) used (enum T))=> [j|].
    * have [_ [Hj Hvalue]] := first_free_some E.
      have Hjimage : j \notin p @: done by rewrite -Hused.
      have Hq : compatible s target (set_destination p i j).
        apply: set_destination_compatible Hp _; exact: esym Hvalue.
      have Hused' : j |: used = set_destination p i j @: (i |: done).
        by rewrite (set_destination_image Hinot Hjimage) -Hused.
      have Hfresh' : forall x, x \in xs -> x \notin fixed_values s target ->
          x \notin i |: done.
        move=> x Hx Hnot; rewrite !inE negb_or; apply/andP; split.
        -- apply/eqP=> E'; subst x; by rewrite Hx in Hixs.
        -- apply: Hfresh Hnot; by rewrite in_cons Hx orbT.
      have [q [Hfill [Hcompatible Hkeep]]] := IH _ _ _ Hq Hused' Huniq Hfresh'.
      exists q; split=> //; split=> // x Hx.
      rewrite Hkeep; last by rewrite inE Hx orbT.
      exact: set_destination_keeps Hinot Hjimage Hx.
    * have Hnone := first_free_none E (j := p i) ltac:(by rewrite mem_enum) Hpi.
      by rewrite -Hp eqxx in Hnone.
Qed.

Theorem normalize_complete (s : T -> A) p :
  exists q, normalize s p = Some q /\ compatible s (target_of s p) q /\
    (forall i, s i = target_of s p i -> q i = i).
Proof.
pose target := target_of s p.
pose good := fixed_values s target.
pose q0 := fix_values s target p.
have Hq0 : compatible s target q0.
  apply: fix_fold_compatible; exact: target_compatible.
have Hfixed : forall i, i \in good -> q0 i = i.
  move=> i Hi; apply: fix_fold_fixes Hi; exact: mem_enum.
have Himage : good = q0 @: good.
  symmetry; rewrite (eq_in_imset (g := id) Hfixed).
  exact: imset_id.
have Hfresh : forall i, i \in enum T -> i \notin good -> i \notin good by [].
have [q [Hfill [Hcompatible Hkeep]]] :=
  fill_complete Hq0 Himage (enum_uniq T) Hfresh.
exists q; split; first exact: Hfill.
split=> // i Hi.
have Hgood : i \in good by rewrite /good /fixed_values inE Hi eqxx.
by rewrite (Hkeep i Hgood) Hfixed.
Qed.

Lemma fill_raw_refinement (s target : T -> A) xs (p : {perm T}) used (done : {set T})
    (assignment : T -> T) (q : {perm T}) :
  used = p @: done -> uniq xs ->
  (forall i, i \in fixed_values s target -> i \in done) ->
  (forall i, i \in xs -> i \notin fixed_values s target -> i \notin done) ->
  (forall i, i \in done -> assignment i = p i) ->
  fill_destinations s target xs p used = Some q ->
  exists result, raw_fill s target xs assignment used = Some result /\
    (forall i, (i \in done) || (i \in xs) -> result i = q i).
Proof.
elim: xs p used done assignment=> [|i xs IH] p used done assignment
  Hused Huniq Hfixed Hfresh Hagree /=.
- move=> [<-]; exists assignment; split=> // x.
  by rewrite in_nil orbF; exact: Hagree.
- move/andP: Huniq=> [Hixs Huniq].
  case Hgood: (i \in fixed_values s target).
  + move=> Hfill.
    have Hfresh' : forall x, x \in xs -> x \notin fixed_values s target ->
        x \notin done.
      move=> x Hx Hnot; apply: Hfresh Hnot; by rewrite in_cons Hx orbT.
    have [result [Hraw Hresult]] :=
      IH _ _ _ _ Hused Huniq Hfixed Hfresh' Hagree Hfill.
    exists result; split=> // x.
    rewrite in_cons=> /orP[Hx|/orP[/eqP ->|Hx]].
    * apply: Hresult; by rewrite Hx.
    * apply: Hresult; by rewrite Hfixed.
    * apply: Hresult; by rewrite Hx orbT.
  + case E: (first_free target (s i) used (enum T))=> [j|] // Hfill.
    have Hinot : i \notin done.
      apply: Hfresh; by rewrite ?in_cons ?eqxx ?Hgood.
    have [_ [Hj Hvalue]] := first_free_some E.
    have Hjimage : j \notin p @: done by rewrite -Hused.
    have Hused' : j |: used = set_destination p i j @: (i |: done).
      by rewrite (set_destination_image Hinot Hjimage) -Hused.
    have Hfixed' : forall x, x \in fixed_values s target -> x \in i |: done.
      move=> x Hx; by rewrite inE Hfixed ?orbT.
    have Hfresh' : forall x, x \in xs -> x \notin fixed_values s target ->
        x \notin i |: done.
      move=> x Hx Hnot; rewrite !inE negb_or; apply/andP; split.
      * apply/eqP=> E'; subst x; by rewrite Hx in Hixs.
      * apply: Hfresh Hnot; by rewrite in_cons Hx orbT.
    have Hagree' : forall x, x \in i |: done ->
        write_index assignment i j x = set_destination p i j x.
      move=> x; rewrite !inE=> /orP[/eqP ->|Hx].
      * by rewrite /write_index eqxx set_destination_here.
      * have Hxi : x != i by apply/eqP=> E'; subst x; rewrite Hx in Hinot.
        rewrite /write_index (negbTE Hxi) (Hagree _ Hx).
        symmetry; exact: set_destination_keeps Hinot Hjimage Hx.
    have [result [Hraw Hresult]] :=
      IH _ _ _ _ Hused' Huniq Hfixed' Hfresh' Hagree' Hfill.
    exists result; split=> // x.
    rewrite in_cons=> /orP[Hx|/orP[/eqP ->|Hx]]; apply: Hresult.
    * by rewrite inE Hx orbT.
    * by rewrite !inE eqxx.
    * by rewrite Hx orbT.
Qed.

Theorem raw_normalize_complete (s : T -> A) p :
  exists q result, normalize s p = Some q /\ raw_normalize s p = Some result /\
    (forall i, result i = q i) /\ compatible s (target_of s p) q /\
    (forall i, s i = target_of s p i -> q i = i).
Proof.
have [q [Hnorm [Hcompatible Hfixed]]] := normalize_complete s p.
pose target := target_of s p.
pose good := fixed_values s target.
pose q0 := fix_values s target p.
have Hfixed0 : forall i, i \in good -> q0 i = i.
  move=> i Hi; apply: fix_fold_fixes Hi; exact: mem_enum.
have Himage : good = q0 @: good.
  symmetry; rewrite (eq_in_imset (g := id) Hfixed0); exact: imset_id.
have Hinclude : forall i, i \in fixed_values s target -> i \in good by [].
have Hfresh : forall i, i \in enum T -> i \notin good -> i \notin good by [].
have Hagree : forall i, i \in good ->
    (if i \in good then i else p i) = q0 i.
  by move=> i Hi; rewrite Hi Hfixed0.
have [result [Hraw Hresult]] :=
  fill_raw_refinement Himage (enum_uniq T) Hinclude Hfresh Hagree Hnorm.
exists q, result; split; first exact: Hnorm.
split; first exact: Hraw.
split.
- move=> i; apply: Hresult; by rewrite mem_enum orbT.
- by split.
Qed.
End NormalizationProofs.

Section LoopProofs.
Variable A : eqType.
Variable m : nat.
Let top : 'I_m.+1 := ord_max.

Lemma equal_swap (s : 'I_m.+1 -> A) pos :
  s top = s pos -> forall i, swap_stack s pos i = s i.
Proof.
move=> Heq i; rewrite /swap_stack /comp.
case Hit: (i == top).
- by move/eqP: Hit=> ->; rewrite tpermL Heq.
case Hip: (i == pos).
- by move/eqP: Hip=> ->; rewrite tpermR Heq.
- rewrite tpermD //; by rewrite eq_sym ?Hit ?Hip.
Qed.

Lemma equal_exchange (s : 'I_m.+1 -> A) p pos :
  s top = s pos -> forall i, s ((exchange p top pos)^-1 i) = s (p^-1 i).
Proof.
move=> Heq i; rewrite -(equal_swap Heq).
exact: apply_exchange.
Qed.

Lemma solc_run_no_exhaustion fuel s p trace :
  (rank p top < fuel)%coq_nat -> @solc_run A m fuel s p trace <> SolcExhausted.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace Hfuel; first by lia.
rewrite /=; case Hchoose: (choose p ord_max)=> [pos|] //.
have Hrank := choose_rank Hchoose.
have Hnext : (rank (exchange p top pos) top < fuel)%coq_nat.
  exact (Nat.lt_le_trans _ _ _ Hrank (proj1 (Nat.lt_succ_r _ _) Hfuel)).
case: ifP=> Heq; first exact: IH.
case: ifP=> Hdepth //; exact: IH.
Qed.

Lemma solc_run_correct fuel s p trace result finalp out :
  @solc_run A m fuel s p trace = SolcDone result finalp out ->
  finalp = 1 /\ forall i, result i = s (p^-1 i).
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [pos|].
- case: ifP=> [/eqP Heq|Hneq].
  + move/IH=> [Hfinal Hresult]; split=> // i.
    rewrite Hresult; apply: equal_exchange; exact Heq.
  + case: ifP=> Hdepth // /IH[Hfinal Hresult]; split=> // i.
    rewrite Hresult; exact: apply_exchange.
- move=> [<- <- _]; split; first exact: choose_none Hchoose.
  move=> i; by rewrite (choose_none Hchoose) invg1 perm1.
Qed.

Lemma solc_run_trace fuel start s p trace result finalp out :
  SwapTrace start s trace ->
  @solc_run A m fuel s p trace = SolcDone result finalp out ->
  SwapTrace start result out.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace Htrace //=.
case Hchoose: (choose p ord_max)=> [pos|].
- case: ifP=> Heq; first exact: IH Htrace.
  case: ifP=> Hdepth // Hrun; apply: IH Hrun.
  apply: Trace_step Htrace=> //; exact: chosen_depth Hchoose.
- by move=> [<- _ <-].
Qed.

Lemma solc_run_blocked fuel start s p trace result finalp out pos excess :
  SwapTrace start s trace ->
  @solc_run A m fuel s p trace = SolcBlocked result finalp out pos excess ->
  SwapTrace start result out /\
  choose finalp top = Some pos /\
  result top != result pos /\
  (16 < depth pos)%N /\ excess = (depth pos - 16)%N.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace Htrace //=.
case Hchoose: (choose p ord_max)=> [selected|] //.
case: ifP=> Heq; first exact: IH Htrace.
case: ifP=> Hdepth.
- apply: IH.
  apply: Trace_step Htrace=> //; exact: chosen_depth Hchoose.
- move=> [<- <- <- <- <-]; repeat split=> //.
  + by rewrite Heq.
  + by rewrite ltnNge Hdepth.
Qed.

Lemma solc_run_blocked_target fuel s p trace result finalp out pos excess :
  @solc_run A m fuel s p trace = SolcBlocked result finalp out pos excess ->
  forall i, result (finalp^-1 i) = s (p^-1 i).
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [selected|] //.
case: ifP=> [/eqP Heq|Hneq].
- move/IH=> Hresult i; rewrite Hresult; apply: equal_exchange; exact Heq.
- case: ifP=> Hdepth.
  + move/IH=> Hresult i; rewrite Hresult; exact: apply_exchange.
  + by move=> [<- <- _ _ _].
Qed.

Lemma rank_bound (p : 'S_m.+1) : ((rank p top).+1 <= 2 * m.+1)%N.
Proof.
have Hsub : moved p :\ top \subset [set~ top].
  by apply/subsetP=> x; rewrite !inE=> /andP[Htop _].
have Hcard := subset_leq_card Hsub.
rewrite cardsC1 card_ord /= in Hcard.
have Hmult : (2 * #|moved p :\ top| <= 2 * m)%N.
  by rewrite leq_mul2l Hcard orbT.
rewrite /rank mulnS add2n; case: ifP=> _.
- rewrite addn1; exact Hmult.
- rewrite addn0; change (2 * #|moved p :\ top| <= (2 * m).+1)%N.
  exact: leq_trans Hmult (leqnSn _).
Qed.

Lemma solc_run_done_bound fuel s p trace result finalp out :
  @solc_run A m fuel s p trace = SolcDone result finalp out ->
  (size out <= size trace + fuel)%N.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [pos|].
- case: ifP=> Heq.
  + move/IH=> Hbound; apply: leq_trans Hbound _.
    by rewrite leq_add2l leqnSn.
  + case: ifP=> Hdepth // /IH Hbound.
    rewrite size_cat /= addn1 addSn -addnS in Hbound; exact: Hbound.
- move=> [_ _ <-]; exact: leq_addr.
Qed.

Lemma solc_run_blocked_bound fuel s p trace result finalp out pos excess :
  @solc_run A m fuel s p trace = SolcBlocked result finalp out pos excess ->
  (size out <= size trace + fuel)%N.
Proof.
elim: fuel s p trace=> [|fuel IH] s p trace //=.
case Hchoose: (choose p ord_max)=> [selected|] //.
case: ifP=> Heq.
- move/IH=> Hbound; apply: leq_trans Hbound _.
  by rewrite leq_add2l leqnSn.
- case: ifP=> Hdepth.
  + move/IH=> Hbound.
    rewrite size_cat /= addn1 addSn -addnS in Hbound; exact: Hbound.
  + move=> [_ _ <- _ _]; exact: leq_addr.
Qed.

Theorem solc_nonempty_no_exhaustion s p :
  @solc_nonempty A m s p <> SolcExhausted.
Proof. apply: solc_run_no_exhaustion; exact: Nat.lt_succ_diag_r. Qed.

Theorem solc_nonempty_correct s p result finalp out :
  @solc_nonempty A m s p = SolcDone result finalp out ->
  finalp = 1 /\ (forall i, result i = s (p^-1 i)) /\
    SwapTrace s result out /\ (size out <= 2 * m.+1)%N.
Proof.
move=> Hrun; have [Hfinal Hresult] := solc_run_correct Hrun.
split=> //; split=> //; split.
- exact: solc_run_trace (Trace_refl s) Hrun.
- have Hbound := solc_run_done_bound Hrun.
  rewrite /= add0n in Hbound.
  exact: leq_trans Hbound (rank_bound p).
Qed.

Theorem solc_nonempty_blocked s p result finalp out pos excess :
  @solc_nonempty A m s p = SolcBlocked result finalp out pos excess ->
  SwapTrace s result out /\ choose finalp top = Some pos /\
  result top != result pos /\ (16 < depth pos)%N /\
  excess = (depth pos - 16)%N /\ (size out <= 2 * m.+1)%N /\
  (forall i, result (finalp^-1 i) = s (p^-1 i)).
Proof.
move=> Hrun.
have [Htrace [Hchoose [Hdifferent [Hdepth Hexcess]]]] :=
  solc_run_blocked (Trace_refl s) Hrun.
repeat split=> //.
- have Hbound := solc_run_blocked_bound Hrun.
  rewrite /= add0n in Hbound.
  exact: leq_trans Hbound (rank_bound p).
- exact: solc_run_blocked_target Hrun.
Qed.


Theorem solc_permute_verified (s : 'I_m.+1 -> A) (p : 'S_m.+1) :
  exists r, solc_permute s p = Some r /\ solc_result_spec s p r.
Proof.
have [q [Hnorm [Hcompatible Hfixed]]] := normalize_complete s p.
exists (solc_nonempty s q); split.
- by rewrite /solc_permute Hnorm.
- case Hrun: (solc_nonempty s q)=> [result finalp out|result finalp out pos excess|] /=.
  + have [Hfinal [Hresult [Htrace Hbound]]] := solc_nonempty_correct Hrun.
    split=> //; split.
    * move=> i; rewrite Hresult; apply: compatible_inverse; exact Hcompatible.
    * by split.
  + have [Htrace [Hchoose [Hneq [Hdepth [Hexcess [Hbound Htarget]]]]]] :=
      solc_nonempty_blocked Hrun.
    repeat split=> //.
    move=> i; rewrite Htarget; apply: compatible_inverse; exact Hcompatible.
  + exact: solc_nonempty_no_exhaustion Hrun.
Qed.
End LoopProofs.

Print Assumptions normalize_complete.
Print Assumptions raw_normalize_complete.
Print Assumptions solc_nonempty_no_exhaustion.
Print Assumptions solc_nonempty_correct.
Print Assumptions solc_nonempty_blocked.
Print Assumptions solc_permute_verified.
