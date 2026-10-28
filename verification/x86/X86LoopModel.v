(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Proofs.
Require Import ClightScalar SolcModel ModelProofs MainInvariant.
From X86 Require Import X86ModelTypes X86NormalizationModel.

Definition model_top d : 'I_(S d) := ord_max.
Definition model_choice {d} (p : model_permutation (S d)) := Legacy.Permute.choose p ord_max.
Definition model_exchange {d} (p : model_permutation (S d)) position :=
  Legacy.Permute.exchange p ord_max position.
Definition model_swap {d} (source : 'I_(S d) -> nat) position := Legacy.Permute.swap_stack source position.
Definition model_depth {d} (position : 'I_(S d)) := Legacy.Permute.depth position.
Definition model_rank {d} (p : model_permutation (S d)) := Legacy.Permute.rank p ord_max.
Definition model_run {d} fuel (source : 'I_(S d) -> nat) (p : model_permutation (S d)) depths :=
  SolcModel.solc_run fuel source p depths.
Definition model_nonempty {d} (source : 'I_(S d) -> nat) (p : model_permutation (S d)) :=
  SolcModel.solc_nonempty source p.
Definition model_permute {size} (source : 'I_size -> nat) (p : model_permutation size) :=
  SolcModel.solc_permute source p.

Lemma model_chosen_bounds d (p : model_permutation (S d)) position fuel :
  model_choice p = Some position -> (model_rank p < S fuel)%coq_nat ->
  (nat_of_ord position < d)%coq_nat /\ (model_rank (model_exchange p position) < fuel)%coq_nat.
Proof. exact (@main_selected_bounds d p position fuel). Qed.

Lemma model_run_done d fuel source (p : model_permutation (S d)) depths :
  model_choice p = None -> model_run (S fuel) source p depths = SolcDone source p depths.
Proof. intro Choice. unfold model_choice in Choice. unfold model_run. cbn [solc_run]. rewrite Choice. reflexivity. Qed.

Lemma model_run_equal d fuel source (p : model_permutation (S d)) depths position :
  model_choice p = Some position -> source (model_top d) = source position ->
  model_run (S fuel) source p depths = model_run fuel source (model_exchange p position) depths.
Proof.
  intros Choice Equal. unfold model_choice in Choice. unfold model_run. cbn [solc_run]. rewrite Choice.
  change (source ord_max = source position) in Equal. rewrite Equal eqxx. reflexivity.
Qed.

Lemma model_run_near d fuel source (p : model_permutation (S d)) depths position :
  model_choice p = Some position -> source (model_top d) <> source position ->
  (d <= nat_of_ord position + 16)%coq_nat ->
  model_run (S fuel) source p depths = model_run fuel (model_swap source position)
    (model_exchange p position) (depths ++ [:: model_depth position]).
Proof.
  intros Choice Different Near. unfold model_choice in Choice. unfold model_run. cbn [solc_run]. rewrite Choice.
  assert (Equal : (source ord_max == source position) = false).
  { apply /eqP. exact Different. }
  assert (Bound : (Legacy.Permute.depth position <= 16)%N).
  { apply /leP. change ((d - nat_of_ord position)%coq_nat <= 16)%coq_nat.
    unfold addn, muln, subn in *. lia. }
  rewrite Equal Bound. reflexivity.
Qed.

Lemma model_run_blocked d fuel source (p : model_permutation (S d)) depths position :
  model_choice p = Some position -> source (model_top d) <> source position ->
  (nat_of_ord position + 16 < d)%coq_nat ->
  model_run (S fuel) source p depths =
    SolcBlocked source p depths position (Nat.sub (model_depth position) 16).
Proof.
  intros Choice Different Far. unfold model_choice in Choice. unfold model_run. cbn [solc_run]. rewrite Choice.
  assert (Equal : (source ord_max == source position) = false).
  { apply /eqP. exact Different. }
  assert (Bound : (Legacy.Permute.depth position <= 16)%N = false).
  { apply Bool.not_true_is_false. intro Near.
    pose proof (elimT leP Near) as NearNat.
    change ((d - nat_of_ord position)%coq_nat <= 16)%coq_nat in NearNat.
    unfold addn, muln, subn in *. lia. }
  rewrite Equal Bound. reflexivity.
Qed.

Lemma model_swap_uint d source (position : 'I_(S d)) :
  (forall index, uint (Z.of_nat (source index))) ->
  forall index, uint (Z.of_nat (model_swap source position index)).
Proof. intros Values index. apply Values. Qed.

Lemma model_initial_budget d (p : model_permutation (S d)) :
  (S (model_rank p) <= 2 * S d)%coq_nat.
Proof. exact (elimT leP (rank_bound p)). Qed.

Lemma model_permute_normalized d source (p q : model_permutation (S d)) :
  model_normalize source p = Some q -> model_permute source p = Some (model_nonempty source q).
Proof.
  intro Normalized. unfold model_normalize in Normalized.
  unfold model_permute, solc_permute. rewrite Normalized. reflexivity.
Qed.

Print Assumptions model_chosen_bounds.
Print Assumptions model_run_done.
Print Assumptions model_run_equal.
Print Assumptions model_run_near.
Print Assumptions model_run_blocked.
Print Assumptions model_swap_uint.
Print Assumptions model_initial_budget.
Print Assumptions model_permute_normalized.
