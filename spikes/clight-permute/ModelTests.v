(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
From Legacy Require Import Permute Compute.
Require Import SolcModel ModelProofs.
Set Implicit Arguments.
Open Scope group_scope.

Definition zero3 : 'I_3 := @Ordinal 3 0 erefl.
Definition one3 : 'I_3 := @Ordinal 3 1 erefl.
Definition two3 : 'I_3 := @Ordinal 3 2 erefl.

Definition raw_values (s : 'I_3 -> nat) (p : 'S_3) :=
  if raw_normalize s p is Some q then Some [seq val (q i) | i <- enum 'I_3]
  else None.

Example first_free_reserves_equal_positions :
  first_free (fun _ : 'I_3 => 7) 7 [set zero3] [:: zero3; one3; two3] = Some one3.
Proof. by rewrite /first_free !inE; vm_compute. Qed.

Example first_free_no_candidate :
  first_free (fun _ : 'I_3 => 7) 9 set0 [:: zero3; one3; two3] = None.
Proof. by rewrite /first_free !inE; vm_compute. Qed.

Example normalize_equal_values :
  raw_values (fun _ => 7) (tperm zero3 two3) = Some [:: 0%N; 1%N; 2%N].
Proof.
rewrite /raw_values /raw_normalize /target_of /comp.
rewrite !enum_ordSl ?enum_ord0 /raw_fill /first_free /fixed_values !inE.
repeat (progress (rewrite ?inE /=)).
by vm_compute.
Qed.

Example suppress_equal_swap :
  solc_run 2 (fun _ : 'I_3 => 7%N) (tperm zero3 two3) [::] =
  SolcDone (fun _ => 7) 1 [::].
Proof.
rewrite /solc_run /choose /exchange /last_moved.
rewrite !enum_ordSl ?enum_ord0.
repeat (progress (rewrite ?permM ?tperm_eval ?invgK /= /bump)).
have H : (tperm ord_max zero3 * tperm zero3 two3 = 1)%g.
  have Etop : (ord_max : 'I_3) = two3 by apply: val_inj.
  rewrite Etop.
  rewrite [tperm two3 zero3]tpermC.
  have K := mulgV (tperm zero3 two3); by rewrite tpermV in K.
by rewrite H.
Qed.

Print Assumptions normalize_equal_values.
Print Assumptions suppress_equal_swap.
