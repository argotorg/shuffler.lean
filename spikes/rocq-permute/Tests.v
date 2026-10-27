(* SPDX-License-Identifier: GPL-3.0-or-later *)
From mathcomp Require Import all_boot all_fingroup.
Require Import Permute Compute.

Set Implicit Arguments.
Open Scope group_scope.
Open Scope nat_scope.

Definition below_top : 'S_3 := tperm ord0 (@Ordinal 3 1 erefl).

Example empty_stack : @permute nat 0 (fun i => val i) 1%g = Done (fun i => val i) [::].
Proof. by vm_compute. Qed.

Example identity : summary (@permute nat 3 val 1%g) =
    Success [:: 0; 1; 2] [::].
Proof. evaluate_perm. Qed.

Example top_swap : summary (@permute nat 3 val (tperm ord0 ord_max)) =
    Success [:: 2; 1; 0] [:: 2].
Proof. evaluate_perm. Qed.

Example below_top_swap : summary (@permute nat 3 val below_top) =
    Success [:: 1; 0; 2] [:: 1; 2; 1].
Proof. rewrite /below_top; evaluate_perm. Qed.

Example equal_values_still_swap : summary (@permute nat 3 (fun _ => 7) below_top) =
    Success [:: 7; 7; 7] [:: 1; 2; 1].
Proof. rewrite /below_top; evaluate_perm. Qed.

Example depth_sixteen : summary (@permute nat 17 val
    (tperm ord0 ord_max)) =
    Success ([:: 16] ++ iota 1 15 ++ [:: 0]) [:: 16].
Proof. evaluate_perm. Qed.

Example depth_seventeen_blocks : summary (@permute nat 18 val
    (tperm ord0 ord_max)) = Failure 1.
Proof. evaluate_perm. Qed.

Example fixed_top_unreachable_cycle : summary (@permute nat 19 val
    (tperm ord0 (@Ordinal 19 1 erefl))) = Failure 1.
Proof. evaluate_perm. Qed.
