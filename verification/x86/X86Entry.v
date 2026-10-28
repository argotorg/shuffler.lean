(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Control.
Open Scope Z_scope.

Lemma code_address_range layout code (frame : call_frame layout code) offset :
  (offset < List.length code)%nat ->
  0 <= entry_pc frame + Z.of_nat offset < address_modulus.
Proof.
  intro Offset. pose proof (frame_code_bounds layout code frame). lia.
Qed.

Lemma code_address_not_return layout code (frame : call_frame layout code) offset :
  (offset < List.length code)%nat ->
  machine_address (entry_pc frame + Z.of_nat offset) <>
    machine_address (return_pc frame).
Proof.
  intro Offset.
  pose proof (code_address_range layout code frame offset Offset) as Code.
  pose proof (frame_return_bounds layout code frame) as Return.
  pose proof (frame_return_outside layout code frame) as Outside.
  intro Equal. apply (f_equal (@bv_unsigned 64)) in Equal.
  unfold machine_address in Equal.
  rewrite !Z_to_bv_small in Equal by assumption. lia.
Qed.

Lemma instruction_before_return layout code (frame : call_frame layout code) offset state :
  (offset < List.length code)%nat ->
  read_reg_seq_state rip state =
    Some (machine_address (entry_pc frame + Z.of_nat offset)) ->
  ~ archState.is_terminated (return_condition (machine_address (return_pc frame))) (sst state).
Proof.
  intros Offset PC. eapply not_at_return; [exact PC|].
  apply code_address_not_return, Offset.
Qed.

Lemma code_at_register_write reg value state base code :
  code_at state base code -> code_at (write_reg_seq_state reg value state) base code.
Proof.
  intros Code k byte At. exact (Code k byte At).
Qed.

Lemma returned_state_terminates layout code (frame : call_frame layout code)
    before after result :
  abi_return layout code frame before after result ->
  archState.is_terminated (return_condition (machine_address (return_pc frame))) (sst after).
Proof.
  intro Returned. apply return_condition_iff.
  exact (return_rip layout code frame before after result Returned).
Qed.

Print Assumptions instruction_before_return.
Print Assumptions code_at_register_write.
Print Assumptions returned_state_terminates.
