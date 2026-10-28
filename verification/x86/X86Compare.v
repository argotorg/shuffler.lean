(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import MachineWord Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Instructions X86Flags X86Arithmetic X86Data X86Sail.
Import ListNotations.

Lemma flag_write_trace nondet state flags (update : bv 64 -> bv 64) :
  read_reg_seq_state rflags state = Some flags ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86_types.Defs.bind
      (Tiny_x86_types.Defs.read_reg (e := unit) rflags)
      (fun old => Tiny_x86_types.Defs.write_reg rflags (update old))))
    state (write_reg_seq_state rflags (update flags) state) tt.
Proof.
  intro Read. eapply trace_sail_bind.
  - apply sail_read_reg_trace, Read.
  - apply sail_write_reg_trace with (old := flags), Read.
Qed.

Definition sign_flag32 (value : bv 32) : bv 1 :=
  vec_of_bits [@access_vec_dec 32 value 31].

Lemma sign_update32_trace nondet state flags value :
  read_reg_seq_state rflags state = Some flags ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86.update_sign_flag 32 value))
    state (write_reg_seq_state rflags
      (_update_rflags_type_SF flags (sign_flag32 value)) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_sign_flag.
  exact (flag_write_trace nondet state flags
    (fun f => _update_rflags_type_SF f (sign_flag32 value)) Read).
Qed.

Definition zero_flag32 (value : bv 32) : bv 1 :=
  if @eq_vec 32 value (Z_to_bv 32 0) then Z_to_bv 1 1 else Z_to_bv 1 0.

Lemma zero_update32_trace nondet state flags value :
  read_reg_seq_state rflags state = Some flags ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86.update_zero_flag 32 value))
    state (write_reg_seq_state rflags
      (_update_rflags_type_ZF flags (zero_flag32 value)) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_zero_flag.
  exact (flag_write_trace nondet state flags
    (fun f => _update_rflags_type_ZF f (zero_flag32 value)) Read).
Qed.

Lemma overflow_update32_trace nondet state flags (first second result : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.update_overflow_flag_sub 32 first second result))
    state (write_reg_seq_state rflags (_update_rflags_type_OF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_overflow_flag_sub,
    Tiny_x86.update_overflow_flag_add_inner.
  exists (if andb (@eq_vec 1 (@access_vec_dec 32 first 31)
      (flip_bit (@access_vec_dec 32 second 31)))
      (negb (@eq_vec 1 (@access_vec_dec 32 result 31) (@access_vec_dec 32 first 31)))
    then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_OF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_OF f bit) Read)
  end.
Qed.

Lemma carry_update32_trace nondet state flags (first second : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (@Tiny_x86.update_carry_flag_sub 32 first second))
    state (write_reg_seq_state rflags (_update_rflags_type_CF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_carry_flag_sub.
  exists (if Z.ltb (@uint 32 first) (@uint 32 second) then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_CF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_CF f bit) Read)
  end.
Qed.

Lemma auxiliary_update32_trace nondet state flags (first second : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (@Tiny_x86.update_aux_carry_flag_sub 32 first second))
    state (write_reg_seq_state rflags (_update_rflags_type_AF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_aux_carry_flag_sub.
  exists (if Z.ltb (@uint 4 (@subrange_vec_dec 32 first 3 0))
    (@uint 4 (@subrange_vec_dec 32 second 3 0)) then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_AF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_AF f bit) Read)
  end.
Qed.

Lemma parity_update32_trace nondet state flags (result : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (@Tiny_x86.update_parity_flag 32 result))
    state (write_reg_seq_state rflags (_update_rflags_type_PF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_parity_flag.
  match goal with
  | |- context [update_subrange_vec_dec _ 2 2 ?value] => exists value
  end.
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_PF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_PF f bit) Read)
  end.
Qed.

Print Assumptions sign_update32_trace.
Print Assumptions zero_update32_trace.
Print Assumptions overflow_update32_trace.
Print Assumptions carry_update32_trace.
Print Assumptions auxiliary_update32_trace.
Print Assumptions parity_update32_trace.

Theorem comparison_flags32_trace nondet state flags (first second result : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    sail_trace nondet (iMon_from_Sail nondet
      (@Tiny_x86.update_rflags_sub 32 first second result)) state
      (write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity) state) tt.
Proof.
  intro Read.
  pose (f1 := _update_rflags_type_SF flags (sign_flag32 result)).
  pose proof (sign_update32_trace nondet state flags result Read) as Sign.
  destruct (overflow_update32_trace nondet (write_reg_seq_state rflags f1 state)
      f1 first second result (register_read_written rflags f1 state)) as [overflow Overflow].
  rewrite register_write_overwrite in Overflow.
  pose (f2 := _update_rflags_type_OF f1 overflow).
  destruct (carry_update32_trace nondet (write_reg_seq_state rflags f2 state)
      f2 first second (register_read_written rflags f2 state)) as [carry Carry].
  rewrite register_write_overwrite in Carry.
  pose (f3 := _update_rflags_type_CF f2 carry).
  pose proof (zero_update32_trace nondet (write_reg_seq_state rflags f3 state)
      f3 result (register_read_written rflags f3 state)) as Zero.
  rewrite register_write_overwrite in Zero.
  pose (f4 := _update_rflags_type_ZF f3 (zero_flag32 result)).
  destruct (auxiliary_update32_trace nondet (write_reg_seq_state rflags f4 state)
      f4 first second (register_read_written rflags f4 state)) as [auxiliary Auxiliary].
  rewrite register_write_overwrite in Auxiliary.
  pose (f5 := _update_rflags_type_AF f4 auxiliary).
  destruct (parity_update32_trace nondet (write_reg_seq_state rflags f5 state)
      f5 result (register_read_written rflags f5 state)) as [parity Parity].
  rewrite register_write_overwrite in Parity.
  exists overflow, carry, auxiliary, parity.
  unfold Tiny_x86.update_rflags_sub, Tiny_x86_types.Defs.bind0.
  eapply trace_sail_bind; [|exact Parity].
  eapply trace_sail_bind; [|exact Auxiliary].
  eapply trace_sail_bind; [|exact Zero].
  eapply trace_sail_bind; [|exact Carry].
  eapply trace_sail_bind; [exact Sign|exact Overflow].
Qed.

Print Assumptions comparison_flags32_trace.

Definition low_register32 index old : bv 32 :=
  @subrange_vec_dec 64 (Values.to_ty (gpr_reference index) old) 31 0.

Theorem execute_cmp32_registers nondet first_index second_index state first_old second_old flags :
  read_reg_seq_state (Values.reg (gpr_reference first_index)) state = Some first_old ->
  read_reg_seq_state (Values.reg (gpr_reference second_index)) state = Some second_old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @sub_vec 32 (low_register32 first_index first_old)
      (low_register32 second_index second_old) in
    sail_run nondet (Tiny_x86.execute
      (CMP (32, rm_REG (REG_NORMAL first_index), rmi_REG (REG_NORMAL second_index)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity) state, tt)] [].
Proof.
  intros First Second Flags.
  destruct (comparison_flags32_trace nondet state flags
      (low_register32 first_index first_old) (low_register32 second_index second_old)
      (@sub_vec 32 (low_register32 first_index first_old)
        (low_register32 second_index second_old)) Flags)
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_CMP, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind
    Tiny_x86.read_rm_operand_without_lock Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_without_lock Tiny_x86.read_rmi_operand_with_lock].
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet first_index state first_old First)|].
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet second_index state second_old Second)|].
  exact Trace.
Qed.

Print Assumptions execute_cmp32_registers.

Lemma comparison_sign a b flags overflow carry auxiliary parity :
  (0 <= a < 2147483648)%Z -> (0 <= b < 2147483648)%Z ->
  let result := @sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b) in
  _get_rflags_type_SF (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity) =
    Z_to_bv 1 (if Z.ltb a b then 1 else 0).
Proof.
  intros A B. cbn beta zeta. rewrite result_flags_sign.
  unfold sign_flag32. rewrite bits_singleton. apply compare32_sign; assumption.
Qed.

Lemma comparison_zero a b flags overflow carry auxiliary parity :
  (0 <= a < 4294967296)%Z -> (0 <= b < 4294967296)%Z ->
  let result := @sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b) in
  _get_rflags_type_ZF (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity) =
    Z_to_bv 1 (if Z.eqb a b then 1 else 0).
Proof.
  intros A B. cbn beta zeta. rewrite result_flags_zero.
  unfold zero_flag32. rewrite compare32_zero by assumption.
  destruct (Z.eqb a b); reflexivity.
Qed.

Lemma comparison_jns a b flags overflow carry auxiliary parity :
  (0 <= a < 2147483648)%Z -> (0 <= b < 2147483648)%Z ->
  let result := @sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b) in
  @eq_vec 1 (_get_rflags_type_SF
    (result_flags flags (sign_flag32 result) overflow carry
      (zero_flag32 result) auxiliary parity)) (Z_to_bv 1 0) = Z.leb b a.
Proof.
  intros A B. cbn beta zeta. rewrite comparison_sign by assumption.
  destruct (Z.ltb a b) eqn:Less; destruct (Z.leb b a) eqn:AtLeast;
    try reflexivity;
    apply Z.ltb_lt in Less || apply Z.ltb_ge in Less;
    apply Z.leb_le in AtLeast || apply Z.leb_gt in AtLeast; lia.
Qed.

Lemma comparison_jne a b flags overflow carry auxiliary parity :
  (0 <= a < 4294967296)%Z -> (0 <= b < 4294967296)%Z ->
  let result := @sub_vec 32 (Z_to_bv 32 a) (Z_to_bv 32 b) in
  @eq_vec 1 (_get_rflags_type_ZF
    (result_flags flags (sign_flag32 result) overflow carry
      (zero_flag32 result) auxiliary parity)) (Z_to_bv 1 0) = negb (Z.eqb a b).
Proof.
  intros A B. cbn beta zeta. rewrite comparison_zero by assumption.
  destruct (Z.eqb a b); reflexivity.
Qed.

Print Assumptions comparison_jns.
Print Assumptions comparison_jne.

Theorem execute_cmp32_imm8 nondet index state old flags immediate :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @sub_vec 32 (low_register32 index old) (@sign_extend 8 immediate 32) in
    sail_run nondet (Tiny_x86.execute
      (CMP (32, rm_REG (REG_NORMAL index), rmi_IMM (IMM8 immediate)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity) state, tt)] [].
Proof.
  intros Register Flags.
  destruct (comparison_flags32_trace nondet state flags (low_register32 index old)
      (@sign_extend 8 immediate 32)
      (@sub_vec 32 (low_register32 index old) (@sign_extend 8 immediate 32)) Flags)
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_CMP, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86_types.Defs.assert_exp'
    Tiny_x86.read_rm_operand_without_lock Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_without_lock Tiny_x86.read_rmi_operand_with_lock Tiny_x86.read_imm].
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet index state old Register)|].
  exact Trace.
Qed.

Theorem execute_cmp32_imm32 nondet index state old flags immediate :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @sub_vec 32 (low_register32 index old) immediate in
    sail_run nondet (Tiny_x86.execute
      (CMP (32, rm_REG (REG_NORMAL index), rmi_IMM (IMM32 immediate)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity) state, tt)] [].
Proof.
  intros Register Flags.
  destruct (comparison_flags32_trace nondet state flags (low_register32 index old)
      immediate (@sub_vec 32 (low_register32 index old) immediate) Flags)
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_CMP, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86_types.Defs.assert_exp'
    Tiny_x86.read_rm_operand_without_lock Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_without_lock Tiny_x86.read_rmi_operand_with_lock Tiny_x86.read_imm].
  rewrite sign_extend32.
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet index state old Register)|].
  exact Trace.
Qed.

Print Assumptions execute_cmp32_imm8.
Print Assumptions execute_cmp32_imm32.
