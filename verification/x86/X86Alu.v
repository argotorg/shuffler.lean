(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import MachineWord Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Instructions X86Flags X86Data X86Sail X86Compare.
Import ListNotations.

Lemma alu_interface_bind nondet {A B} (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) state middle value :
  sail_trace nondet (iMon_from_Sail nondet program) state middle value ->
  sail_run nondet (Tiny_x86_types.Interface.iMon_bind program next) state =
    sail_run nondet (next value) middle.
Proof. apply sail_run_bind. Qed.

Lemma alu_interface_assoc {A B C} (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) (last : B -> Tiny_x86_types.M C) :
  Tiny_x86_types.Interface.iMon_bind
    (Tiny_x86_types.Interface.iMon_bind program next) last =
  Tiny_x86_types.Interface.iMon_bind program
    (fun value => Tiny_x86_types.Interface.iMon_bind (next value) last).
Proof. apply sail_bind_assoc. Qed.

Definition gpr32_written index (value : bv 32) state :=
  write_reg_seq_state (Values.reg (gpr_reference index))
    (Values.from_ty (gpr_reference index) (@zero_extend 32 value 64)) state.

Lemma flags_after_gpr32 index value state flags :
  Values.reg (gpr_reference index) <> rflags ->
  read_reg_seq_state rflags state = Some flags ->
  read_reg_seq_state rflags (gpr32_written index value state) = Some flags.
Proof.
  intros Different Flags. unfold gpr32_written.
  rewrite register_read_frame by exact Different. exact Flags.
Qed.

Lemma xor32_self (value : bv 32) : @xor_vec 32 value value = Z_to_bv 32 0.
Proof.
  change (bv_xor value value = Z_to_bv 32 0). apply bv_eq.
  rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity.
Qed.

Definition xor_zero_flags flags :=
  _update_rflags_type_PF
    (_update_rflags_type_ZF
      (_update_rflags_type_SF
        (_update_rflags_type_CF
          (_update_rflags_type_OF flags (Z_to_bv 1 0)) (Z_to_bv 1 0))
        (Z_to_bv 1 0)) (Z_to_bv 1 1)) (Z_to_bv 1 1).

Lemma parity_zero_trace nondet state flags :
  read_reg_seq_state rflags state = Some flags ->
  sail_trace nondet (iMon_from_Sail nondet
    (@Tiny_x86.update_parity_flag 32 (Z_to_bv 32 0))) state
    (write_reg_seq_state rflags (_update_rflags_type_PF flags (Z_to_bv 1 1)) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_parity_flag.
  exact (flag_write_trace nondet state flags
    (fun f => _update_rflags_type_PF f (Z_to_bv 1 1)) Read).
Qed.

Theorem execute_xor32_self nondet index state old flags :
  Values.reg (gpr_reference index) <> rflags ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  read_reg_seq_state rflags state = Some flags ->
  sail_run nondet (Tiny_x86.execute
    (XOR (false, 32, rm_REG (REG_NORMAL index), rmi_REG (REG_NORMAL index)))) state =
    Exec.make [(write_reg_seq_state rflags (xor_zero_flags flags)
      (gpr32_written index (Z_to_bv 32 0) state), tt)] [].
Proof.
  intros Different Register Flags.
  unfold Tiny_x86.execute, Tiny_x86.execute_XOR, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_with_lock Tiny_x86.write_rm_operand_with_lock].
  unfold Tiny_x86_types.Defs.bind0, Tiny_x86_types.Defs.bind.
  cbn [Tiny_x86_types.Interface.iMon_bind].
  repeat rewrite alu_interface_assoc.
  cbn [Tiny_x86_types.Interface.iMon_bind].
  repeat erewrite alu_interface_bind by constructor.
  erewrite alu_interface_bind by exact (read_gpr32_trace nondet index state old Register).
  erewrite alu_interface_bind by exact (read_gpr32_trace nondet index state old Register).
  rewrite xor32_self.
  repeat rewrite alu_interface_assoc.
  erewrite alu_interface_bind by exact
    (write_gpr32_trace_single nondet index state old (Z_to_bv 32 0) Register).
  fold (gpr32_written index (Z_to_bv 32 0) state).
  pose proof (flags_after_gpr32 index (Z_to_bv 32 0) state flags Different Flags) as Read.
  erewrite alu_interface_bind by exact (@sail_read_reg_trace nondet rflags _ flags Read).
  repeat rewrite alu_interface_assoc.
  erewrite alu_interface_bind by exact (@sail_write_reg_trace nondet rflags _ flags _ Read).
  erewrite alu_interface_bind by
    (exact (@sail_read_reg_trace nondet rflags _ _ (register_read_written rflags _ _))).
  repeat rewrite alu_interface_assoc.
  erewrite alu_interface_bind by
    (exact (@sail_write_reg_trace nondet rflags _ _ _ (register_read_written rflags _ _))).
  rewrite register_write_overwrite.
  erewrite alu_interface_bind by
    (apply sign_update32_trace; apply register_read_written).
  rewrite register_write_overwrite.
  erewrite alu_interface_bind by
    (apply zero_update32_trace; apply register_read_written).
  rewrite register_write_overwrite.
  match goal with
  | |- sail_run _ _ (write_reg_seq_state ?reg ?value ?before) = _ =>
      pose proof (parity_zero_trace nondet _ value
        (register_read_written reg value before)) as Last
  end.
  rewrite register_write_overwrite in Last.
  apply sail_trace_run with (nondet := nondet). exact Last.
Qed.

Print Assumptions execute_xor32_self.

Lemma overflow_add32_trace nondet state flags (first second result : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.update_overflow_flag_add 32 first second result)) state
    (write_reg_seq_state rflags (_update_rflags_type_OF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_overflow_flag_add,
    Tiny_x86.update_overflow_flag_add_inner.
  exists (if andb (@eq_vec 1 (@access_vec_dec 32 first 31)
      (@access_vec_dec 32 second 31))
      (negb (@eq_vec 1 (@access_vec_dec 32 result 31) (@access_vec_dec 32 first 31)))
    then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_OF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_OF f bit) Read)
  end.
Qed.

Lemma carry_add32_trace nondet state flags (first second : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.update_carry_flag_add 32 first second)) state
    (write_reg_seq_state rflags (_update_rflags_type_CF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_carry_flag_add.
  exists (if Z.gtb (@uint 32 first + @uint 32 second) 4294967295
    then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_CF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_CF f bit) Read)
  end.
Qed.

Lemma auxiliary_add32_trace nondet state flags (first second : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists bit, sail_trace nondet (iMon_from_Sail nondet
    (@Tiny_x86.update_aux_carry_flag_add 32 first second)) state
    (write_reg_seq_state rflags (_update_rflags_type_AF flags bit) state) tt.
Proof.
  intro Read. unfold Tiny_x86.update_aux_carry_flag_add.
  exists (if Z.gtb (@uint 4 (@subrange_vec_dec 32 first 3 0) +
    @uint 4 (@subrange_vec_dec 32 second 3 0)) 15
    then Z_to_bv 1 1 else Z_to_bv 1 0).
  match goal with
  | |- sail_trace _ _ _ (write_reg_seq_state _ (_update_rflags_type_AF _ ?bit) _) _ =>
    exact (flag_write_trace nondet state flags (fun f => _update_rflags_type_AF f bit) Read)
  end.
Qed.

Theorem addition_flags32_trace nondet state flags (first second result : bv 32) :
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    sail_trace nondet (iMon_from_Sail nondet
      (@Tiny_x86.update_rflags_add 32 first second result)) state
      (write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity) state) tt.
Proof.
  intro Read.
  pose (f1 := _update_rflags_type_SF flags (sign_flag32 result)).
  pose proof (sign_update32_trace nondet state flags result Read) as Sign.
  destruct (overflow_add32_trace nondet (write_reg_seq_state rflags f1 state)
      f1 first second result (register_read_written rflags f1 state)) as [overflow Overflow].
  rewrite register_write_overwrite in Overflow.
  pose (f2 := _update_rflags_type_OF f1 overflow).
  destruct (carry_add32_trace nondet (write_reg_seq_state rflags f2 state)
      f2 first second (register_read_written rflags f2 state)) as [carry Carry].
  rewrite register_write_overwrite in Carry.
  pose (f3 := _update_rflags_type_CF f2 carry).
  pose proof (zero_update32_trace nondet (write_reg_seq_state rflags f3 state)
      f3 result (register_read_written rflags f3 state)) as Zero.
  rewrite register_write_overwrite in Zero.
  pose (f4 := _update_rflags_type_ZF f3 (zero_flag32 result)).
  destruct (auxiliary_add32_trace nondet (write_reg_seq_state rflags f4 state)
      f4 first second (register_read_written rflags f4 state)) as [auxiliary Auxiliary].
  rewrite register_write_overwrite in Auxiliary.
  pose (f5 := _update_rflags_type_AF f4 auxiliary).
  destruct (parity_update32_trace nondet (write_reg_seq_state rflags f5 state)
      f5 result (register_read_written rflags f5 state)) as [parity Parity].
  rewrite register_write_overwrite in Parity.
  exists overflow, carry, auxiliary, parity.
  unfold Tiny_x86.update_rflags_add, Tiny_x86_types.Defs.bind0.
  eapply trace_sail_bind; [|exact Parity].
  eapply trace_sail_bind; [|exact Auxiliary].
  eapply trace_sail_bind; [|exact Zero].
  eapply trace_sail_bind; [|exact Carry].
  eapply trace_sail_bind; [exact Sign|exact Overflow].
Qed.

Theorem execute_sub32_registers nondet destination source state old source_old flags :
  Values.reg (gpr_reference destination) <> rflags ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some source_old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @sub_vec 32 (low_register32 destination old)
      (low_register32 source source_old) in
    sail_run nondet (Tiny_x86.execute
      (SUB (false, 32, rm_REG (REG_NORMAL destination), rmi_REG (REG_NORMAL source)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity)
        (gpr32_written destination result state), tt)] [].
Proof.
  intros Different Destination Source Flags.
  pose (result := @sub_vec 32 (low_register32 destination old)
    (low_register32 source source_old)).
  destruct (comparison_flags32_trace nondet (gpr32_written destination result state) flags
    (low_register32 destination old) (low_register32 source source_old) result
    (flags_after_gpr32 destination result state flags Different Flags))
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_SUB, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_with_lock Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet destination state old Destination)|].
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet source state source_old Source)|].
  eapply trace_sail_bind; [exact (write_gpr32_trace_single nondet destination state old result Destination)|].
  exact Trace.
Qed.

Theorem execute_sub32_imm8 nondet destination state old flags immediate :
  Values.reg (gpr_reference destination) <> rflags ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @sub_vec 32 (low_register32 destination old) (@sign_extend 8 immediate 32) in
    sail_run nondet (Tiny_x86.execute
      (SUB (false, 32, rm_REG (REG_NORMAL destination), rmi_IMM (IMM8 immediate)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity)
        (gpr32_written destination result state), tt)] [].
Proof.
  intros Different Destination Flags.
  pose (result := @sub_vec 32 (low_register32 destination old) (@sign_extend 8 immediate 32)).
  destruct (comparison_flags32_trace nondet (gpr32_written destination result state) flags
    (low_register32 destination old) (@sign_extend 8 immediate 32) result
    (flags_after_gpr32 destination result state flags Different Flags))
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_SUB, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86_types.Defs.assert_exp'
    Tiny_x86.read_rm_operand_with_lock Tiny_x86.read_rmi_operand_with_lock
    Tiny_x86.read_imm Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet destination state old Destination)|].
  eapply trace_sail_bind; [exact (write_gpr32_trace_single nondet destination state old result Destination)|].
  exact Trace.
Qed.

Theorem execute_add32_registers nondet destination source state old source_old flags :
  Values.reg (gpr_reference destination) <> rflags ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some source_old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @add_vec 32 (low_register32 destination old)
      (low_register32 source source_old) in
    sail_run nondet (Tiny_x86.execute
      (ADD (false, 32, rm_REG (REG_NORMAL destination), rmi_REG (REG_NORMAL source)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity)
        (gpr32_written destination result state), tt)] [].
Proof.
  intros Different Destination Source Flags.
  pose (result := @add_vec 32 (low_register32 destination old)
    (low_register32 source source_old)).
  destruct (addition_flags32_trace nondet (gpr32_written destination result state) flags
    (low_register32 destination old) (low_register32 source source_old) result
    (flags_after_gpr32 destination result state flags Different Flags))
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_ADD, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86.read_rm_operand_with_lock
    Tiny_x86.read_rmi_operand_with_lock Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet destination state old Destination)|].
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet source state source_old Source)|].
  eapply trace_sail_bind; [exact (write_gpr32_trace_single nondet destination state old result Destination)|].
  exact Trace.
Qed.

Theorem execute_add32_imm8 nondet destination state old flags immediate :
  Values.reg (gpr_reference destination) <> rflags ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  read_reg_seq_state rflags state = Some flags ->
  exists overflow carry auxiliary parity,
    let result := @add_vec 32 (low_register32 destination old) (@sign_extend 8 immediate 32) in
    sail_run nondet (Tiny_x86.execute
      (ADD (false, 32, rm_REG (REG_NORMAL destination), rmi_IMM (IMM8 immediate)))) state =
      Exec.make [(write_reg_seq_state rflags
        (result_flags flags (sign_flag32 result) overflow carry
          (zero_flag32 result) auxiliary parity)
        (gpr32_written destination result state), tt)] [].
Proof.
  intros Different Destination Flags.
  pose (result := @add_vec 32 (low_register32 destination old) (@sign_extend 8 immediate 32)).
  destruct (addition_flags32_trace nondet (gpr32_written destination result state) flags
    (low_register32 destination old) (@sign_extend 8 immediate 32) result
    (flags_after_gpr32 destination result state flags Different Flags))
    as [overflow [carry [auxiliary [parity Trace]]]].
  exists overflow, carry, auxiliary, parity. cbn beta zeta.
  unfold Tiny_x86.execute, Tiny_x86.execute_ADD, Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86_types.Defs.assert_exp'
    Tiny_x86.read_rm_operand_with_lock Tiny_x86.read_rmi_operand_with_lock
    Tiny_x86.read_imm Tiny_x86.write_rm_operand_with_lock].
  repeat rewrite sail_bind_assoc.
  apply sail_trace_run with (nondet := nondet).
  eapply trace_sail_bind; [exact (read_gpr32_trace nondet destination state old Destination)|].
  eapply trace_sail_bind; [exact (write_gpr32_trace_single nondet destination state old result Destination)|].
  exact Trace.
Qed.

Print Assumptions addition_flags32_trace.
Print Assumptions execute_sub32_registers.
Print Assumptions execute_sub32_imm8.
Print Assumptions execute_add32_registers.
Print Assumptions execute_add32_imm8.
