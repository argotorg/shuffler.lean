(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Classical_Prop.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Flags X86Instructions.
Import ListNotations.

Lemma gpr_reference_inverse index value :
  Values.to_ty (gpr_reference index)
    (Values.from_ty (gpr_reference index) value) = value.
Proof.
  unfold gpr_reference, Tiny_x86.GPRs, Values.vec_access_dec,
    Values.access_list_dec, Values.access_list_inc, Values.length_list.
  cbn.
  change (Z.of_nat 16 - 1)%Z with 15%Z.
  destruct (15 - index <? 0)%Z; [reflexivity|].
  remember (Z.to_nat (15 - index)) as count.
  do 16 (destruct count as [|count]; [reflexivity|]).
  destruct count; reflexivity.
Qed.

Lemma read_gpr32_trace nondet index state old :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_GPR 32 (REG_NORMAL index))) state state
    (SailStdpp.Operators_mwords.subrange_vec_dec
      (Values.to_ty (gpr_reference index) old) 31 0).
Proof.
  intro Read. unfold Tiny_x86.read_GPR. cbn.
  econstructor.
  - exact (@register_read (Values.reg (gpr_reference index)) None state old Read).
  - constructor.
Qed.

Lemma write_gpr32_trace nondet index state old value :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_GPR 32 (REG_NORMAL index) value)) state
    (write_reg_seq_state (Values.reg (gpr_reference index))
      (Values.from_ty (gpr_reference index)
        (SailStdpp.Operators_mwords.zero_extend value 64))
      (write_reg_seq_state (Values.reg (gpr_reference index))
        (Values.from_ty (gpr_reference index)
          (SailStdpp.Operators_mwords.update_subrange_vec_dec
            (Values.to_ty (gpr_reference index) old) 63 32 (Z_to_bv 32 0))) state)) tt.
Proof.
  intro Read. unfold Tiny_x86.write_GPR. cbn.
  econstructor.
  - exact (@register_read (Values.reg (gpr_reference index)) None state old Read).
  - econstructor.
    + exact (@register_write (Values.reg (gpr_reference index)) None state old _ Read).
    + econstructor.
      * apply register_read. apply register_read_written.
      * change (sail_trace nondet (iMon_from_Sail nondet
          (Tiny_x86_types.Defs.write_reg_ref (e := unit) (gpr_reference index)
            (SailStdpp.Operators_mwords.update_subrange_vec_dec
              (Values.to_ty (gpr_reference index)
                (Values.from_ty (gpr_reference index)
                  (SailStdpp.Operators_mwords.update_subrange_vec_dec
                    (Values.to_ty (gpr_reference index) old) 63 32 (Z_to_bv 32 0))))
              31 0 value)))
          (write_reg_seq_state (Values.reg (gpr_reference index))
            (Values.from_ty (gpr_reference index)
              (SailStdpp.Operators_mwords.update_subrange_vec_dec
                (Values.to_ty (gpr_reference index) old) 63 32 (Z_to_bv 32 0))) state)
          (write_reg_seq_state (Values.reg (gpr_reference index))
            (Values.from_ty (gpr_reference index)
              (SailStdpp.Operators_mwords.zero_extend value 64))
            (write_reg_seq_state (Values.reg (gpr_reference index))
              (Values.from_ty (gpr_reference index)
                (SailStdpp.Operators_mwords.update_subrange_vec_dec
                  (Values.to_ty (gpr_reference index) old) 63 32 (Z_to_bv 32 0))) state)) tt).
        rewrite gpr_reference_inverse, update32_zero_extend.
        cbn. econstructor.
        -- eapply register_write. apply register_read_written.
        -- constructor.
Qed.

Lemma register_map_car_equal (before after : registerMap) :
  dmap_car before = dmap_car after -> before = after.
Proof.
  destruct before as [first First], after as [second Second]. cbn.
  intro Equal. subst second. f_equal.
  apply Stdlib.Logic.Classical_Prop.proof_irrelevance.
Qed.

Lemma register_map_overwrite (reg : Arch.reg) (old value : reg_type reg)
    (registers : registerMap) :
  dmap_insert reg value (dmap_insert reg old registers) = dmap_insert reg value registers.
Proof.
  apply register_map_car_equal. cbn. rewrite insert_insert. case_decide; congruence.
Qed.

Lemma register_write_overwrite reg old value state :
  write_reg_seq_state reg value (write_reg_seq_state reg old state) =
    write_reg_seq_state reg value state.
Proof.
  destruct state as [[memory space registers] changed].
  unfold write_reg_seq_state. cbn. unfold Setter_compose. cbn.
  f_equal. f_equal. apply vec_eq. intro index. inv_fin index.
  unfold Setter_valter. rewrite !vlookup_alter. apply register_map_overwrite.
  intro impossible. inv_fin impossible.
Qed.

Lemma write_gpr32_trace_single nondet index state old value :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_GPR 32 (REG_NORMAL index) value)) state
    (write_reg_seq_state (Values.reg (gpr_reference index))
      (Values.from_ty (gpr_reference index)
        (SailStdpp.Operators_mwords.zero_extend value 64)) state) tt.
Proof.
  intro Read. pose proof (write_gpr32_trace nondet index state old value Read) as Write.
  now rewrite register_write_overwrite in Write.
Qed.

Print Assumptions read_gpr32_trace.
Print Assumptions write_gpr32_trace_single.

Lemma sign_extend32 (value : bv 32) :
  @SailStdpp.Operators_mwords.sign_extend 32 value 32 = value.
Proof. change (bv_sign_extend 32 value = value). apply bv_sign_extend_idemp. Qed.

Lemma execute_mov32_registers nondet source destination state source_value old :
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some source_value ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_REG (REG_NORMAL destination), rmi_REG (REG_NORMAL source)))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination)
        (SailStdpp.Operators_mwords.zero_extend
          (SailStdpp.Operators_mwords.subrange_vec_dec
            (Values.to_ty (gpr_reference source) source_value) 31 0) 64)) state, tt)] [].
Proof.
  intros Source Destination.
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind
    Tiny_x86.read_rmi_operand_without_lock Tiny_x86.read_rmi_operand_with_lock
    Tiny_x86.write_rm_operand_without_lock Tiny_x86.write_rm_operand_with_lock].
  erewrite sail_run_bind by exact (read_gpr32_trace nondet source state source_value Source).
  apply sail_trace_run with (nondet := nondet).
  now apply write_gpr32_trace_single with (old := old).
Qed.

Lemma execute_mov32_immediate nondet destination state old value :
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_run nondet (Tiny_x86.execute
    (MOV (32, rm_REG (REG_NORMAL destination), rmi_IMM (IMM32 value)))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination)
        (SailStdpp.Operators_mwords.zero_extend value 64)) state, tt)] [].
Proof.
  intro Destination.
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands, Tiny_x86.read_rmi_operand_without_lock,
    Tiny_x86.read_rmi_operand_with_lock, Tiny_x86.read_imm.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind Tiny_x86_types.Defs.assert_exp'
    Tiny_x86.write_rm_operand_without_lock Tiny_x86.write_rm_operand_with_lock].
  rewrite sign_extend32.
  apply sail_trace_run with (nondet := nondet).
  now apply write_gpr32_trace_single with (old := old).
Qed.

Print Assumptions execute_mov32_registers.
Print Assumptions execute_mov32_immediate.
