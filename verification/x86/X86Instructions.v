(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Flags.
Import ListNotations.

Definition sail_run {A} (nondet : bool) (program : Tiny_x86_types.M A)
    : Exec.t seq_state string A :=
  FMon.cinterp (sequential_model_outcome None)
    (iMon_from_Sail nondet program).

Lemma register_read reg access state value :
  read_reg_seq_state reg state = Some value ->
  sequential_model_outcome None (RegRead reg access) state =
    Exec.make [(state, value)] [].
Proof.
  intro Read. simp sequential_model_outcome.
  unfold mget, mbind, Exec.mbind_inst, fmap, Exec.fmap_inst,
    Exec.res_fmap_inst, Exec.res_mbind_inst, mcall, Exec.st_call_MState.
  cbn. rewrite Read. reflexivity.
Qed.

Lemma register_write reg access state old value :
  read_reg_seq_state reg state = Some old ->
  sequential_model_outcome None (RegWrite reg access value) state =
    Exec.make [(write_reg_seq_state reg value state, tt)] [].
Proof.
  intro Read. simp sequential_model_outcome.
  unfold mget, mbind, Exec.mbind_inst, fmap, Exec.fmap_inst,
    Exec.res_fmap_inst, Exec.res_mbind_inst, mcall, Exec.st_call_MState.
  cbn. rewrite Read. reflexivity.
Qed.

Lemma execute_jmp8 nondet displacement state pc :
  read_reg_seq_state rip state = Some pc ->
  sail_run nondet (Tiny_x86.execute (JMP displacement)) state =
    Exec.make [(write_reg_seq_state rip
      (SailStdpp.Operators_mwords.add_vec pc
        (SailStdpp.Operators_mwords.sign_extend displacement 64)) state, tt)] [].
Proof.
  intro Read. unfold sail_run, Tiny_x86.execute, Tiny_x86.execute_JMP.
  cbn.
  erewrite exec_bind_single by exact (@register_read rip None state pc Read).
  erewrite exec_bind_single by exact (@register_write rip None state pc _ Read).
  reflexivity.
Qed.

Lemma execute_jmp32 nondet displacement state pc :
  read_reg_seq_state rip state = Some pc ->
  sail_run nondet (Tiny_x86.execute (JMP32 displacement)) state =
    Exec.make [(write_reg_seq_state rip
      (SailStdpp.Operators_mwords.add_vec pc
        (SailStdpp.Operators_mwords.sign_extend displacement 64)) state, tt)] [].
Proof.
  intro Read. unfold sail_run, Tiny_x86.execute, Tiny_x86.execute_JMP32.
  cbn.
  erewrite exec_bind_single by exact (@register_read rip None state pc Read).
  erewrite exec_bind_single by exact (@register_write rip None state pc _ Read).
  reflexivity.
Qed.

Lemma execute_jne nondet displacement state pc flags :
  read_reg_seq_state rip state = Some pc ->
  read_reg_seq_state rflags state = Some flags ->
  sail_run nondet (Tiny_x86.execute (JNE displacement)) state =
    Exec.make [(if SailStdpp.Operators_mwords.eq_vec
      (Tiny_x86._get_rflags_type_ZF flags) (Z_to_bv 1 0)
    then write_reg_seq_state rip
      (SailStdpp.Operators_mwords.add_vec pc
        (SailStdpp.Operators_mwords.sign_extend displacement 64)) state
    else state, tt)] [].
Proof.
  intros PC Flags. unfold sail_run, Tiny_x86.execute, Tiny_x86.execute_JNE.
  cbn.
  erewrite exec_bind_single by exact (@register_read rflags None state flags Flags).
  change (MachineWord.MachineWord.N_to_word 1 (0 + 0)) with (Z_to_bv 1 0).
  destruct (SailStdpp.Operators_mwords.eq_vec
    (Tiny_x86._get_rflags_type_ZF flags) (Z_to_bv 1 0)); [|reflexivity].
  now apply execute_jmp8.
Qed.

Lemma execute_jns nondet displacement state pc flags :
  read_reg_seq_state rip state = Some pc ->
  read_reg_seq_state rflags state = Some flags ->
  sail_run nondet (Tiny_x86.execute (JNS displacement)) state =
    Exec.make [(if SailStdpp.Operators_mwords.eq_vec
      (Tiny_x86._get_rflags_type_SF flags) (Z_to_bv 1 0)
    then write_reg_seq_state rip
      (SailStdpp.Operators_mwords.add_vec pc
        (SailStdpp.Operators_mwords.sign_extend displacement 64)) state
    else state, tt)] [].
Proof.
  intros PC Flags. unfold sail_run, Tiny_x86.execute, Tiny_x86.execute_JNS.
  cbn.
  erewrite exec_bind_single by exact (@register_read rflags None state flags Flags).
  change (MachineWord.MachineWord.N_to_word 1 (0 + 0)) with (Z_to_bv 1 0).
  destruct (SailStdpp.Operators_mwords.eq_vec
    (Tiny_x86._get_rflags_type_SF flags) (Z_to_bv 1 0)); [|reflexivity].
  now apply execute_jmp8.
Qed.

Lemma register_read_written reg value state :
  read_reg_seq_state reg (write_reg_seq_state reg value state) = Some value.
Proof.
  unfold read_reg_seq_state, write_reg_seq_state.
  destruct state as [[memory space registers] changed]. cbn.
  unfold Setter_valter. rewrite vlookup_alter. apply dmap_lookup_insert.
Qed.

Lemma register_read_frame reg other value state :
  reg <> other ->
  read_reg_seq_state other (write_reg_seq_state reg value state) =
    read_reg_seq_state other state.
Proof.
  intro Different. unfold read_reg_seq_state, write_reg_seq_state.
  destruct state as [[memory space registers] changed]. cbn.
  unfold Setter_valter. rewrite vlookup_alter. now apply dmap_lookup_insert_ne.
Qed.

Lemma sail_adapter_bind nondet {A B} (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) :
  iMon_from_Sail nondet (Tiny_x86_types.Defs.bind program next) =
    (iMon_from_Sail nondet program ≫= fun value => iMon_from_Sail nondet (next value)).
Proof.
  induction program as [value|T outcome resume IH]; cbn.
  - reflexivity.
  - rewrite <- monad_assoc. f_equal. apply functional_extensionality.
    intro value. apply IH.
Qed.

(* A successful trace requires one result at each event. This excludes error
   branches and is the condition needed to compose exact Exec results. *)
Inductive sail_trace {A} (nondet : bool) :
    iMon A -> seq_state -> seq_state -> A -> Prop :=
| sail_trace_return value state :
    sail_trace nondet (FMon.Ret value) state state value
| sail_trace_next call resume state middle final answer value :
    (sequential_model_outcome None +ₕ mcall_fHandler) call state =
      Exec.make [(middle, answer)] [] ->
    sail_trace nondet (resume answer) middle final value ->
    sail_trace nondet (FMon.Next call resume) state final value.

Lemma sail_trace_run {A} nondet (program : iMon A) state final value :
  sail_trace nondet program state final value ->
  FMon.cinterp (sequential_model_outcome None) program state =
    Exec.make [(final, value)] [].
Proof.
  intro Trace. induction Trace; [reflexivity|].
  cbn [FMon.cinterp FMon.finterp].
  erewrite exec_bind_single by exact H. exact IHTrace.
Qed.

Lemma sail_trace_bind {A B} nondet (program : iMon A)
    (next : A -> iMon B) state final value :
  sail_trace nondet program state final value ->
  FMon.cinterp (sequential_model_outcome None) (program ≫= next) state =
    FMon.cinterp (sequential_model_outcome None) (next value) final.
Proof.
  intro Trace. induction Trace; [reflexivity|].
  cbn [mbind FMon.fMon_bind FMon.cinterp FMon.finterp].
  erewrite exec_bind_single by exact H. exact IHTrace.
Qed.

Lemma sail_run_bind {A B} nondet (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) state final value :
  sail_trace nondet (iMon_from_Sail nondet program) state final value ->
  sail_run nondet (Tiny_x86_types.Defs.bind program next) state =
    sail_run nondet (next value) final.
Proof.
  intro Trace. unfold sail_run. rewrite sail_adapter_bind.
  exact (@sail_trace_bind A B nondet (iMon_from_Sail nondet program)
    (fun value => iMon_from_Sail nondet (next value)) state final value Trace).
Qed.

Lemma sail_read_reg_trace nondet reg state value :
  read_reg_seq_state reg state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86_types.Defs.read_reg (e := unit) reg))
    state state value.
Proof.
  intro Read. cbn. econstructor.
  - exact (@register_read reg None state value Read).
  - constructor.
Qed.

Lemma sail_write_reg_trace nondet reg state old value :
  read_reg_seq_state reg state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86_types.Defs.write_reg (e := unit) reg value))
    state (write_reg_seq_state reg value state) tt.
Proof.
  intro Read. cbn. econstructor.
  - exact (@register_write reg None state old value Read).
  - constructor.
Qed.

Theorem fetch_execute_decoded nondet state pc next_pc instr final :
  read_reg_seq_state rip state = Some pc ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86.decode pc))
    state state (Some (next_pc, instr)) ->
  sail_run nondet (Tiny_x86.execute instr)
    (write_reg_seq_state rip next_pc state) = Exec.make [(final, tt)] [] ->
  instruction_step (sail_tiny_x86_sem nondet) state = Exec.make [(final, tt)] [].
Proof.
  intros PC Decode Execute.
  change (sail_run nondet (Tiny_x86.fetch_execute tt) state =
    Exec.make [(final, tt)] []).
  unfold Tiny_x86.fetch_execute.
  erewrite sail_run_bind by exact (@sail_read_reg_trace nondet rip state pc PC).
  erewrite sail_run_bind by exact Decode.
  cbn beta iota zeta. unfold Tiny_x86_types.Defs.bind0.
  erewrite sail_run_bind by exact (@sail_write_reg_trace nondet rip state pc next_pc PC).
  exact Execute.
Qed.

Print Assumptions execute_jmp8.
Print Assumptions execute_jmp32.
Print Assumptions execute_jne.
Print Assumptions execute_jns.
Print Assumptions register_read_written.
Print Assumptions register_read_frame.
Print Assumptions fetch_execute_decoded.

Definition gpr_reference (index : Z) := Values.vec_access_dec Tiny_x86.GPRs index.

Lemma read_gpr64_trace nondet index state old :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_GPR 64 (REG_NORMAL index))) state state
    (Values.to_ty (gpr_reference index) old).
Proof.
  intro Read. unfold Tiny_x86.read_GPR. cbn.
  econstructor.
  - exact (@register_read (Values.reg (gpr_reference index)) None state old Read).
  - change (sail_trace nondet (FMon.Ret
      (SailStdpp.Operators_mwords.subrange_vec_dec
        (Values.to_ty (gpr_reference index) old) 63 0)) state state
      (Values.to_ty (gpr_reference index) old)).
    rewrite subrange64. constructor.
Qed.

Lemma write_gpr64_trace nondet index state old value :
  read_reg_seq_state (Values.reg (gpr_reference index)) state = Some old ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_GPR 64 (REG_NORMAL index) value)) state
    (write_reg_seq_state (Values.reg (gpr_reference index))
      (Values.from_ty (gpr_reference index) value) state) tt.
Proof.
  intro Read. unfold Tiny_x86.write_GPR. cbn.
  econstructor.
  - exact (@register_read (Values.reg (gpr_reference index)) None state old Read).
  - change (sail_trace nondet (iMon_from_Sail nondet
      (Tiny_x86_types.Defs.write_reg_ref (e := unit) (gpr_reference index)
        (SailStdpp.Operators_mwords.update_subrange_vec_dec
          (Values.to_ty (gpr_reference index) old) 63 0 value))) state
      (write_reg_seq_state (Values.reg (gpr_reference index))
        (Values.from_ty (gpr_reference index) value) state) tt).
    rewrite update64. cbn. econstructor.
    + exact (@register_write (Values.reg (gpr_reference index)) None state old
        (Values.from_ty (gpr_reference index) value) Read).
    + constructor.
Qed.

Lemma execute_mov64_registers nondet source destination state source_value old :
  read_reg_seq_state (Values.reg (gpr_reference source)) state = Some source_value ->
  read_reg_seq_state (Values.reg (gpr_reference destination)) state = Some old ->
  sail_run nondet (Tiny_x86.execute
    (MOV (64, rm_REG (REG_NORMAL destination), rmi_REG (REG_NORMAL source)))) state =
    Exec.make [(write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination)
        (Values.to_ty (gpr_reference source) source_value)) state, tt)] [].
Proof.
  intros Source Destination.
  unfold Tiny_x86.execute, Tiny_x86.execute_MOV,
    Tiny_x86.fail_if_two_mem_operands.
  cbn [Tiny_x86_types.Defs.bind0 Tiny_x86_types.Defs.bind
    Tiny_x86_types.Interface.iMon_bind
    Tiny_x86.read_rmi_operand_without_lock Tiny_x86.read_rmi_operand_with_lock
    Tiny_x86.write_rm_operand_without_lock Tiny_x86.write_rm_operand_with_lock].
  erewrite sail_run_bind by exact (read_gpr64_trace nondet source state source_value Source).
  apply sail_trace_run with (nondet := nondet). now apply write_gpr64_trace with (old := old).
Qed.

Print Assumptions read_gpr64_trace.
Print Assumptions write_gpr64_trace.
Print Assumptions execute_mov64_registers.
