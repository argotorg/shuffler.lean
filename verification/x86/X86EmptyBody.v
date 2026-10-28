(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86Decoded
  X86Compare X86Alu X86Flags X86Data X86StackMemory.
Import ListNotations.
Open Scope Z_scope.

Definition empty_pc (state : seq_state) (base offset : Z) : seq_state :=
  write_reg_seq_state rip (machine_address (base + offset)) state.

Lemma empty_cmp_zero_step nondet layout (frame : call_frame layout program_bytes)
    state offset old :
  In offset [37; 55] ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 0 ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (empty_pc state (entry_pc frame) (offset + 3))) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = true /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = false.
Proof.
  intros Site Code Present PC Old Low.
  destruct (Present rflags) as [flags Flags].
  pose (next := empty_pc state (entry_pc frame) (offset + 3)).
  assert (OldNext : read_reg_seq_state rdi next = Some old).
  { unfold next, empty_pc. rewrite register_read_frame by discriminate. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, empty_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm8 nondet 7 next old flags (Z_to_bv 8 0) OldNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  change (@sign_extend 8 (Z_to_bv 8 0) 32) with (Z_to_bv 32 0) in Execute.
  exists (result_flags flags
    (sign_flag32 (@sub_vec 32 (Z_to_bv 32 0) (Z_to_bv 32 0))) overflow carry
    (zero_flag32 (@sub_vec 32 (Z_to_bv 32 0) (Z_to_bv 32 0))) auxiliary parity).
  split.
  - eapply framed_instruction with (offset := offset) (size := 3)
      (instruction := CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM8 (Z_to_bv 8 0))));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [<-|[<-|Impossible]]; [vm_compute; tauto|vm_compute; tauto|contradiction].
    + destruct Site as [<-|[<-|Impossible]]; [destruct nondet; reflexivity|destruct nondet; reflexivity|contradiction].
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + 3) with (entry_pc frame + (offset + 3)) by lia.
      exact Execute.
  - split; [apply comparison_jns|apply comparison_jne]; lia.
Qed.

Lemma empty_cmp_bound_step nondet layout (frame : call_frame layout program_bytes)
    state old :
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 47)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 0 ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (empty_pc state (entry_pc frame) 53)) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = false.
Proof.
  intros Code Present PC Old Low.
  destruct (Present rflags) as [flags Flags].
  pose (next := empty_pc state (entry_pc frame) 53).
  assert (OldNext : read_reg_seq_state rdi next = Some old).
  { unfold next, empty_pc. rewrite register_read_frame by discriminate. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, empty_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm32 nondet 7 next old flags (Z_to_bv 32 1025) OldNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  exists (result_flags flags
    (sign_flag32 (@sub_vec 32 (Z_to_bv 32 0) (Z_to_bv 32 1025))) overflow carry
    (zero_flag32 (@sub_vec 32 (Z_to_bv 32 0) (Z_to_bv 32 1025))) auxiliary parity).
  split.
  - eapply framed_instruction with (offset := 47) (size := 6)
      (instruction := CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM32 (Z_to_bv 32 1025))));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 47 + 6) with (entry_pc frame + 53) by lia.
      exact Execute.
  - apply comparison_jns; lia.
Qed.

Print Assumptions empty_cmp_zero_step.
Print Assumptions empty_cmp_bound_step.

Record empty_body_result base (initial final : seq_state) : Prop := {
  empty_body_pc : read_reg_seq_state rip final = Some (machine_address (base + 428));
  empty_body_rax : read_reg_seq_state rax final = Some (Z_to_bv 64 0);
  empty_body_other : forall reg, reg <> rip -> reg <> rflags -> reg <> rax ->
    read_reg_seq_state reg final = read_reg_seq_state reg initial;
  empty_body_memory : archState.memory (sst final) = archState.memory (sst initial);
  empty_body_written : written final = written initial;
  empty_body_present : registers_present final;
  empty_body_code : code_at final base program_bytes
}.

Ltac unfold_empty_states :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold empty_pc.

Ltac empty_reads :=
  unfold_empty_states;
  repeat first [rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Ltac empty_code :=
  unfold_empty_states; repeat apply code_at_register_write; assumption.

Ltac empty_present :=
  unfold_empty_states; repeat apply registers_present_write; assumption.

Theorem empty_body_path nondet layout (frame : call_frame layout program_bytes)
    state old :
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 37)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 0 ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 9 state final /\
    empty_body_result (entry_pc frame) state final.
Proof.
  intros Code Present PC Old Low.
  destruct (empty_cmp_zero_step nondet layout frame state 37 old
    ltac:(left; reflexivity) Code Present PC Old Low)
    as [f1 [Step1 [Sign1 Zero1]]].
  pose (s1 := write_reg_seq_state rflags f1 (empty_pc state (entry_pc frame) 40)).
  change (instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1) in Step1.
  pose (s2 := empty_pc s1 (entry_pc frame) 47).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { eapply framed_instruction with (offset := 40) (size := 2)
      (instruction := JNS (Z_to_bv 8 5)).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 40 + 2) with (entry_pc frame + 42) by lia.
      erewrite execute_jns with (pc := machine_address (entry_pc frame + 42)) (flags := f1).
      + rewrite Sign1.
        change (@sign_extend 8 (Z_to_bv 8 5) 64) with (Z_to_bv 64 5).
        change (@add_vec 64 (machine_address (entry_pc frame + 42)) (Z_to_bv 64 5))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 42)) 5).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 42 + 5) with (entry_pc frame + 47) by lia.
        reflexivity.
      + apply register_read_written.
      + empty_reads. reflexivity. }
  assert (Code2 : code_at s2 (entry_pc frame) program_bytes) by empty_code.
  assert (Present2 : registers_present s2) by empty_present.
  assert (PC2 : read_reg_seq_state rip s2 = Some (machine_address (entry_pc frame + 47)))
    by (empty_reads; reflexivity).
  assert (Old2 : read_reg_seq_state rdi s2 = Some old) by (empty_reads; exact Old).
  destruct (empty_cmp_bound_step nondet layout frame s2 old Code2 Present2 PC2 Old2 Low)
    as [f2 [Step3 Sign2]].
  pose (s3 := write_reg_seq_state rflags f2 (empty_pc s2 (entry_pc frame) 53)).
  change (instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s2 s3) in Step3.
  pose (s4 := empty_pc s3 (entry_pc frame) 55).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { eapply framed_instruction with (offset := 53) (size := 2)
      (instruction := JNS (Z_to_bv 8 10)).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 53 + 2) with (entry_pc frame + 55) by lia.
      erewrite execute_jns with (pc := machine_address (entry_pc frame + 55)) (flags := f2).
      + rewrite Sign2. reflexivity.
      + apply register_read_written.
      + empty_reads. reflexivity. }
  assert (Code4 : code_at s4 (entry_pc frame) program_bytes) by empty_code.
  assert (Present4 : registers_present s4) by empty_present.
  assert (PC4 : read_reg_seq_state rip s4 = Some (machine_address (entry_pc frame + 55)))
    by (empty_reads; reflexivity).
  assert (Old4 : read_reg_seq_state rdi s4 = Some old) by (empty_reads; exact Old).
  destruct (empty_cmp_zero_step nondet layout frame s4 55 old
    ltac:(right; left; reflexivity) Code4 Present4 PC4 Old4 Low)
    as [f3 [Step5 [Sign3 Zero3]]].
  pose (s5 := write_reg_seq_state rflags f3 (empty_pc s4 (entry_pc frame) 58)).
  change (instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s4 s5) in Step5.
  pose (s6 := empty_pc s5 (entry_pc frame) 60).
  assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s5 s6).
  { eapply framed_instruction with (offset := 58) (size := 2)
      (instruction := JNE (Z_to_bv 8 10)).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 58 + 2) with (entry_pc frame + 60) by lia.
      erewrite execute_jne with (pc := machine_address (entry_pc frame + 60)) (flags := f3).
      + rewrite Zero3. reflexivity.
      + apply register_read_written.
      + empty_reads. reflexivity. }
  pose (s7 := empty_pc s6 (entry_pc frame) 419).
  assert (Step7 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s6 s7).
  { eapply framed_instruction with (offset := 60) (size := 5)
      (instruction := JMP32 (Z_to_bv 32 354)).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 60 + 5) with (entry_pc frame + 65) by lia.
      erewrite execute_jmp32 with (pc := machine_address (entry_pc frame + 65)).
      + change (@sign_extend 32 (Z_to_bv 32 354) 64) with (Z_to_bv 64 354).
        change (@add_vec 64 (machine_address (entry_pc frame + 65)) (Z_to_bv 64 354))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 65)) 354).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 65 + 354) with (entry_pc frame + 419) by lia.
        reflexivity.
      + apply register_read_written. }
  pose (s8 := write_reg_seq_state rflags (xor_zero_flags f3)
    (write_reg_seq_state rax (Z_to_bv 64 0) (empty_pc s7 (entry_pc frame) 421))).
  assert (Step8 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s7 s8).
  { eapply framed_instruction with (offset := 419) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0))).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 419 + 2) with (entry_pc frame + 421) by lia.
      destruct (Present rax) as [rax_old Rax].
      apply (execute_xor32_self nondet 0 _ rax_old f3).
      + discriminate.
      + change (read_reg_seq_state rax
          (write_reg_seq_state rip (machine_address (entry_pc frame + 421)) s7) = Some rax_old).
        empty_reads. exact Rax.
      + empty_reads. reflexivity. }
  pose (s9 := empty_pc s8 (entry_pc frame) 428).
  assert (Step9 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s8 s9).
  { eapply framed_instruction with (offset := 421) (size := 2)
      (instruction := JMP (Z_to_bv 8 5)).
    - empty_code.
    - empty_present.
    - empty_reads. reflexivity.
    - vm_compute; tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 421 + 2) with (entry_pc frame + 423) by lia.
      erewrite execute_jmp8 with (pc := machine_address (entry_pc frame + 423)).
      + change (@sign_extend 8 (Z_to_bv 8 5) 64) with (Z_to_bv 64 5).
        change (@add_vec 64 (machine_address (entry_pc frame + 423)) (Z_to_bv 64 5))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 423)) 5).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 423 + 5) with (entry_pc frame + 428) by lia.
        reflexivity.
      + apply register_read_written. }
  exists s9. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 8%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 7%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 6%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step4|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step5|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step6|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step7|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step8|exact Step9].
  - constructor.
    + empty_reads. reflexivity.
    + empty_reads. reflexivity.
    + intros reg NotPC NotFlags NotRax. unfold_empty_states.
      repeat rewrite register_read_frame by congruence. reflexivity.
    + unfold_empty_states. reflexivity.
    + unfold_empty_states. reflexivity.
    + empty_present.
    + empty_code.
Qed.

Print Assumptions empty_body_path.
