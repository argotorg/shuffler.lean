(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86Compare
  X86Arithmetic X86Flags X86Data X86StackMemory.
Import ListNotations.
Open Scope Z_scope.

Definition size_pc (state : seq_state) (base offset : Z) : seq_state :=
  write_reg_seq_state rip (machine_address (base + offset)) state.

Lemma comparison_zero_jns_unsigned n flags overflow carry auxiliary parity :
  0 <= n < 4294967296 ->
  let result := @sub_vec 32 (Z_to_bv 32 n) (Z_to_bv 32 0) in
  @eq_vec 1 (_get_rflags_type_SF
    (result_flags flags (sign_flag32 result) overflow carry
      (zero_flag32 result) auxiliary parity)) (Z_to_bv 1 0) = (n <? 2147483648).
Proof.
  intro Range. cbn beta zeta. rewrite result_flags_sign.
  unfold sign_flag32. rewrite bits_singleton, subtract32 by lia.
  rewrite Z.sub_0_r, sign_bit32_unsigned by exact Range.
  destruct (n <? 2147483648); reflexivity.
Qed.

Lemma size_cmp_zero_step nondet layout (frame : call_frame layout program_bytes)
    state offset old n :
  In offset [37; 55] ->
  0 <= n < 4294967296 ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 n ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (size_pc state (entry_pc frame) (offset + 3))) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = (n <? 2147483648) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (Z.eqb n 0).
Proof.
  intros Site Range Code Present PC Old Low.
  destruct (Present rflags) as [flags Flags].
  pose (next := size_pc state (entry_pc frame) (offset + 3)).
  assert (OldNext : read_reg_seq_state rdi next = Some old).
  { unfold next, size_pc. rewrite register_read_frame by discriminate. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, size_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm8 nondet 7 next old flags (Z_to_bv 8 0) OldNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  change (@sign_extend 8 (Z_to_bv 8 0) 32) with (Z_to_bv 32 0) in Execute.
  exists (result_flags flags
    (sign_flag32 (@sub_vec 32 (Z_to_bv 32 n) (Z_to_bv 32 0))) overflow carry
    (zero_flag32 (@sub_vec 32 (Z_to_bv 32 n) (Z_to_bv 32 0))) auxiliary parity).
  split.
  - eapply framed_instruction with (offset := offset) (size := 3)
      (instruction := CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM8 (Z_to_bv 8 0))));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [<-|[<-|Impossible]]; [vm_compute; tauto|vm_compute; tauto|contradiction].
    + destruct Site as [<-|[<-|Impossible]]; [destruct nondet; reflexivity|destruct nondet; reflexivity|contradiction].
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + 3) with (entry_pc frame + (offset + 3)) by lia.
      exact Execute.
  - split; [apply comparison_zero_jns_unsigned|apply comparison_jne]; lia.
Qed.

Lemma size_cmp_bound_step nondet layout (frame : call_frame layout program_bytes)
    state old n :
  0 <= n < 2147483648 ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 47)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 n ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (size_pc state (entry_pc frame) 53)) /\
    @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = (1025 <=? n).
Proof.
  intros Range Code Present PC Old Low.
  destruct (Present rflags) as [flags Flags].
  pose (next := size_pc state (entry_pc frame) 53).
  assert (OldNext : read_reg_seq_state rdi next = Some old).
  { unfold next, size_pc. rewrite register_read_frame by discriminate. exact Old. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, size_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_imm32 nondet 7 next old flags (Z_to_bv 32 1025) OldNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite Low in Execute.
  exists (result_flags flags
    (sign_flag32 (@sub_vec 32 (Z_to_bv 32 n) (Z_to_bv 32 1025))) overflow carry
    (zero_flag32 (@sub_vec 32 (Z_to_bv 32 n) (Z_to_bv 32 1025))) auxiliary parity).
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

Lemma size_jns_step nondet layout (frame : call_frame layout program_bytes)
    state offset displacement flags taken :
  In (offset, displacement) [(40, 5); (53, 10)] ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_SF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (size_pc state (entry_pc frame)
      (if taken then offset + 2 + displacement else offset + 2)).
Proof.
  intros Site Code Present PC Flags Taken.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 displacement) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNS (Z_to_bv 8 displacement));
    [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jns with (pc := machine_address (entry_pc frame + offset + 2)) (flags := flags).
    + rewrite Taken. destruct taken.
      * rewrite Extend.
        change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
          with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + offset + 2 + displacement) with
          (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
      * replace (entry_pc frame + offset + 2) with (entry_pc frame + (offset + 2)) by lia.
        reflexivity.
    + apply register_read_written.
    + rewrite register_read_frame by discriminate. exact Flags.
Qed.

Lemma size_invalid_jump_step nondet layout (frame : call_frame layout program_bytes)
    state offset displacement :
  In (offset, displacement) [(42, 376); (65, 353)] ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (size_pc state (entry_pc frame) 423).
Proof.
  intros Site Code Present PC.
  assert (Extend : @sign_extend 32 (Z_to_bv 32 displacement) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; reflexivity. }
  assert (Target : offset + 5 + displacement = 423).
  { destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction]; lia. }
  eapply framed_instruction with (offset := offset) (size := 5)
    (instruction := JMP32 (Z_to_bv 32 displacement));
    [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|Impossible]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jmp32 with (pc := machine_address (entry_pc frame + offset + 5)).
    + rewrite Extend.
      change (@add_vec 64 (machine_address (entry_pc frame + offset + 5)) (Z_to_bv 64 displacement))
        with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 5)) displacement).
      rewrite machine_address_next, register_write_overwrite.
      replace (entry_pc frame + offset + 5 + displacement) with (entry_pc frame + 423) by lia.
      reflexivity.
    + apply register_read_written.
Qed.

Lemma size_return_invalid_step nondet layout (frame : call_frame layout program_bytes) state :
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 423)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state rax (Z_to_bv 64 2) (size_pc state (entry_pc frame) 428)).
Proof.
  intros Code Present PC. destruct (Present rax) as [old Old].
  eapply framed_instruction with (offset := 423) (size := 5)
    (instruction := MOV (32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM32 (Z_to_bv 32 2))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 423 + 5) with (entry_pc frame + 428) by lia.
    apply (execute_mov32_immediate nondet 0 _ old (Z_to_bv 32 2)).
    change (read_reg_seq_state rax
      (write_reg_seq_state rip (machine_address (entry_pc frame + 428)) state) = Some old).
    rewrite register_read_frame by discriminate. exact Old.
Qed.

Print Assumptions comparison_zero_jns_unsigned.
Print Assumptions size_cmp_zero_step.
Print Assumptions size_cmp_bound_step.
Print Assumptions size_jns_step.
Print Assumptions size_invalid_jump_step.
Print Assumptions size_return_invalid_step.

Record oversized_body_result base (initial final : seq_state) : Prop := {
  oversized_body_pc : read_reg_seq_state rip final = Some (machine_address (base + 428));
  oversized_body_rax : read_reg_seq_state rax final = Some (Z_to_bv 64 2);
  oversized_body_other : forall reg, reg <> rip -> reg <> rflags -> reg <> rax ->
    read_reg_seq_state reg final = read_reg_seq_state reg initial;
  oversized_body_memory : archState.memory (sst final) = archState.memory (sst initial);
  oversized_body_written : written final = written initial;
  oversized_body_present : registers_present final;
  oversized_body_code : code_at final base program_bytes
}.

Ltac unfold_size_states :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold size_pc.

Ltac size_reads :=
  unfold_size_states;
  repeat first [rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Ltac size_code :=
  unfold_size_states; repeat apply code_at_register_write; assumption.

Ltac size_present :=
  unfold_size_states; repeat apply registers_present_write; assumption.

Ltac oversized_result :=
  constructor;
  [size_reads; reflexivity |
   size_reads; reflexivity |
   intros reg NotPC NotFlags NotRax; unfold_size_states;
     repeat rewrite register_read_frame by congruence; reflexivity |
   unfold_size_states; reflexivity |
   unfold_size_states; reflexivity |
   size_present |
   size_code].

Theorem oversized_body_path nondet layout (frame : call_frame layout program_bytes)
    state old n :
  1024 < n < 4294967296 ->
  code_at state (entry_pc frame) program_bytes ->
  registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 37)) ->
  read_reg_seq_state rdi state = Some old ->
  low_register32 7 old = Z_to_bv 32 n ->
  exists count final,
    (count = 4 \/ count = 6)%nat /\
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) count state final /\
    oversized_body_result (entry_pc frame) state final.
Proof.
  intros Range Code Present PC Old Low.
  destruct (size_cmp_zero_step nondet layout frame state 37 old n
    ltac:(left; reflexivity) ltac:(lia) Code Present PC Old Low)
    as [f1 [Step1 [Sign1 Zero1]]].
  pose (s1 := write_reg_seq_state rflags f1 (size_pc state (entry_pc frame) 40)).
  change (instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1) in Step1.
  destruct (n <? 2147483648) eqn:Small.
  - apply Z.ltb_lt in Small.
    pose (s2 := size_pc s1 (entry_pc frame) 47).
    assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s1 s2).
    { apply (size_jns_step nondet layout frame s1 40 5 f1 true).
      - left. reflexivity.
      - size_code.
      - size_present.
      - size_reads. reflexivity.
      - size_reads. reflexivity.
      - exact Sign1. }
    destruct (size_cmp_bound_step nondet layout frame s2 old n
      ltac:(lia) ltac:(size_code) ltac:(size_present)
      ltac:(size_reads; reflexivity) ltac:(size_reads; exact Old) Low)
      as [f2 [Step3 Sign2]].
    assert (Bound : (1025 <=? n) = true) by (apply Z.leb_le; lia).
    rewrite Bound in Sign2.
    pose (s3 := write_reg_seq_state rflags f2 (size_pc s2 (entry_pc frame) 53)).
    change (instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s2 s3) in Step3.
    pose (s4 := size_pc s3 (entry_pc frame) 65).
    assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s3 s4).
    { apply (size_jns_step nondet layout frame s3 53 10 f2 true).
      - right. left. reflexivity.
      - size_code.
      - size_present.
      - size_reads. reflexivity.
      - size_reads. reflexivity.
      - exact Sign2. }
    pose (s5 := size_pc s4 (entry_pc frame) 423).
    assert (Step5 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s4 s5).
    { apply (size_invalid_jump_step nondet layout frame s4 65 353).
      - right. left. reflexivity.
      - size_code.
      - size_present.
      - size_reads. reflexivity. }
    pose (s6 := write_reg_seq_state rax (Z_to_bv 64 2) (size_pc s5 (entry_pc frame) 428)).
    assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s5 s6).
    { apply size_return_invalid_step.
      - size_code.
      - size_present.
      - size_reads. reflexivity. }
    exists 6%nat, s6. split; [right; reflexivity|]. split.
    + eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step1|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step2|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step3|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step4|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step5|exact Step6].
    + oversized_result.
  - pose (s2 := size_pc s1 (entry_pc frame) 42).
    assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s1 s2).
    { apply (size_jns_step nondet layout frame s1 40 5 f1 false).
      - left. reflexivity.
      - size_code.
      - size_present.
      - size_reads. reflexivity.
      - size_reads. reflexivity.
      - exact Sign1. }
    pose (s3 := size_pc s2 (entry_pc frame) 423).
    assert (Step3 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s2 s3).
    { apply (size_invalid_jump_step nondet layout frame s2 42 376).
      - left. reflexivity.
      - size_code.
      - size_present.
      - size_reads. reflexivity. }
    pose (s4 := write_reg_seq_state rax (Z_to_bv 64 2) (size_pc s3 (entry_pc frame) 428)).
    assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s3 s4).
    { apply size_return_invalid_step.
      - size_code.
      - size_present.
      - size_reads. reflexivity. }
    exists 4%nat, s4. split; [left; reflexivity|]. split.
    + eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
    + oversized_result.
Qed.

Print Assumptions oversized_body_path.
