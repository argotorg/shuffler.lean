(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Control X86ABI X86Entry X86Execution
  X86Program X86Memory X86Address X86Decode X86DecodeReplay X86Compare
  X86Arithmetic X86Flags X86Data X86OversizedBody.
Import ListNotations.
Open Scope Z_scope.

Record nonempty_size_result base (initial final : seq_state) : Prop := {
  nonempty_size_pc : read_reg_seq_state rip final = Some (machine_address (base + 70));
  nonempty_size_other : forall reg, reg <> rip -> reg <> rflags ->
    read_reg_seq_state reg final = read_reg_seq_state reg initial;
  nonempty_size_memory : archState.memory (sst final) = archState.memory (sst initial);
  nonempty_size_written : written final = written initial;
  nonempty_size_present : registers_present final;
  nonempty_size_code : code_at final base program_bytes
}.

Theorem nonempty_size_path nondet layout (frame : call_frame layout program_bytes)
    state old n :
  0 < n <= 1024 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 37)) ->
  read_reg_seq_state rdi state = Some old -> low_register32 7 old = Z_to_bv 32 n ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 6 state final /\
    nonempty_size_result (entry_pc frame) state final.
Proof.
  intros Range Code Present PC Old Low.
  assert (HighBit : (n <? 2147483648) = true) by (apply Z.ltb_lt; lia).
  assert (Bound : (1025 <=? n) = false) by (apply Z.leb_gt; lia).
  assert (Nonzero : (n =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (size_cmp_zero_step nondet layout frame state 37 old n
    ltac:(left; reflexivity) ltac:(lia) Code Present PC Old Low)
    as [f1 [Step1 [Sign1 Zero1]]].
  pose (s1 := write_reg_seq_state rflags f1 (size_pc state (entry_pc frame) 40)).
  pose (s2 := size_pc s1 (entry_pc frame) 47).
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { apply (size_jns_step nondet layout frame s1 40 5 f1 true).
    - left. reflexivity.
    - size_code.
    - size_present.
    - size_reads. reflexivity.
    - size_reads. reflexivity.
    - now rewrite HighBit in Sign1. }
  destruct (size_cmp_bound_step nondet layout frame s2 old n ltac:(lia)
    ltac:(size_code) ltac:(size_present) ltac:(size_reads; reflexivity)
    ltac:(size_reads; exact Old) Low) as [f3 [Step3 Sign3]].
  pose (s3 := write_reg_seq_state rflags f3 (size_pc s2 (entry_pc frame) 53)).
  pose (s4 := size_pc s3 (entry_pc frame) 55).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { apply (size_jns_step nondet layout frame s3 53 10 f3 false).
    - right. left. reflexivity.
    - size_code.
    - size_present.
    - size_reads. reflexivity.
    - size_reads. reflexivity.
    - now rewrite Bound in Sign3. }
  destruct (size_cmp_zero_step nondet layout frame s4 55 old n
    ltac:(right; left; reflexivity) ltac:(lia)
    ltac:(size_code) ltac:(size_present) ltac:(size_reads; reflexivity)
    ltac:(size_reads; exact Old) Low) as [f5 [Step5 [Sign5 Zero5]]].
  pose (s5 := write_reg_seq_state rflags f5 (size_pc s4 (entry_pc frame) 58)).
  pose (s6 := size_pc s5 (entry_pc frame) 70).
  assert (Step6 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s5 s6).
  { eapply framed_instruction with (offset := 58) (size := 2)
      (instruction := JNE (Z_to_bv 8 10)).
    - size_code.
    - size_present.
    - size_reads. reflexivity.
    - vm_compute. tauto.
    - destruct nondet; reflexivity.
    - rewrite machine_address_next.
      erewrite execute_jne with (pc := machine_address (entry_pc frame + 58 + 2)) (flags := f5).
      + rewrite Zero5, Nonzero. cbn beta iota zeta.
        change (@sign_extend 8 (Z_to_bv 8 10) 64) with (Z_to_bv 64 10).
        change (@add_vec 64 (machine_address (entry_pc frame + 58 + 2)) (Z_to_bv 64 10))
          with (@add_vec_int 64 (machine_address (entry_pc frame + 58 + 2)) 10).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + 58 + 2 + 10) with (entry_pc frame + 70) by lia.
        reflexivity.
      + apply register_read_written.
      + rewrite register_read_frame by discriminate. size_reads. reflexivity. }
  exists s6. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step4|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step5|exact Step6].
  - constructor.
    + size_reads. reflexivity.
    + intros reg NotPC NotFlags. unfold_size_states.
      repeat rewrite register_read_frame by congruence. reflexivity.
    + unfold_size_states. reflexivity.
    + unfold_size_states. reflexivity.
    + size_present.
    + size_code.
Qed.

Print Assumptions nonempty_size_path.
