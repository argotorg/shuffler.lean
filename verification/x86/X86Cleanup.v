(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Integers.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Control X86Flags
  X86Instructions X86StackMemory X86Program X86DecodeReplay X86Execution
  X86Entry X86Address.
Import ListNotations.
Open Scope Z_scope.

Definition cleanup_pop_state destination next_pc stack (value : bv 64) state : seq_state :=
  write_reg_seq_state rsp (machine_address (stack + 8))
    (write_reg_seq_state (Values.reg (gpr_reference destination))
      (Values.from_ty (gpr_reference destination) value)
      (write_reg_seq_state rip (machine_address next_pc) state)).

Lemma cleanup_pop_once layout (frame : call_frame layout program_bytes)
    state offset size destination stack value :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rsp state = Some (machine_address stack) ->
  read_mem_seq_state 8 (machine_address stack) state = Some value ->
  Values.reg (gpr_reference destination) <> rsp ->
  Values.reg (gpr_reference destination) <> rip ->
  In (offset, size) program_instructions ->
  decoded_instruction true (machine_address (entry_pc frame + offset))
    (register_values_of state) offset = Some (POP (64, rm_REG (REG_NORMAL destination))) ->
  instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 state
    (cleanup_pop_state destination (entry_pc frame + offset + size) stack value state).
Proof.
  intros Code Present PC Stack Read NotStack NotPC At Decode.
  destruct (Present (Values.reg (gpr_reference destination))) as [old Old].
  eapply framed_instruction; [exact Code|exact Present|exact PC|exact At|exact Decode|].
  rewrite machine_address_next. unfold cleanup_pop_state.
  pose proof (execute_pop64 true destination
    (write_reg_seq_state rip (machine_address (entry_pc frame + offset + size)) state)
    (machine_address stack) old value NotStack) as Execute.
  rewrite register_read_frame in Execute by discriminate.
  rewrite register_read_frame in Execute by congruence.
  specialize (Execute Stack Old Read).
  rewrite machine_address_next in Execute. exact Execute.
Qed.

Lemma cleanup_pop_code destination next_pc stack value state base code :
  code_at state base code ->
  code_at (cleanup_pop_state destination next_pc stack value state) base code.
Proof. intro Code. repeat apply code_at_register_write. exact Code. Qed.

Lemma cleanup_pop_registers destination next_pc stack value state :
  registers_present state ->
  registers_present (cleanup_pop_state destination next_pc stack value state).
Proof. intro Present. repeat apply registers_present_write. exact Present. Qed.

Lemma cleanup_pop_pc destination next_pc stack value state :
  Values.reg (gpr_reference destination) <> rip ->
  read_reg_seq_state rip (cleanup_pop_state destination next_pc stack value state) =
    Some (machine_address next_pc).
Proof.
  intro Different. unfold cleanup_pop_state.
  rewrite register_read_frame by discriminate.
  rewrite register_read_frame by exact Different. apply register_read_written.
Qed.

Lemma cleanup_pop_stack destination next_pc stack value state :
  read_reg_seq_state rsp (cleanup_pop_state destination next_pc stack value state) =
    Some (machine_address (stack + 8)).
Proof. apply register_read_written. Qed.

Lemma cleanup_pop_read destination next_pc stack value state size addr :
  read_mem_seq_state size addr (cleanup_pop_state destination next_pc stack value state) =
    read_mem_seq_state size addr state.
Proof. reflexivity. Qed.

Print Assumptions cleanup_pop_once.

Definition cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx
    return_address state : seq_state :=
  let first := cleanup_pop_state 15 (base + 430) (stack - 40) saved15 state in
  let second := cleanup_pop_state 14 (base + 432) (stack - 32) saved14 first in
  let third := cleanup_pop_state 13 (base + 434) (stack - 24) saved13 second in
  let fourth := cleanup_pop_state 12 (base + 436) (stack - 16) saved12 third in
  let fifth := cleanup_pop_state 3 (base + 437) (stack - 8) saved_bx fourth in
  write_reg_seq_state rsp (machine_address (stack + 8))
    (write_reg_seq_state rip return_address
      (write_reg_seq_state rip (machine_address (base + 438)) fifth)).

Theorem cleanup_steps layout (frame : call_frame layout program_bytes) state
    saved15 saved14 saved13 saved12 saved_bx :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 428)) ->
  read_reg_seq_state rsp state = Some (machine_address (entry_sp frame - 40)) ->
  read_mem_seq_state 8 (machine_address (entry_sp frame - 40)) state = Some saved15 ->
  read_mem_seq_state 8 (machine_address (entry_sp frame - 32)) state = Some saved14 ->
  read_mem_seq_state 8 (machine_address (entry_sp frame - 24)) state = Some saved13 ->
  read_mem_seq_state 8 (machine_address (entry_sp frame - 16)) state = Some saved12 ->
  read_mem_seq_state 8 (machine_address (entry_sp frame - 8)) state = Some saved_bx ->
  read_mem_seq_state 8 (machine_address (entry_sp frame)) state =
    Some (machine_address (return_pc frame)) ->
  instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 6 state
    (cleanup_result (entry_pc frame) (entry_sp frame) saved15 saved14 saved13 saved12
      saved_bx (machine_address (return_pc frame)) state).
Proof.
  intros Code Present PC Stack Read15 Read14 Read13 Read12 ReadBX ReadReturn.
  set (first := cleanup_pop_state 15 (entry_pc frame + 430) (entry_sp frame - 40) saved15 state).
  set (second := cleanup_pop_state 14 (entry_pc frame + 432) (entry_sp frame - 32) saved14 first).
  set (third := cleanup_pop_state 13 (entry_pc frame + 434) (entry_sp frame - 24) saved13 second).
  set (fourth := cleanup_pop_state 12 (entry_pc frame + 436) (entry_sp frame - 16) saved12 third).
  set (fifth := cleanup_pop_state 3 (entry_pc frame + 437) (entry_sp frame - 8) saved_bx fourth).
  assert (Step15 : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 state first).
  { unfold first. replace (entry_pc frame + 430) with (entry_pc frame + 428 + 2) by lia.
    apply cleanup_pop_once; try assumption; try discriminate;
      [vm_compute; tauto|reflexivity]. }
  assert (Step14 : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 first second).
  { unfold second. replace (entry_pc frame + 432) with (entry_pc frame + 430 + 2) by lia.
    apply cleanup_pop_once.
    - apply cleanup_pop_code, Code.
    - apply cleanup_pop_registers, Present.
    - apply cleanup_pop_pc. discriminate.
    - replace (entry_sp frame - 32) with (entry_sp frame - 40 + 8) by lia.
      apply cleanup_pop_stack.
    - exact Read14.
    - discriminate.
    - discriminate.
    - vm_compute. tauto.
    - reflexivity. }
  assert (Step13 : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 second third).
  { unfold third. replace (entry_pc frame + 434) with (entry_pc frame + 432 + 2) by lia.
    apply cleanup_pop_once.
    - apply cleanup_pop_code, cleanup_pop_code, Code.
    - apply cleanup_pop_registers, cleanup_pop_registers, Present.
    - apply cleanup_pop_pc. discriminate.
    - replace (entry_sp frame - 24) with (entry_sp frame - 32 + 8) by lia.
      apply cleanup_pop_stack.
    - exact Read13.
    - discriminate.
    - discriminate.
    - vm_compute. tauto.
    - reflexivity. }
  assert (Step12 : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 third fourth).
  { unfold fourth. replace (entry_pc frame + 436) with (entry_pc frame + 434 + 2) by lia.
    apply cleanup_pop_once.
    - apply cleanup_pop_code, cleanup_pop_code, cleanup_pop_code, Code.
    - apply cleanup_pop_registers, cleanup_pop_registers, cleanup_pop_registers, Present.
    - apply cleanup_pop_pc. discriminate.
    - replace (entry_sp frame - 16) with (entry_sp frame - 24 + 8) by lia.
      apply cleanup_pop_stack.
    - exact Read12.
    - discriminate.
    - discriminate.
    - vm_compute. tauto.
    - reflexivity. }
  assert (StepBX : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 fourth fifth).
  { unfold fifth. replace (entry_pc frame + 437) with (entry_pc frame + 436 + 1) by lia.
    apply cleanup_pop_once.
    - apply cleanup_pop_code, cleanup_pop_code, cleanup_pop_code, cleanup_pop_code, Code.
    - apply cleanup_pop_registers, cleanup_pop_registers, cleanup_pop_registers,
        cleanup_pop_registers, Present.
    - apply cleanup_pop_pc. discriminate.
    - replace (entry_sp frame - 8) with (entry_sp frame - 16 + 8) by lia.
      apply cleanup_pop_stack.
    - exact ReadBX.
    - discriminate.
    - discriminate.
    - vm_compute. tauto.
    - reflexivity. }
  assert (Return : instruction_steps (sail_tiny_x86_sem true)
    (return_condition (machine_address (return_pc frame))) 1 fifth
      (cleanup_result (entry_pc frame) (entry_sp frame) saved15 saved14 saved13 saved12
        saved_bx (machine_address (return_pc frame)) state)).
  { eapply framed_instruction with (offset := 437) (size := 1) (instruction := RET tt).
    - apply cleanup_pop_code, cleanup_pop_code, cleanup_pop_code, cleanup_pop_code,
        cleanup_pop_code, Code.
    - apply cleanup_pop_registers, cleanup_pop_registers, cleanup_pop_registers,
        cleanup_pop_registers, cleanup_pop_registers, Present.
    - apply cleanup_pop_pc. discriminate.
    - vm_compute. tauto.
    - reflexivity.
    - rewrite machine_address_next.
      replace (entry_pc frame + 437 + 1) with (entry_pc frame + 438) by lia.
      pose proof (execute_ret true
        (write_reg_seq_state rip (machine_address (entry_pc frame + 438)) fifth)
        (machine_address (entry_sp frame)) (machine_address (entry_pc frame + 438))
        (machine_address (return_pc frame))) as Execute.
      rewrite register_read_frame in Execute by discriminate.
      rewrite register_read_written in Execute.
      assert (StackNow : read_reg_seq_state rsp fifth = Some (machine_address (entry_sp frame))).
      { unfold fifth. rewrite cleanup_pop_stack. f_equal. f_equal. lia. }
      specialize (Execute StackNow eq_refl ReadReturn).
      rewrite machine_address_next in Execute. exact Execute. }
  eapply instruction_steps_append with (count := 1%nat) (rest := 5%nat); [exact Step15|].
  eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step14|].
  eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step13|].
  eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step12|].
  eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact StepBX|exact Return].
Qed.

Print Assumptions cleanup_steps.

Local Ltac cleanup_register :=
  unfold cleanup_result, cleanup_pop_state;
  repeat first [rewrite register_read_written |
    rewrite register_read_frame by discriminate]; reflexivity.

Lemma cleanup_pc base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state rip
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some return_address.
Proof. cleanup_register. Qed.

Lemma cleanup_stack base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state rsp
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some (machine_address (stack + 8)).
Proof. cleanup_register. Qed.

Lemma cleanup_rbx base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state rbx
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some saved_bx.
Proof. cleanup_register. Qed.

Lemma cleanup_r12 base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state r12
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some saved12.
Proof. cleanup_register. Qed.

Lemma cleanup_r13 base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state r13
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some saved13.
Proof. cleanup_register. Qed.

Lemma cleanup_r14 base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state r14
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some saved14.
Proof. cleanup_register. Qed.

Lemma cleanup_r15 base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state r15
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    Some saved15.
Proof. cleanup_register. Qed.

Lemma cleanup_rbp base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state rbp
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    read_reg_seq_state rbp state.
Proof. cleanup_register. Qed.

Lemma cleanup_rax base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  read_reg_seq_state rax
    (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state) =
    read_reg_seq_state rax state.
Proof. cleanup_register. Qed.

Lemma cleanup_memory base stack saved15 saved14 saved13 saved12 saved_bx return_address state :
  archState.memory
    (sst (cleanup_result base stack saved15 saved14 saved13 saved12 saved_bx return_address state)) =
    archState.memory (sst state).
Proof. reflexivity. Qed.

Lemma state_register_lookup state reg :
  reg_lookup reg (state_registers state) = read_reg_seq_state reg state.
Proof. reflexivity. Qed.

Lemma callee_saved_from_reads before after :
  read_reg_seq_state rbx after = read_reg_seq_state rbx before ->
  read_reg_seq_state rbp after = read_reg_seq_state rbp before ->
  read_reg_seq_state r12 after = read_reg_seq_state r12 before ->
  read_reg_seq_state r13 after = read_reg_seq_state r13 before ->
  read_reg_seq_state r14 after = read_reg_seq_state r14 before ->
  read_reg_seq_state r15 after = read_reg_seq_state r15 before ->
  callee_saved_preserved before after.
Proof.
  intros BX BP R12 R13 R14 R15 reg Saved. rewrite !state_register_lookup.
  cbn in Saved.
  destruct Saved as [Same|[Same|[Same|[Same|[Same|[Same|Impossible]]]]]];
    try contradiction; subst reg; assumption.
Qed.

Theorem cleanup_abi_return layout (frame : call_frame layout program_bytes) before state
    saved15 saved14 saved13 saved12 saved_bx result :
  read_reg_seq_state r15 before = Some saved15 ->
  read_reg_seq_state r14 before = Some saved14 ->
  read_reg_seq_state r13 before = Some saved13 ->
  read_reg_seq_state r12 before = Some saved12 ->
  read_reg_seq_state rbx before = Some saved_bx ->
  read_reg_seq_state rbp state = read_reg_seq_state rbp before ->
  (exists value, read_reg_seq_state rax state = Some value /\
    bv_extract 0 32 value = machine_word result) ->
  abi_return layout program_bytes frame before
    (cleanup_result (entry_pc frame) (entry_sp frame) saved15 saved14 saved13 saved12
      saved_bx (machine_address (return_pc frame)) state) result.
Proof.
  intros Saved15 Saved14 Saved13 Saved12 SavedBX SavedBP [value [Value Result]].
  constructor.
  - rewrite state_register_lookup. apply cleanup_pc.
  - rewrite state_register_lookup. apply cleanup_stack.
  - exists value. split; [|exact Result].
    rewrite state_register_lookup, cleanup_rax. exact Value.
  - apply callee_saved_from_reads.
    + rewrite cleanup_rbx. symmetry. exact SavedBX.
    + rewrite cleanup_rbp. exact SavedBP.
    + rewrite cleanup_r12. symmetry. exact Saved12.
    + rewrite cleanup_r13. symmetry. exact Saved13.
    + rewrite cleanup_r14. symmetry. exact Saved14.
    + rewrite cleanup_r15. symmetry. exact Saved15.
Qed.

Print Assumptions cleanup_abi_return.
