(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers.
From ASCommon Require Import Common.
From ArchSemX86 Require Import X86Inst.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Program
  X86Prologue X86Initialize X86Call.
Import ListNotations.

Definition argument_registers : list reg :=
  [(rdi : reg); (rsi : reg); (rdx : reg); (rcx : reg); (r8 : reg); (r9 : reg); (r10 : reg)].

Record core_arguments layout (size : nat) bd bp bt bu trace output state : Prop := {
  core_size : exists value, read_reg_seq_state rdi state = Some value /\
    bv_extract 0 32 value = machine_word (Int.repr (Z.of_nat size));
  core_data : read_reg_seq_state rsi state = Some (pointer_to_block layout bd);
  core_permutation : read_reg_seq_state rdx state = Some (pointer_to_block layout bp);
  core_target : read_reg_seq_state rcx state = Some (pointer_to_block layout bt);
  core_used : read_reg_seq_state r8 state = Some (pointer_to_block layout bu);
  core_trace : read_reg_seq_state r9 state = Some (pointer_to_block layout trace);
  core_output : read_reg_seq_state r10 state = Some (pointer_to_block layout output)
}.

Lemma core_arguments_frame layout size bd bp bt bu trace output before after :
  core_arguments layout size bd bp bt bu trace output before ->
  (forall reg, In reg argument_registers ->
    read_reg_seq_state reg after = read_reg_seq_state reg before) ->
  core_arguments layout size bd bp bt bu trace output after.
Proof.
  intros [Size Data Perm Target Used Trace Output] Frame.
  constructor.
  - destruct Size as [value [Read Low]]. exists value. split; [|exact Low].
    rewrite Frame; [exact Read|cbn; tauto].
  - rewrite Frame; [exact Data|cbn; tauto].
  - rewrite Frame; [exact Perm|cbn; tauto].
  - rewrite Frame; [exact Target|cbn; tauto].
  - rewrite Frame; [exact Used|cbn; tauto].
  - rewrite Frame; [exact Trace|cbn; tauto].
  - rewrite Frame; [exact Output|cbn; tauto].
Qed.

Lemma core_arguments_write layout size bd bp bt bu trace output state reg value :
  ~ In reg argument_registers ->
  core_arguments layout size bd bp bt bu trace output state ->
  core_arguments layout size bd bp bt bu trace output (write_reg_seq_state reg value state).
Proof.
  intros Outside Arguments. apply (core_arguments_frame _ _ _ _ _ _ _ _ state _ Arguments).
  intros other Inside. rewrite register_read_frame; [reflexivity|congruence].
Qed.

Lemma core_arguments_store layout size bd bp bt bu trace output state addr contents :
  core_arguments layout size bd bp bt bu trace output state ->
  core_arguments layout size bd bp bt bu trace output (stored_bytes_state state addr contents).
Proof.
  intro Arguments. apply (core_arguments_frame _ _ _ _ _ _ _ _ state _ Arguments).
  intros reg Inside. apply stored_register_read.
Qed.

Theorem call_body_arguments layout (frame : call_frame layout program_bytes)
    size bd bp bt bu trace output initial :
  abi_entry layout program_bytes frame (Int.repr (Z.of_nat size))
    bd bp bt bu trace output initial ->
  core_arguments layout size bd bp bt bu trace output
    (call_body_state layout frame output initial).
Proof.
  intro Entry. unfold call_body_state. constructor.
  - destruct (entry_size _ _ _ _ _ _ _ _ _ _ _ Entry) as [value [Read Low]].
    exists value. split; [|exact Low].
    rewrite initialized_other, prologue_other by discriminate. exact Read.
  - rewrite initialized_other, prologue_other by discriminate. exact (entry_data _ _ _ _ _ _ _ _ _ _ _ Entry).
  - rewrite initialized_other, prologue_other by discriminate. exact (entry_permutation _ _ _ _ _ _ _ _ _ _ _ Entry).
  - rewrite initialized_other, prologue_other by discriminate. exact (entry_target _ _ _ _ _ _ _ _ _ _ _ Entry).
  - rewrite initialized_other, prologue_other by discriminate. exact (entry_used _ _ _ _ _ _ _ _ _ _ _ Entry).
  - rewrite initialized_other, prologue_other by discriminate. exact (entry_trace _ _ _ _ _ _ _ _ _ _ _ Entry).
  - rewrite initialized_other by discriminate. apply prologue_output.
Qed.

Print Assumptions core_arguments_frame.
Print Assumptions core_arguments_write.
Print Assumptions core_arguments_store.
Print Assumptions call_body_arguments.
