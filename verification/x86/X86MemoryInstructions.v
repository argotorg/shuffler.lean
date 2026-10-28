(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Memory X86Instructions X86Flags.
Import ListNotations.

Local Ltac combine_byte_slices :=
  repeat match goal with
  | |- context [bv_concat ?total (bv_extract ?low ?high ?value)
      (bv_extract 0 ?low ?value)] =>
      let value_type := type of value in
      lazymatch value_type with bv ?n =>
        let Join := fresh "Join" in
        pose proof (@concat_adjacent_extracts n high low value) as Join;
        change (bv_concat total (bv_extract low high value)
          (bv_extract 0 low value) = bv_extract 0 total value) in Join;
        rewrite Join; clear Join
      end
  end.

Lemma sail_read_bytes32 (value : bv 32) :
  Tiny_x86.from_bytes_le 4 (@Tiny_x86_types.Defs.bytes_of_bv 4 value) = value.
Proof.
  change (MachineWord.MachineWord.update_slice
    (MachineWord.MachineWord.update_slice
      (MachineWord.MachineWord.update_slice
        (MachineWord.MachineWord.update_slice (Z_to_bv 32 0) 0 (bv_extract 0 8 value))
        8 (bv_extract 8 8 value)) 16 (bv_extract 16 8 value))
    24 (bv_extract 24 8 value) = value).
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  bv_simplify.
  rewrite bv_zero_extend_idemp.
  replace (bv_extract 0 0 (Z_to_bv 32 0)) with (bv_extract 0 0 value)
    by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity).
  combine_byte_slices.
  apply extract_whole.
Qed.

Lemma sail_read_bytes64 (value : bv 64) :
  Tiny_x86.from_bytes_le 8 (@Tiny_x86_types.Defs.bytes_of_bv 8 value) = value.
Proof.
  change (MachineWord.MachineWord.update_slice
    (MachineWord.MachineWord.update_slice
      (MachineWord.MachineWord.update_slice
        (MachineWord.MachineWord.update_slice
          (MachineWord.MachineWord.update_slice
            (MachineWord.MachineWord.update_slice
              (MachineWord.MachineWord.update_slice
                (MachineWord.MachineWord.update_slice (Z_to_bv 64 0)
                  0 (bv_extract 0 8 value))
                8 (bv_extract 8 8 value)) 16 (bv_extract 16 8 value))
            24 (bv_extract 24 8 value)) 32 (bv_extract 32 8 value))
        40 (bv_extract 40 8 value)) 48 (bv_extract 48 8 value))
    56 (bv_extract 56 8 value) = value).
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  bv_simplify. rewrite bv_zero_extend_idemp.
  replace (bv_extract 0 0 (Z_to_bv 64 0)) with (bv_extract 0 0 value)
    by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity).
  combine_byte_slices.
  apply extract_whole.
Qed.

Lemma sail_write_bytes32 (value : bv 32) :
  Tiny_x86_types.Defs.bv_of_bytes (Tiny_x86.to_bytes_le 4 value) = value.
Proof.
  change (bv_concat 32 (bv_extract 24 8 value)
    (bv_concat 24 (bv_extract 16 8 value)
      (bv_concat 16 (bv_extract 8 8 value)
        (bv_concat 8 (bv_extract 0 8 value) (bv_0 0)))) = value).
  replace (bv_0 0) with (bv_extract 0 0 value)
    by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity).
  combine_byte_slices.
  apply extract_whole.
Qed.

Lemma sail_write_bytes64 (value : bv 64) :
  Tiny_x86_types.Defs.bv_of_bytes (Tiny_x86.to_bytes_le 8 value) = value.
Proof.
  change (bv_concat 64 (bv_extract 56 8 value)
    (bv_concat 56 (bv_extract 48 8 value)
      (bv_concat 48 (bv_extract 40 8 value)
        (bv_concat 40 (bv_extract 32 8 value)
          (bv_concat 32 (bv_extract 24 8 value)
            (bv_concat 24 (bv_extract 16 8 value)
              (bv_concat 16 (bv_extract 8 8 value)
                (bv_concat 8 (bv_extract 0 8 value) (bv_0 0)))))))) = value).
  replace (bv_0 0) with (bv_extract 0 0 value)
    by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity).
  combine_byte_slices.
  apply extract_whole.
Qed.

Lemma sail_read_word_trace nondet addr state (value : bv 32) :
  read_mem_seq_state 4 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_memory 4 addr (Tiny_x86.create_readAccessDescriptor tt)))
    state state value.
Proof.
  intro Read.
  assert (Address : SailStdpp.Operators_mwords.vector_truncate addr 64 = addr).
  { change (bv_extract 0 64 addr = addr). bv_simplify. reflexivity. }
  cbn. rewrite Address.
  econstructor.
  - exact (@explicit_read_seq 4 addr state value Read).
  - change (sail_trace nondet (FMon.Ret
      (Tiny_x86.from_bytes_le 4 (@Tiny_x86_types.Defs.bytes_of_bv 4 value)))
      state state value).
    rewrite sail_read_bytes32. constructor.
Qed.

Lemma sail_read_doubleword_trace nondet addr state (value : bv 64) :
  read_mem_seq_state 8 addr state = Some value ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.read_memory 8 addr (Tiny_x86.create_readAccessDescriptor tt)))
    state state value.
Proof.
  intro Read.
  assert (Address : SailStdpp.Operators_mwords.vector_truncate addr 64 = addr).
  { change (bv_extract 0 64 addr = addr). apply extract_whole. }
  cbn. rewrite Address. econstructor.
  - exact (@explicit_read_seq 8 addr state value Read).
  - change (sail_trace nondet (FMon.Ret
      (Tiny_x86.from_bytes_le 8 (@Tiny_x86_types.Defs.bytes_of_bv 8 value)))
      state state value).
    rewrite sail_read_bytes64. constructor.
Qed.

Lemma sail_write_word_trace nondet addr state (value : bv 32) :
  mem_present addr 4 (archState.memory (sst state)) = true ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_memory 4 addr value (Tiny_x86.create_writeAccessDescriptor tt)))
    state (stored_bytes_state state addr (bv_to_bytes 8 value)) tt.
Proof.
  intro Mapped.
  assert (Address : SailStdpp.Operators_mwords.vector_truncate addr 64 = addr).
  { change (bv_extract 0 64 addr = addr). apply extract_whole. }
  cbn. rewrite Address.
  match goal with |- context [@Tiny_x86_types.Defs.bv_of_bools ?n ?tags] =>
    assert (Tags : @Tiny_x86_types.Defs.bv_of_bools n tags = bv_0 0)
      by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity);
    rewrite Tags
  end.
  econstructor 2 with
    (middle := stored_bytes_state state addr (bv_to_bytes 8 value)) (answer := Ok tt).
  -
    change (sequential_model_outcome None
      (MemWrite (MemReq.make (Tiny_x86.create_writeAccessDescriptor tt) addr tt 4 0)
        (Tiny_x86_types.Defs.bv_of_bytes (Tiny_x86.to_bytes_le 4 value)) (bv_0 0))
      state = Exec.make [(stored_bytes_state state addr (bv_to_bytes 8 value), Ok tt)] []).
    rewrite sail_write_bytes32. exact (@explicit_write_seq 4 addr state value Mapped).
  - constructor.
Qed.

Lemma sail_write_doubleword_trace nondet addr state (value : bv 64) :
  mem_present addr 8 (archState.memory (sst state)) = true ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86.write_memory 8 addr value (Tiny_x86.create_writeAccessDescriptor tt)))
    state (stored_bytes_state state addr (bv_to_bytes 8 value)) tt.
Proof.
  intro Mapped.
  assert (Address : SailStdpp.Operators_mwords.vector_truncate addr 64 = addr).
  { change (bv_extract 0 64 addr = addr). apply extract_whole. }
  cbn. rewrite Address.
  match goal with |- context [@Tiny_x86_types.Defs.bv_of_bools ?n ?tags] =>
    assert (Tags : @Tiny_x86_types.Defs.bv_of_bools n tags = bv_0 0)
      by (apply bv_eq; rewrite !bv_unsigned_N_0; reflexivity);
    rewrite Tags
  end.
  econstructor 2 with
    (middle := stored_bytes_state state addr (bv_to_bytes 8 value)) (answer := Ok tt).
  - change (sequential_model_outcome None
      (MemWrite (MemReq.make (Tiny_x86.create_writeAccessDescriptor tt) addr tt 8 0)
        (Tiny_x86_types.Defs.bv_of_bytes (Tiny_x86.to_bytes_le 8 value)) (bv_0 0))
      state = Exec.make [(stored_bytes_state state addr (bv_to_bytes 8 value), Ok tt)] []).
    rewrite sail_write_bytes64. exact (@explicit_write_seq 8 addr state value Mapped).
  - constructor.
Qed.

Print Assumptions sail_read_word_trace.
Print Assumptions sail_read_doubleword_trace.
Print Assumptions sail_write_word_trace.
Print Assumptions sail_write_doubleword_trace.
