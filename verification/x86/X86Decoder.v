(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Program X86Decode X86DecodeReplay
  X86Memory X86ABI X86CodeMemory X86FetchAddress.
Import ListNotations.
Open Scope Z_scope.

Lemma expected_fetch_from_code state base offset fetched size :
  code_at state base program_bytes ->
  0 <= fetched ->
  fetched + Z.of_N size <= Z.of_nat (List.length program_bytes) ->
  event_succeeds state
    (expected_fetch (machine_address (base + offset)) offset (fetched, size)).
Proof.
  intros Code Low High.
  change (sequential_model_outcome None
    (MemRead (MemReq.make (Tiny_x86.create_iFetchAccessDescriptor tt)
      (@SailStdpp.Operators_mwords.vector_truncate 64
        (@SailStdpp.Operators_mwords.add_vec_int 64
          (Z_to_bv 64 (base + offset)) (fetched - offset)) 64) tt size 0)) state =
    Exec.make [(state, Ok (code_read_value size fetched, bv_0 0))] []).
  rewrite instruction_fetch_address.
  unfold code_read_value.
  replace (base + fetched) with (base + Z.of_nat (Z.to_nat fetched)) by lia.
  apply code_slice_fetch; [exact Code|lia].
Qed.

Theorem decode_from_code nondet state base registers offset size instruction :
  code_at state base program_bytes ->
  In (offset, size) program_instructions ->
  decoded_instruction nondet (machine_address (base + offset)) registers offset =
    Some instruction ->
  (forall reg, read_reg_seq_state reg state = Some (registers reg)) ->
  sail_trace nondet
    (iMon_from_Sail nondet (Tiny_x86.decode (machine_address (base + offset))))
    state state
    (Some (@SailStdpp.Operators_mwords.add_vec_int 64
      (machine_address (base + offset)) size, instruction)).
Proof.
  intros Code At Instruction Registers.
  eapply decode_instruction_trace; [exact At|exact Instruction|exact Registers|].
  apply List.Forall_forall. intros event Event.
  apply in_map_iff in Event as [[fetched count] [Equal In]]. subst event.
  destruct (instruction_fetch_in_code offset size fetched count At In) as [Low High].
  now apply expected_fetch_from_code.
Qed.

Print Assumptions decode_from_code.
