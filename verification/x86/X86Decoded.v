(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Flags X86Address X86Decode X86DecodeReplay.
Open Scope Z_scope.

Lemma decode_output_pointer nondet pc registers :
  decoded_instruction nondet pc registers 0 =
    Some (MOV (64, rm_REG (REG_NORMAL 10),
      rmi_MEM (@add_vec_int 64 (registers rsp) 8))).
Proof.
  destruct nondet;
  change (Some (MOV (64, rm_REG (REG_NORMAL 10),
    rmi_MEM (@add_vec 64
      (@add_vec 64 (@subrange_vec_dec 64 (registers rsp) 63 0)
        (Z_to_bv 64 0)) (Z_to_bv 64 8)))) =
    Some (MOV (64, rm_REG (REG_NORMAL 10),
      rmi_MEM (@add_vec_int 64 (registers rsp) 8))));
  rewrite subrange64, address_add_zero; reflexivity.
Qed.

Lemma decode_pushes nondet pc registers :
  map (decoded_instruction nondet pc registers) [5; 6; 8; 10; 12] =
    map (fun index => Some (PUSH (64, rmi_REG (REG_NORMAL index))))
      [3; 12; 13; 14; 15].
Proof. destruct nondet; reflexivity. Qed.

Print Assumptions decode_output_pointer.
Print Assumptions decode_pushes.

Lemma decode_output_zero nondet pc registers :
  decoded_instruction nondet pc registers 14 =
    Some (MOV (32, rm_MEM (registers r10), rmi_IMM (IMM32 (Z_to_bv 32 0)))).
Proof.
  destruct nondet;
  change (Some (MOV (32, rm_MEM (@subrange_vec_dec 64 (registers r10) 63 0),
    rmi_IMM (IMM32 (Z_to_bv 32 0)))) =
    Some (MOV (32, rm_MEM (registers r10), rmi_IMM (IMM32 (Z_to_bv 32 0)))));
  rewrite subrange64; reflexivity.
Qed.

Lemma decode_output_fields nondet pc registers offset displacement :
  List.In (offset, displacement) [(21, 4); (29, 8)] ->
  decoded_instruction nondet pc registers offset =
    Some (MOV (32, rm_MEM (@add_vec_int 64 (registers r10) displacement),
      rmi_IMM (IMM32 (Z_to_bv 32 0)))).
Proof.
  rewrite <- (subrange64 (registers r10)).
  intros [Same|[Same|Impossible]]; [inversion Same; subst|inversion Same; subst|contradiction];
    destruct nondet; reflexivity.
Qed.

Lemma decode_entry_control nondet pc registers :
  map (decoded_instruction nondet pc registers) [37; 40; 47; 53; 55; 58; 60] =
  [Some (CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM8 (Z_to_bv 8 0))));
   Some (JNS (Z_to_bv 8 5));
   Some (CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM32 (Z_to_bv 32 1025))));
   Some (JNS (Z_to_bv 8 10));
   Some (CMP (32, rm_REG (REG_NORMAL 7), rmi_IMM (IMM8 (Z_to_bv 8 0))));
   Some (JNE (Z_to_bv 8 10));
   Some (JMP32 (Z_to_bv 32 354))].
Proof. destruct nondet; reflexivity. Qed.
