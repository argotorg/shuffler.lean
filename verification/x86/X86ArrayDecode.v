(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions X86Flags X86Program X86Decode X86DecodeReplay.
Import ListNotations.
Open Scope Z_scope.

Definition gpr64 (registers : register_values) index : bv 64 :=
  Values.to_ty (gpr_reference index) (registers (Values.reg (gpr_reference index))).

Definition scaled_gprs (values : Z -> bv 64) base index : bv 64 :=
  @add_vec 64 (values base) (@shiftl 64 (values index) 2).

Definition scaled_address registers base index : bv 64 :=
  scaled_gprs (gpr64 registers) base index.

(* Each row is (offset, size, destination, base, index). These rows state
   expected ASTs; the proofs below run the actual Sail decoder on the bytes. *)
Definition array_load_sites : list (Z * Z * Z * Z * Z) :=
  [(89, 4, 11, 2, 0); (109, 4, 3, 8, 11); (126, 3, 3, 6, 0);
   (149, 4, 11, 6, 0); (153, 3, 3, 1, 0); (187, 4, 11, 6, 0);
   (191, 3, 3, 1, 0); (204, 4, 3, 8, 13); (213, 4, 3, 1, 13);
   (275, 4, 13, 2, 12); (296, 4, 3, 2, 13); (311, 4, 3, 2, 13);
   (322, 4, 0, 6, 13); (326, 4, 3, 6, 12);
   (398, 4, 0, 2, 13); (402, 4, 3, 2, 12)].

(* Each row is (offset, size, source, base, index). *)
Definition array_store_sites : list (Z * Z * Z * Z * Z) :=
  [(129, 4, 3, 1, 11); (166, 3, 0, 2, 0); (174, 4, 3, 8, 0);
   (243, 4, 13, 2, 0); (356, 4, 3, 6, 13); (360, 4, 0, 6, 12);
   (364, 4, 14, 9, 11); (406, 4, 3, 2, 13); (410, 4, 0, 2, 12)].

(* Each row is (offset, size, immediate, base, index). *)
Definition array_immediate_sites : list (Z * Z * Z * Z * Z) :=
  [(72, 8, 0, 8, 0); (118, 8, 1, 8, 11); (247, 8, 1, 8, 13)].

Definition array_site_offset (site : Z * Z * Z * Z * Z) : Z :=
  let '(offset, _, _, _, _) := site in offset.

Definition array_site_instruction (site : Z * Z * Z * Z * Z) : Z * Z :=
  let '(offset, size, _, _, _) := site in (offset, size).

Definition array_load_ast (values : Z -> bv 64) (site : Z * Z * Z * Z * Z) : ast :=
  let '(_, _, destination, base, index) := site in
  MOV (32, rm_REG (REG_NORMAL destination), rmi_MEM (scaled_gprs values base index)).

Definition array_store_ast (values : Z -> bv 64) (site : Z * Z * Z * Z * Z) : ast :=
  let '(_, _, source, base, index) := site in
  MOV (32, rm_MEM (scaled_gprs values base index), rmi_REG (REG_NORMAL source)).

Definition array_immediate_ast (values : Z -> bv 64) (site : Z * Z * Z * Z * Z) : ast :=
  let '(_, _, immediate, base, index) := site in
  MOV (32, rm_MEM (scaled_gprs values base index), rmi_IMM (IMM32 (Z_to_bv 32 immediate))).

Definition decoded_gprs registers index : bv 64 :=
  @subrange_vec_dec 64 (gpr64 registers index) 63 0.

Lemma array_load_table_decodes nondet pc registers :
  map (fun site => decoded_instruction nondet pc registers (array_site_offset site))
    array_load_sites =
  map (fun site => Some (array_load_ast (decoded_gprs registers) site)) array_load_sites.
Proof. destruct nondet; reflexivity. Qed.

Lemma array_store_table_decodes nondet pc registers :
  map (fun site => decoded_instruction nondet pc registers (array_site_offset site))
    array_store_sites =
  map (fun site => Some (array_store_ast (decoded_gprs registers) site)) array_store_sites.
Proof. destruct nondet; reflexivity. Qed.

Lemma array_immediate_table_decodes nondet pc registers :
  map (fun site => decoded_instruction nondet pc registers (array_site_offset site))
    array_immediate_sites =
  map (fun site => Some (array_immediate_ast (decoded_gprs registers) site)) array_immediate_sites.
Proof. destruct nondet; reflexivity. Qed.

Lemma scaled_gprs_normalized registers base index :
  scaled_gprs (decoded_gprs registers) base index = scaled_address registers base index.
Proof. unfold scaled_gprs, decoded_gprs, scaled_address. now rewrite !subrange64. Qed.

Theorem decode_array_load nondet pc registers offset size destination base index :
  In (offset, size, destination, base, index) array_load_sites ->
  decoded_instruction nondet pc registers offset =
    Some (MOV (32, rm_REG (REG_NORMAL destination),
      rmi_MEM (scaled_address registers base index))).
Proof.
  intro Site.
  pose proof (equal_maps_at _ _ _ _ (array_load_table_decodes nondet pc registers) Site) as Decode.
  cbn [array_site_offset array_load_ast] in Decode.
  now rewrite scaled_gprs_normalized in Decode.
Qed.

Theorem decode_array_store nondet pc registers offset size source base index :
  In (offset, size, source, base, index) array_store_sites ->
  decoded_instruction nondet pc registers offset =
    Some (MOV (32, rm_MEM (scaled_address registers base index),
      rmi_REG (REG_NORMAL source))).
Proof.
  intro Site.
  pose proof (equal_maps_at _ _ _ _ (array_store_table_decodes nondet pc registers) Site) as Decode.
  cbn [array_site_offset array_store_ast] in Decode.
  now rewrite scaled_gprs_normalized in Decode.
Qed.

Theorem decode_array_immediate nondet pc registers offset size immediate base index :
  In (offset, size, immediate, base, index) array_immediate_sites ->
  decoded_instruction nondet pc registers offset =
    Some (MOV (32, rm_MEM (scaled_address registers base index),
      rmi_IMM (IMM32 (Z_to_bv 32 immediate)))).
Proof.
  intro Site.
  pose proof (equal_maps_at _ _ _ _ (array_immediate_table_decodes nondet pc registers) Site) as Decode.
  cbn [array_site_offset array_immediate_ast] in Decode.
  now rewrite scaled_gprs_normalized in Decode.
Qed.

Lemma array_sites_are_instructions :
  Forall (fun site => In (array_site_instruction site) program_instructions)
    (array_load_sites ++ array_store_sites ++ array_immediate_sites).
Proof. vm_compute. repeat (constructor 2; [tauto|]). constructor 1. Qed.

Lemma array_load_instruction offset size destination base index :
  In (offset, size, destination, base, index) array_load_sites ->
  In (offset, size) program_instructions.
Proof.
  intro Site.
  pose proof array_sites_are_instructions as All.
  apply List.Forall_forall with (x := (offset, size, destination, base, index)) in All;
    [exact All|apply in_or_app; now left].
Qed.

Lemma array_store_instruction offset size source base index :
  In (offset, size, source, base, index) array_store_sites ->
  In (offset, size) program_instructions.
Proof.
  intro Site.
  pose proof array_sites_are_instructions as All.
  apply List.Forall_forall with (x := (offset, size, source, base, index)) in All;
    [exact All|apply in_or_app; right; apply in_or_app; now left].
Qed.

Lemma array_immediate_instruction offset size immediate base index :
  In (offset, size, immediate, base, index) array_immediate_sites ->
  In (offset, size) program_instructions.
Proof.
  intro Site.
  pose proof array_sites_are_instructions as All.
  apply List.Forall_forall with (x := (offset, size, immediate, base, index)) in All;
    [exact All|apply in_or_app; right; apply in_or_app; now right].
Qed.

Print Assumptions decode_array_load.
Print Assumptions decode_array_store.
Print Assumptions decode_array_immediate.
