(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Memory X86ABI.
Import ListNotations.
Open Scope Z_scope.

Lemma address_index base offset index :
  addr_addN (machine_address (base + Z.of_nat offset)) (N.of_nat index) =
    machine_address (base + Z.of_nat (offset + index)).
Proof.
  unfold addr_addN, machine_address. apply bv_eq.
  rewrite bv_add_Z_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

Lemma code_byte_exists (code : list (bv 8)) offset size index :
  (offset + N.to_nat size <= List.length code)%nat ->
  (index < N.to_nat size)%nat ->
  exists byte, nth_error code (offset + index) = Some byte.
Proof.
  intros Bounds Index.
  destruct (nth_error code (offset + index)) as [byte|] eqn:Byte;
    [eauto|].
  apply nth_error_None in Byte. lia.
Qed.

Lemma code_slice_byte_lookups state base code offset size :
  code_at state base code ->
  (offset + N.to_nat size <= List.length code)%nat ->
  map ((archState.memory (sst state)) !!.)
    (addr_range (machine_address (base + Z.of_nat offset)) size) =
  map Some (firstn (N.to_nat size) (skipn offset code)).
Proof.
  intros Code Bounds. apply nth_error_ext. intro index.
  unfold addr_range, seqN.
  rewrite !map_map, !nth_error_map, nth_error_seq,
    nth_error_firstn, nth_error_skipn.
  destruct (index <? N.to_nat size)%nat eqn:Index; [|reflexivity].
  apply Nat.ltb_lt in Index.
  destruct (code_byte_exists code offset size index Bounds Index) as [byte Byte].
  rewrite Byte. cbn. rewrite address_index.
  change (Some (archState.memory (sst state) !!
    machine_address (base + Z.of_nat (offset + index))) = Some (Some byte)).
  unfold code_at, read_byte_seq_state in Code.
  now rewrite (proj1 (Code _ _ Byte)).
Qed.

Lemma list_of_some {A} (values : list A) :
  list_of_options (map Some values) = Some values.
Proof.
  induction values as [|head tail IH]; [reflexivity|].
  change (match list_of_options (map Some tail) with
    | Some values => Some (head :: values)
    | None => None
    end = Some (head :: tail)).
  now rewrite IH.
Qed.

Lemma code_slice_read state base code offset size :
  code_at state base code ->
  (offset + N.to_nat size <= List.length code)%nat ->
  read_mem_seq_state size (machine_address (base + Z.of_nat offset)) state =
    Some (bv_of_bytes (8 * size)
      (firstn (N.to_nat size) (skipn offset code))).
Proof.
  intros Code Bounds. rewrite read_mem_is_lookup.
  change (option_map (bv_of_bytes (8 * size))
    (list_of_options (map ((archState.memory (sst state)) !!.)
      (addr_range (machine_address (base + Z.of_nat offset)) size))) =
    Some (bv_of_bytes (8 * size)
      (firstn (N.to_nat size) (skipn offset code)))).
  rewrite (code_slice_byte_lookups state base code offset size Code Bounds),
    list_of_some. reflexivity.
Qed.

Lemma code_slice_untouched state base code offset size :
  code_at state base code ->
  (offset + N.to_nat size <= List.length code)%nat ->
  mem_was_written size (machine_address (base + Z.of_nat offset)) state = false.
Proof.
  intros Code Bounds. apply untouched_fetch. intros address In.
  unfold addr_range, seqN in In.
  apply in_map_iff in In as [n [Address In]].
  apply in_map_iff in In as [index [Number In]].
  apply in_seq in In. cbn in In. subst n.
  rewrite address_index in Address. subst address.
  destruct (code_byte_exists code offset size index Bounds ltac:(lia))
    as [byte Byte].
  exact (proj2 (Code _ _ Byte)).
Qed.

Lemma code_slice_fetch state base code offset size :
  code_at state base code ->
  (offset + N.to_nat size <= List.length code)%nat ->
  sequential_model_outcome None
    (MemRead (MemReq.make (Tiny_x86.create_iFetchAccessDescriptor tt)
      (machine_address (base + Z.of_nat offset)) tt size 0)) state =
    Exec.make [(state, Ok (bv_of_bytes (8 * size)
      (firstn (N.to_nat size) (skipn offset code)), bv_0 0))] [].
Proof.
  intros Code Bounds. apply fetch_read_seq.
  - apply (code_slice_read state base code offset size Code Bounds).
  - apply (code_slice_untouched state base code offset size Code Bounds).
Qed.

Print Assumptions code_slice_read.
Print Assumptions code_slice_fetch.
