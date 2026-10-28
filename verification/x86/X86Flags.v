(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From ASCommon Require Import Common.
From stdpp.bitvector Require Import tactics.
From SailStdpp Require Import MachineWord Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.

Lemma extract_concat_low m n1 n2 start count (high : bv n1) (low : bv n2) :
  (start + count <= n2)%N -> (m = n1 + n2)%N ->
  bv_extract start count (bv_concat m high low) = bv_extract start count low.
Proof.
  intros Range Width. apply bv_eq.
  rewrite !bv_extract_unsigned, bv_concat_unsigned, !bv_wrap_land by exact Width.
  apply Z.bits_inj_iff'. intros i Nonnegative.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec;
    try lia.
  case_bool_decide; rewrite ?andb_false_r, ?andb_true_r; [|reflexivity].
  rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma extract_whole n (value : bv n) : bv_extract 0 n value = value.
Proof. apply bv_eq. rewrite bv_extract_0_unsigned, bv_wrap_bv_unsigned. reflexivity. Qed.

Lemma extract_extract n start count outer width (value : bv n) :
  (start + count <= width)%N ->
  bv_extract start count (bv_extract outer width value) =
    bv_extract (outer + start) count value.
Proof.
  intro Range. apply bv_eq. rewrite !bv_extract_unsigned.
  apply Z.bits_inj_iff'. intros i Nonnegative.
  rewrite !bv_wrap_spec by lia.
  case_bool_decide; [|reflexivity]. cbn.
  rewrite !Z.shiftr_spec by lia.
  rewrite bv_wrap_spec_low by lia.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma extract_updated_bit_frame width index other (value : bv width) (bit : bv 1) :
  (index < width)%N -> (other < width)%N -> index <> other ->
  bv_extract other 1 (MachineWord.update_slice value index bit) =
    bv_extract other 1 value.
Proof.
  intros Index Other Different.
  unfold MachineWord.update_slice, MachineWord.slice.
  destruct (N.lt_ge_cases other index) as [Before|After].
  - rewrite extract_concat_low by lia.
    rewrite extract_concat_low by lia.
    rewrite extract_extract by lia.
    now rewrite N.add_0_l.
  - rewrite bv_extract_concat_later by lia.
    rewrite extract_extract by lia.
    replace (index + 1 + (other - (index + 1)))%N with other by lia.
    reflexivity.
Qed.

Lemma sign_flag_written (flags : bv 64) (bit : bv 1) :
  _get_rflags_type_SF (_update_rflags_type_SF flags bit) = bit.
Proof.
  change (bv_extract 7 1 (MachineWord.update_slice flags 7 bit) = bit).
  unfold MachineWord.update_slice, MachineWord.slice.
  rewrite extract_concat_low by reflexivity.
  rewrite bv_extract_concat_later by reflexivity.
  apply extract_whole.
Qed.

Lemma zero_flag_written (flags : bv 64) (bit : bv 1) :
  _get_rflags_type_ZF (_update_rflags_type_ZF flags bit) = bit.
Proof.
  change (bv_extract 6 1 (MachineWord.update_slice flags 6 bit) = bit).
  unfold MachineWord.update_slice, MachineWord.slice.
  rewrite extract_concat_low by reflexivity.
  rewrite bv_extract_concat_later by reflexivity.
  apply extract_whole.
Qed.

Print Assumptions sign_flag_written.

Lemma subrange64 (value : bv 64) : @subrange_vec_dec 64 value 63 0 = value.
Proof. change (bv_extract 0 64 value = value). apply extract_whole. Qed.

Lemma update64 (old value : bv 64) :
  @update_subrange_vec_dec 64 old 63 0 value = value.
Proof.
  change (MachineWord.update_slice old 0 value = value).
  unfold MachineWord.update_slice, MachineWord.slice.
  change (bv_concat 64 (bv_extract 64 0 old)
    (bv_concat 64 value (bv_extract 0 0 old)) = value).
  rewrite bv_concat_0 by apply bv_unsigned_N_0.
  rewrite bv_zero_extend_idemp. apply bv_eq.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_unsigned_N_0. cbn.
  rewrite Z.shiftl_0_r, Z.lor_0_r. reflexivity.
Qed.

Lemma sign_extend64 (value : bv 64) : @sign_extend 64 value 64 = value.
Proof. change (bv_sign_extend 64 value = value). apply bv_sign_extend_idemp. Qed.

Print Assumptions subrange64.
Print Assumptions update64.
Print Assumptions sign_extend64.

(* The arguments describe the six flag writes in update_rflags_sub/add.
   The instruction proofs establish their values using the Sail functions. *)
Definition result_flags (flags : bv 64) (sign overflow carry zero auxiliary parity : bv 1) : bv 64 :=
  MachineWord.update_slice
    (MachineWord.update_slice
      (MachineWord.update_slice
        (MachineWord.update_slice
          (MachineWord.update_slice
            (MachineWord.update_slice flags 7 sign) 11 overflow)
          0 carry) 6 zero) 4 auxiliary) 2 parity.

Lemma result_flags_sign flags sign overflow carry zero auxiliary parity :
  _get_rflags_type_SF (result_flags flags sign overflow carry zero auxiliary parity) = sign.
Proof.
  change (bv_extract 7 1 (result_flags flags sign overflow carry zero auxiliary parity) = sign).
  unfold result_flags. do 5 rewrite extract_updated_bit_frame by lia.
  exact (sign_flag_written flags sign).
Qed.

Lemma result_flags_zero flags sign overflow carry zero auxiliary parity :
  _get_rflags_type_ZF (result_flags flags sign overflow carry zero auxiliary parity) = zero.
Proof.
  change (bv_extract 6 1 (result_flags flags sign overflow carry zero auxiliary parity) = zero).
  unfold result_flags. do 2 rewrite extract_updated_bit_frame by lia.
  apply zero_flag_written.
Qed.

Print Assumptions result_flags_sign.
Print Assumptions result_flags_zero.

Lemma concat_empty_right n (value : bv n) (empty : bv 0) :
  bv_concat n value empty = value.
Proof.
  apply bv_eq. rewrite bv_concat_unsigned by lia.
  rewrite bv_unsigned_N_0. cbn.
  rewrite Z.shiftl_0_r, Z.lor_0_r. reflexivity.
Qed.

Lemma concat_empty_left n (empty : bv 0) (value : bv n) :
  bv_concat n empty value = value.
Proof.
  rewrite bv_concat_0 by apply bv_unsigned_N_0.
  apply bv_zero_extend_idemp.
Qed.

Lemma update32_zero_extend (old : bv 64) (value : bv 32) :
  @update_subrange_vec_dec 64
    (@update_subrange_vec_dec 64 old 63 32 (Z_to_bv 32 0)) 31 0 value =
  @zero_extend 32 value 64.
Proof.
  change (MachineWord.update_slice
    (MachineWord.update_slice old 32 (Z_to_bv 32 0)) 0 value =
    bv_zero_extend 64 value).
  unfold MachineWord.update_slice, MachineWord.slice.
  cbn [N.sub N.add].
  rewrite concat_empty_left, concat_empty_right.
  rewrite bv_extract_concat_later by reflexivity.
  rewrite extract_whole. apply bv_concat_0. reflexivity.
Qed.

Print Assumptions update32_zero_extend.

Lemma concat_adjacent_extracts n high low (value : bv n) :
  bv_concat (high + low) (bv_extract low high value) (bv_extract 0 low value) =
    bv_extract 0 (high + low) value.
Proof.
  apply bv_eq. rewrite bv_concat_unsigned by reflexivity.
  rewrite !bv_extract_unsigned.
  apply Z.bits_inj_iff'. intros i Nonnegative.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z_lt_ge_dec i (Z.of_N low)) as [Low|High].
  - rewrite Z.testbit_neg_r by lia.
    rewrite !bv_wrap_spec by lia. rewrite !Z.shiftr_spec by lia.
    rewrite N2Z.inj_add.
    repeat case_bool_decide; cbn; try lia; reflexivity.
  - rewrite !bv_wrap_spec by lia. rewrite !Z.shiftr_spec by lia.
    rewrite N2Z.inj_add.
    replace (i - Z.of_N low + Z.of_N low)%Z with i by lia.
    replace (i + Z.of_N 0)%Z with i by lia.
    repeat case_bool_decide; cbn; try lia; rewrite ?orb_false_r; reflexivity.
Qed.

Print Assumptions concat_adjacent_extracts.

Lemma bits_singleton (bit : bv 1) : vec_of_bits [bit] = bit.
Proof.
  unfold vec_of_bits.
  rewrite TypeCasts.cast_Z_refl.
  unfold Values.to_word_idx. rewrite MachineWord.cast_idx_refl.
  unfold MachineWord.word_list_concat. cbn.
  rewrite !MachineWord.cast_idx_refl.
  apply concat_empty_right.
Qed.

Print Assumptions bits_singleton.
