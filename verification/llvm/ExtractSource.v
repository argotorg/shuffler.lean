(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString DecimalString ZArith.
Require Import ClightDepth.
Definition decimal_int (v : Integers.Int.int) :=
  DecimalString.NilZero.string_of_int (Z.to_int (Integers.Int.unsigned v)).
Definition decimal_ident (v : BinNums.positive) :=
  DecimalString.NilZero.string_of_uint (Pos.to_uint v).
Extraction "extracted.ml" depth_function Permute.u32 Permute.i32 Permute.ptr
  decimal_int decimal_ident.
