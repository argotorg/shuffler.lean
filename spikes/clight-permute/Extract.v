(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString DecimalString ZArith.
Require Import Permute.

(* Keep Coq integers. Do not replace arithmetic with host machine arithmetic.
   This extracts the AST only; it imports no compiler or parser pass. *)
Definition decimal_int (v : Integers.Int.int) :=
  DecimalString.NilZero.string_of_int (Z.to_int (Integers.Int.unsigned v)).
Definition decimal_ident (v : BinNums.positive) :=
  DecimalString.NilZero.string_of_uint (Pos.to_uint v).

Extraction Language OCaml.
Extraction "extracted.ml" permute u32 i32 ptr decimal_int decimal_ident.
