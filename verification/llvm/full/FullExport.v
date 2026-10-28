(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Vellvm Require Import ShowAST.
Require Import FullContract.

(* Print the exact AST paired with the checked complete-call proof. *)
Definition emitted_llvm := showProg (proj1_sig certified_module).
Extraction "full_exported.ml" emitted_llvm.
