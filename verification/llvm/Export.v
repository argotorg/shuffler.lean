(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Vellvm Require Import ShowAST.
Require Import Equivalence.

(* Both the theorem and the printer use the value in this dependent pair.
   Extraction erases its proof, after Rocq has checked it. *)
Definition emitted_llvm := showProg (proj1_sig certified_module).
Extraction "exported.ml" emitted_llvm.
