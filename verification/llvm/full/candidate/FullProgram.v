(* SPDX-License-Identifier: GPL-3.0-or-later *)
Require Import Normalize FullNormalize FullCandidate.

(* Syntax acceptance only. This value carries no semantic equivalence proof
   and must not be used as a certified module. *)
Definition prepared : {p : llvm_module | FullNormalize.normalize candidate = Some p}.
Proof. eexists; reflexivity. Defined.

Definition program : llvm_module := proj1_sig prepared.
