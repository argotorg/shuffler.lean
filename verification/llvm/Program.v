(* SPDX-License-Identifier: GPL-3.0-or-later *)
Require Import Candidate Normalize.

(* A rejected candidate cannot produce a program through this definition. *)
Definition accepted : {p : llvm_module | normalize candidate = Some p}.
Proof. eexists; vm_compute; reflexivity. Defined.

Definition program : llvm_module := proj1_sig accepted.
