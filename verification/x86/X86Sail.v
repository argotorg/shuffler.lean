(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import MachineWord Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Instructions.
Import ListNotations.

Lemma trace_bind {A B} nondet (program : iMon A) (next : A -> iMon B)
    state middle final value result :
  sail_trace nondet program state middle value ->
  sail_trace nondet (next value) middle final result ->
  sail_trace nondet (program ≫= next) state final result.
Proof.
  intros First Last. induction First; [exact Last|].
  cbn [mbind FMon.fMon_bind]. econstructor; [exact H|].
  apply IHFirst, Last.
Qed.

Lemma trace_sail_bind {A B} nondet (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) state middle final value result :
  sail_trace nondet (iMon_from_Sail nondet program) state middle value ->
  sail_trace nondet (iMon_from_Sail nondet (next value)) middle final result ->
  sail_trace nondet (iMon_from_Sail nondet
    (Tiny_x86_types.Defs.bind program next)) state final result.
Proof.
  intros First Last. rewrite sail_adapter_bind.
  exact (@trace_bind A B nondet (iMon_from_Sail nondet program)
    (fun x => iMon_from_Sail nondet (next x)) state middle final value result First Last).
Qed.


Lemma sail_bind_assoc {A B C} (program : Tiny_x86_types.M A)
    (next : A -> Tiny_x86_types.M B) (last : B -> Tiny_x86_types.M C) :
  Tiny_x86_types.Defs.bind (Tiny_x86_types.Defs.bind program next) last =
    Tiny_x86_types.Defs.bind program
      (fun value => Tiny_x86_types.Defs.bind (next value) last).
Proof.
  induction program as [value|T outcome resume IH]; cbn; [reflexivity|].
  f_equal. apply functional_extensionality. intro value. apply IH.
Qed.

Print Assumptions trace_sail_bind.
Print Assumptions sail_bind_assoc.
