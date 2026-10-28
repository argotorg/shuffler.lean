(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String.
From Vellvm Require Import Syntax TypToDtyp ScopeTheory.
Require Import FullProgram.
Import ListNotations.
Open Scope string_scope.

(* These are the CFG and blocks constructed by Vellvm from the imported,
   normalized full module. They are not copies of the LLVM source. *)
Definition llvm_module := convert_types (mcfg_of_tle FullProgram.program).

Definition single_function :
    {f : definition dtyp (cfg dtyp) | m_definitions llvm_module = [f]}.
Proof. eexists; reflexivity. Defined.

Definition function := proj1_sig single_function.
Definition body := df_instrs function.
Definition named_block name := find_block (blks body) (Name name).

Definition entry : {b : block dtyp | named_block "entry" = Some b}.
Proof. eexists; unfold named_block; apply find_block_eq; reflexivity. Defined.

Definition initialize_used :
    {b : block dtyp | named_block "if.end10" = Some b}.
Proof.
  eexists; unfold named_block.
  do 3 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition check_empty : {b : block dtyp | named_block "if.end" = Some b}.
Proof.
  eexists; unfold named_block.
  eapply eq_trans; [apply find_block_ineq; discriminate|].
  apply find_block_eq; reflexivity.
Defined.

Definition initialize_preheader :
    {b : block dtyp | named_block "if.end10.preheader" = Some b}.
Proof.
  eexists; unfold named_block.
  do 2 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Lemma entry_label : init body = Name "entry".
Proof. reflexivity. Qed.

Lemma function_name : dc_name (df_prototype function) = Name "permute".
Proof. reflexivity. Qed.

Definition validation_preheader :
    {b : block dtyp | named_block "if.end17.preheader" = Some b}.
Proof.
  eexists; unfold named_block.
  do 4 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition validation_range : {b : block dtyp | named_block "if.end17" = Some b}.
Proof.
  eexists; unfold named_block.
  do 5 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition validation_unused : {b : block dtyp | named_block "if.end23" = Some b}.
Proof.
  eexists; unfold named_block.
  do 6 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition validation_store : {b : block dtyp | named_block "if.end29" = Some b}.
Proof.
  eexists; unfold named_block.
  do 7 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fixed_preheader : {b : block dtyp | named_block "if.end43.preheader" = Some b}.
Proof.
  eexists; unfold named_block.
  do 8 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fixed_compare : {b : block dtyp | named_block "if.end43" = Some b}.
Proof.
  eexists; unfold named_block.
  do 9 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fixed_assign : {b : block dtyp | named_block "if.then49" = Some b}.
Proof.
  eexists; unfold named_block.
  do 10 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

Definition fixed_merge : {b : block dtyp | named_block "if.end57" = Some b}.
Proof.
  eexists; unfold named_block.
  do 11 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.
