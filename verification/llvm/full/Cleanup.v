(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith.
From compcert Require Import Integers.
From Vellvm Require Import Utils Syntax TypToDtyp ScopeTheory Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory Control Instructions FullCFG Entry.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition cleanup : {b : LLVMAst.block dtyp | FullCFG.named_block "cleanup" = Some b}.
Proof.
  eexists; unfold FullCFG.named_block.
  do 34 (eapply eq_trans; [apply find_block_ineq; discriminate|]).
  apply find_block_eq; reflexivity.
Defined.

(* Each constructor identifies an actual predecessor and its phi operand. *)
Inductive cleanup_result : block_id -> Z -> Prop :=
| cleanup_blocked : cleanup_result (Name "if.then142") 1
| cleanup_oversized : cleanup_result (Name "entry") 2
| cleanup_empty : cleanup_result (Name "if.end") 0
| cleanup_done : cleanup_result (Name "while.end125") 0
| cleanup_capacity : cleanup_result (Name "if.end147") 2
| cleanup_search : cleanup_result (Name "while.end93") 2
| cleanup_range : cleanup_result (Name "if.end17") 2
| cleanup_duplicate : cleanup_result (Name "if.end23") 2.

Definition cleanup_state s code := set_local s (Name "retval.0") (word_value (Int.repr code)).

Lemma cleanup_memory s code : fst (cleanup_state s code) = fst s.
Proof. apply memory_set_local. Qed.

Lemma cleanup_other s code id : id <> Name "retval.0" ->
  Maps.lookup id (locals (cleanup_state s code)) = Maps.lookup id (locals s).
Proof. apply lookup_local_other. Qed.

Lemma cleanup_runs from code varargs s : cleanup_result from code ->
  runs (denote_block (proj1_sig cleanup) from varargs) s (cleanup_state s code)
    (inr (word_value (Int.repr code))).
Proof.
  intro Result. eapply runs_block with (after_phis := cleanup_state s code)
    (middle := cleanup_state s code).
  - destruct Result; eapply runs_phis_single.
    all: try solve [repeat first [apply assoc_hd | eapply eq_trans; [apply assoc_tl; discriminate|]]].
    all: apply runs_expression_integer; resolve_types; reflexivity.
  - apply runs_code_nil.
  - apply runs_return. unfold cleanup_state. entry_lookup.
Qed.

Lemma cleanup_path from code varargs s : cleanup_result from code ->
  block_path (blks FullCFG.body) varargs from (Name "cleanup") s
    (cleanup_state s code) (word_value (Int.repr code)).
Proof.
  intro Result. eapply path_return; [exact (proj2_sig cleanup)|].
  apply cleanup_runs, Result.
Qed.

Lemma block_steps_return blocks varargs from label s last_from last_label middle final value :
  block_steps blocks varargs from label s last_from last_label middle ->
  block_path blocks varargs last_from last_label middle final value ->
  block_path blocks varargs from label s final value.
Proof.
  intros Steps Path. induction Steps; [exact Path|].
  eapply path_jump; eauto.
Qed.

Theorem cleanup_after_steps varargs from label s previous middle code :
  block_steps (blks FullCFG.body) varargs from label s previous (Name "cleanup") middle ->
  cleanup_result previous code ->
  block_path (blks FullCFG.body) varargs from label s
    (cleanup_state middle code) (word_value (Int.repr code)).
Proof.
  intros Steps Result. eapply block_steps_return; [exact Steps|].
  apply cleanup_path, Result.
Qed.
