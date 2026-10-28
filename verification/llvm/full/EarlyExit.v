(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
Require Import ClightMemory.
From Vellvm Require Import Syntax TypToDtyp Params ParamsV IPtrInfinite
  DynamicValues LLVMEvents Denotation InterpretationStack EOU Operations Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG
  Entry Index Prefix CheckedPrefix Cleanup.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Lemma check_empty_zero from varargs s n :
  Int.unsigned n = 0 ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  runs (denote_block (proj1_sig FullCFG.check_empty) from varargs) s
    (set_local s (Name "cmp3") (boolean_value true)) (inl (Name "cleanup")).
Proof.
  intros Zero N. eapply runs_block_no_phis.
  - eapply runs_code_cons.
    + apply runs_assign with (value := boolean_value true).
      eapply runs_expression_icmp.
      * entry_lookup.
      * apply runs_expression_integer. resolve_types. reflexivity.
      * change (eval_icmp false Eq (word_value n) (word_value Int.zero) =
          raise_ret (boolean_value true)).
        rewrite word_eq, Zero. reflexivity.
    + apply runs_code_nil.
  - change (runs (denote_terminator (IVoid 4,
      TERM_Br (typ_to_dtyp [] (TYPE_I 1), EXP_Ident (ID_Local (Name "cmp3")))
        (Name "cleanup") (Name "if.end10.preheader"), []))
      (set_local s (Name "cmp3") (boolean_value true))
      (set_local s (Name "cmp3") (boolean_value true)) (inl (Name "cleanup"))).
    resolve_types. apply runs_branch with (choice := true). entry_lookup.
Qed.

(* These paths need only the output cells. The other pointer arguments do
   not occur on either path, and their arrays remain unchanged. *)
Theorem oversized_path layout output n varargs c s :
  1024 < Int.unsigned n ->
  (3 <= block_words layout output)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  exists c' s', output_stores c output c' /\
    cells_related layout c' (fst s') /\ array_at c' output [0; 0; 0] /\
    block_path (blks FullCFG.body) varargs (Name "entry") (Name "entry") s s'
      (word_value (Int.repr 2)) /\
    (forall other values, other <> output -> array_at c other values -> array_at c' other values).
Proof.
  intros Large Capacity Related N Output.
  destruct (@entry_related layout c s n output (Name "entry") varargs Related Capacity N Output)
    as [c1 [s1 [Stores [Related1 [Entry [Other Fields]]]]]].
  assert (Test : (1024 <? Int.unsigned n) = true) by (apply Z.ltb_lt; exact Large).
  rewrite Test in Entry.
  exists c1, (cleanup_state s1 2). split; [exact Stores|]. split.
  - rewrite cleanup_memory. exact Related1.
  - split; [eapply output_stores_zero; exact Stores|]. split.
    + eapply path_jump; [exact (proj2_sig FullCFG.entry)|exact Entry|].
      apply cleanup_path, cleanup_oversized.
    + intros other values Separate Array. eapply output_stores_array; eassumption.
Qed.

Theorem empty_path layout output n varargs c s :
  Int.unsigned n = 0 ->
  (3 <= block_words layout output)%nat ->
  cells_related layout c (fst s) ->
  Maps.lookup (Name "v1") (locals s) = Some (word_value n) ->
  Maps.lookup (Name "v7") (locals s) = Some
    (pointer_value (block_address layout output) (block_provenance layout output)) ->
  exists c' s', output_stores c output c' /\
    cells_related layout c' (fst s') /\ array_at c' output [0; 0; 0] /\
    block_path (blks FullCFG.body) varargs (Name "entry") (Name "entry") s s'
      (word_value Int.zero) /\
    (forall other values, other <> output -> array_at c other values -> array_at c' other values).
Proof.
  intros Zero Capacity Related N Output.
  destruct (@entry_related layout c s n output (Name "entry") varargs Related Capacity N Output)
    as [c1 [s1 [Stores [Related1 [Entry [Other Fields]]]]]].
  rewrite Zero in Entry.
  assert (N1 : Maps.lookup (Name "v1") (locals s1) = Some (word_value n)).
  { rewrite Other by (unfold entry_unmodified; repeat split; discriminate). exact N. }
  pose (s2 := set_local s1 (Name "cmp3") (boolean_value true)).
  assert (Empty : runs (denote_block (proj1_sig FullCFG.check_empty) (Name "entry") varargs)
      s1 s2 (inl (Name "cleanup"))).
  { apply check_empty_zero with (n := n); assumption. }
  exists c1, (cleanup_state s2 0). split; [exact Stores|]. split.
  - rewrite cleanup_memory. unfold s2. rewrite memory_set_local. exact Related1.
  - split; [eapply output_stores_zero; exact Stores|]. split.
    + eapply path_jump; [exact (proj2_sig FullCFG.entry)|exact Entry|].
      eapply path_jump; [exact (proj2_sig FullCFG.check_empty)|exact Empty|].
      apply cleanup_path, cleanup_empty.
    + intros other values Separate Array. eapply output_stores_array; eassumption.
Qed.
