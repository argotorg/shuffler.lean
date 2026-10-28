(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From ITree Require Import ITree.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix MainLoop Cleanup.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Record permute_registers layout d bd bp bt bu trace output s : Prop := {
  argument_size : Maps.lookup (Name "v1") (locals s) =
    Some (word_value (Int.repr (Z.of_nat (S d))));
  argument_data : Maps.lookup (Name "v2") (locals s) =
    Some (pointer_value (block_address layout bd) (block_provenance layout bd));
  argument_permutation : Maps.lookup (Name "v3") (locals s) =
    Some (pointer_value (block_address layout bp) (block_provenance layout bp));
  argument_target : Maps.lookup (Name "v4") (locals s) =
    Some (pointer_value (block_address layout bt) (block_provenance layout bt));
  argument_used : Maps.lookup (Name "v5") (locals s) =
    Some (pointer_value (block_address layout bu) (block_provenance layout bu));
  argument_trace : Maps.lookup (Name "v6") (locals s) =
    Some (pointer_value (block_address layout trace) (block_provenance layout trace));
  argument_output : Maps.lookup (Name "v7") (locals s) =
    Some (pointer_value (block_address layout output) (block_provenance layout output))
}.

Section Body.
Context (layout : allocation_layout) (d : nat) (bd bp bt bu trace output : Values.block).
Hypothesis Separate : separate_arrays bd bp bt bu trace output.
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (S d <= block_words layout bt)%coq_nat)
    (CU : (S d <= block_words layout bu)%coq_nat)
    (CR : (2 * S d <= block_words layout trace)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Theorem permute_body_path (source : 'I_(S d) -> nat) (p : 'S_(S d)) c s varargs :
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun i => nat_of_ord (p i))) ->
  permute_registers layout d bd bp bt bu trace output s ->
  exists result c' s' code,
    solc_permute source p = Some result /\
    cells_related layout c' (fst s') /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output result c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs (Name "entry") (Name "entry") s s'
      (word_value (Int.repr code)) /\
    (forall other xs, other <> bd -> other <> bp -> other <> bt -> other <> bu ->
      other <> trace -> other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Values Related Data Perm Registers.
  destruct Separate as [DP DT DU DR DO PT PU PR PO TU TR TO UR UO RO].
  destruct Registers as [N D P T U R O].
  destruct (@main_prefix layout d source p bd bp bt bu trace output Size Values
    DP DU DT PU PT TU DO PO ltac:(congruence) ltac:(congruence)
    CD CP CT CU CR CO varargs c s Related Data Perm N D P T U R O)
    as [q [c1 [s1 [Normalized [Related1 [Arrays1 [Registers1 [Prefix Frame1]]]]]]]].
  destruct (@MainLoop.main_loop_nonempty layout d bd bp trace output
    DP DR DO PR PO RO Size CD CP CR CO source q c1 s1 (Name "while.end105") varargs
    Values Related1 Arrays1 Registers1)
    as [c' [s' [code [Related' [Code [Result [Loop Frame2]]]]]]].
  exists (solc_nonempty source q), c', s', code. split.
  - unfold solc_permute. rewrite Normalized. reflexivity.
  - split; [exact Related'|]. split; [exact Code|]. split; [exact Result|]. split.
    + eapply block_steps_return; [exact Prefix|exact Loop].
    + intros other xs ND NP NT NU NR NO A.
      apply Frame2; try assumption. apply Frame1; assumption.
Qed.

Theorem permute_body_refines (source : 'I_(S d) -> nat) (p : 'S_(S d)) c s varargs :
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst s) ->
  array_at c bd (words source) -> array_at c bp (words (fun i => nat_of_ord (p i))) ->
  permute_registers layout d bd bp bt bu trace output s ->
  exists result c' s' code,
    solc_permute source p = Some result /\
    cells_related layout c' (fst s') /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output result c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    runs (denote_cfg FullCFG.body varargs) s s' (word_value (Int.repr code)) /\
    (forall other xs, other <> bd -> other <> bp -> other <> bt -> other <> bu ->
      other <> trace -> other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Values Related Data Perm Registers.
  destruct (permute_body_path source p c s varargs Values Related Data Perm Registers)
    as [result [c' [s' [code [Model [Related' [Code [Result [Path Frame]]]]]]]]].
  exists result, c', s', code. split; [exact Model|]. split; [exact Related'|].
  split; [exact Code|]. split; [exact Result|]. split; [|exact Frame].
  unfold denote_cfg, denote_cfg_map.
  eapply runs_bind with (middle := s') (x := inr (word_value (Int.repr code))).
  - change (runs (denote_ocfg (blks FullCFG.body) varargs
      (Name "entry", Name "entry")) s s' (inr (word_value (Int.repr code)))).
    apply block_path_sound, Path.
  - apply runs_ret.
Qed.
End Body.
