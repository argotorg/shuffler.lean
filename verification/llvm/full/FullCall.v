(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry
  MainBody CallBoundary BodyFrame NoException BodyNoException EarlyExit.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem full_call_from_path caller body n data perm target used trace output value :
  block_path (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
    (Name "entry") (Name "entry")
    (call_state caller n data perm target used trace output) body value ->
  runs (denote_function FullCFG.function [n; data; perm; target; used; trace; output])
    caller (returned_state caller body) (inr value).
Proof.
  intro Path.
  pose proof (full_block_path_frame Path) as Structure.
  destruct (call_state_structure caller n data perm target used trace output)
    as [Frames [Stack Globals]].
  assert (MemoryFrame : Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst body)) =
      Impl.Snoc (Impl.Memory_stack_frame_stack (Impl.state_memory_stack (fst caller))) []).
  { transitivity (Impl.Memory_stack_frame_stack (Impl.state_memory_stack
      (fst (call_state caller n data perm target used trace output)))); [|exact Frames].
    exact (f_equal (fun x => fst (fst (fst (fst x)))) Structure). }
  assert (LocalStack : snd (fst (snd body)) = fst (fst (snd caller)) :: snd (fst (snd caller))).
  { transitivity (snd (fst (snd (call_state caller n data perm target used trace output))));
      [|exact Stack]. exact (f_equal (fun x => snd (fst x)) Structure). }
  assert (GlobalEnv : snd (snd body) = snd (snd caller)).
  { transitivity (snd (snd (call_state caller n data perm target used trace output)));
      [|exact Globals]. exact (f_equal snd Structure). }
  apply call_denotation_runs; try assumption.
  apply runs_run_exc; [apply full_body_exception_free|].
  unfold denote_cfg, denote_cfg_map.
  eapply runs_bind with (middle := body) (x := inr value).
  - change (runs (denote_ocfg (blks FullCFG.body) (Some (empty_varargs_pointer (fst caller)))
      (Name "entry", Name "entry"))
      (call_state caller n data perm target used trace output) body (inr value)).
    apply block_path_sound, Path.
  - apply runs_ret.
Qed.

Definition mapped_pointer layout b :=
  pointer_value (block_address layout b) (block_provenance layout b).

Definition permute_arguments layout n bd bp bt bu trace output :=
  [word_value n; mapped_pointer layout bd; mapped_pointer layout bp;
   mapped_pointer layout bt; mapped_pointer layout bu; mapped_pointer layout trace;
   mapped_pointer layout output].

Section Call.
Context (layout : allocation_layout) (d : nat) (bd bp bt bu trace output : Values.block).
Hypothesis Separate : separate_arrays bd bp bt bu trace output.
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (S d <= block_words layout bt)%coq_nat)
    (CU : (S d <= block_words layout bu)%coq_nat)
    (CR : (2 * S d <= block_words layout trace)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Theorem permute_call_refines (source : 'I_(S d) -> nat) (p : 'S_(S d)) c caller :
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst caller) ->
  array_at c bd (words source) -> array_at c bp (words (fun i => nat_of_ord (p i))) ->
  exists result c' final code,
    solc_permute source p = Some result /\
    cells_related layout c' (fst final) /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output result c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    runs (denote_function FullCFG.function
      (permute_arguments layout (Int.repr (Z.of_nat (S d))) bd bp bt bu trace output))
      caller final (inr (word_value (Int.repr code))) /\
    snd final = snd caller /\
    (forall other xs, other <> bd -> other <> bp -> other <> bt -> other <> bu ->
      other <> trace -> other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Values Related Data Perm.
  pose (initial := call_state caller (word_value (Int.repr (Z.of_nat (S d))))
    (mapped_pointer layout bd) (mapped_pointer layout bp) (mapped_pointer layout bt)
    (mapped_pointer layout bu) (mapped_pointer layout trace) (mapped_pointer layout output)).
  assert (RelatedInitial : cells_related layout c (fst initial)).
  { apply call_state_related, Related. }
  assert (Registers : permute_registers layout d bd bp bt bu trace output initial).
  { destruct (call_state_bindings caller (word_value (Int.repr (Z.of_nat (S d))))
      (mapped_pointer layout bd) (mapped_pointer layout bp) (mapped_pointer layout bt)
      (mapped_pointer layout bu) (mapped_pointer layout trace) (mapped_pointer layout output))
      as [N [D [P [T [U [R O]]]]]]. constructor; assumption. }
  destruct (@permute_body_path layout d bd bp bt bu trace output Separate Size CD CP CT CU CR CO
    source p c initial (Some (empty_varargs_pointer (fst caller))) Values RelatedInitial Data Perm Registers)
    as [result [c' [body [code [Model [RelatedBody [Code [Result [Path Frame]]]]]]]]].
  exists result, c', (returned_state caller body), code.
  split; [exact Model|]. split; [apply returned_state_related, RelatedBody|].
  split; [exact Code|]. split; [exact Result|]. split.
  - apply full_call_from_path, Path.
  - split; [apply returned_state_caller|exact Frame].
Qed.
End Call.

Theorem empty_call_refines layout output c caller data perm target used trace :
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists c' final, cells_related layout c' (fst final) /\ array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      [word_value Int.zero; data; perm; target; used; trace; mapped_pointer layout output])
      caller final (inr (word_value Int.zero)) /\
    snd final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Related Capacity.
  pose (initial := call_state caller (word_value Int.zero) data perm target used trace
    (mapped_pointer layout output)).
  assert (RelatedInitial : cells_related layout c (fst initial)) by (apply call_state_related, Related).
  destruct (call_state_bindings caller (word_value Int.zero) data perm target used trace
    (mapped_pointer layout output)) as [N [D [P [T [U [R O]]]]]].
  destruct (@empty_path layout output Int.zero (Some (empty_varargs_pointer (fst caller)))
    c initial ltac:(reflexivity) Capacity RelatedInitial N O)
    as [c' [body [Stores [RelatedBody [Output [Path Frame]]]]]].
  exists c', (returned_state caller body). split; [apply returned_state_related, RelatedBody|].
  split; [exact Output|]. split; [apply full_call_from_path, Path|].
  split; [apply returned_state_caller|exact Frame].
Qed.

Theorem oversized_call_refines layout output n c caller data perm target used trace :
  1024 < Int.unsigned n ->
  cells_related layout c (fst caller) -> (3 <= block_words layout output)%coq_nat ->
  exists c' final, cells_related layout c' (fst final) /\ array_at c' output [0; 0; 0] /\
    runs (denote_function FullCFG.function
      [word_value n; data; perm; target; used; trace; mapped_pointer layout output])
      caller final (inr (word_value (Int.repr 2))) /\
    snd final = snd caller /\
    (forall other xs, other <> output -> array_at c other xs -> array_at c' other xs).
Proof.
  intros Large Related Capacity.
  pose (initial := call_state caller (word_value n) data perm target used trace
    (mapped_pointer layout output)).
  assert (RelatedInitial : cells_related layout c (fst initial)) by (apply call_state_related, Related).
  destruct (call_state_bindings caller (word_value n) data perm target used trace
    (mapped_pointer layout output)) as [N [D [P [T [U [R O]]]]]].
  destruct (@oversized_path layout output n (Some (empty_varargs_pointer (fst caller)))
    c initial Large Capacity RelatedInitial N O)
    as [c' [body [Stores [RelatedBody [Output [Path Frame]]]]]].
  exists c', (returned_state caller body). split; [apply returned_state_related, RelatedBody|].
  split; [exact Output|]. split; [apply full_call_from_path, Path|].
  split; [apply returned_state_caller|exact Frame].
Qed.
