(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
From Legacy Require Import Permute Proofs.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix MainInvariant Choose ExchangeBlocked Cleanup MainLoopCore.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Theorem main_blocked_exchange layout d bd bp trace output source (p : 'S_(S d))
    depths position c s from varargs :
  bd <> output -> bp <> output -> trace <> output ->
  (S d <= 1024)%coq_nat -> (S d <= block_words layout bd)%coq_nat ->
  (3 <= block_words layout output)%coq_nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  source ord_max <> source position ->
  (nat_of_ord position + 16 < d)%coq_nat ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  choose_binding from s (Some (nat_of_ord position)) ->
  exists c' s', cells_related layout c' (fst s') /\
    @result_arrays d bd bp trace output
      (SolcBlocked source p depths position (Legacy.Permute.depth position - 16)) c'
      (Out_return (Some (Vint (Int.repr 1), Permute.u32))) /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.then142") (Name "cleanup") s' /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  intros DO PO TO Size CD CO Values Different Far Related Arrays Registers Binding.
  destruct Arrays as [Data Perm Trace Output Writable].
  assert (Unequal : Z.of_nat (source position) <> Z.of_nat (source ord_max)).
  { intro Same. apply Nat2Z.inj in Same. apply Different. symmetry; exact Same. }
  destruct (@exchange_blocked_choice layout bd output (words source) (nat_of_ord position) d
    (Z.of_nat (List.length depths)) 0 0 (Z.of_nat (source position)) (Z.of_nat (source ord_max))
    from varargs c s ltac:(rewrite words_length; exact Size)
    ltac:(rewrite words_length; exact CD) CO
    (words_nth_error source position) (words_nth_error source ord_max)
    (Values position) (Values ord_max) Unequal Far Related Data Output Binding
    (main_data _ _ _ _ _ _ _ Registers) (main_data_top _ _ _ _ _ _ _ Registers)
    (main_top _ _ _ _ _ _ _ Registers) (main_output_fields _ _ _ _ _ _ _ Registers))
    as [c' [s' [Related' [Output' [Steps [Frame Locals]]]]]].
  exists c', s'. split; [exact Related'|]. split.
  - cbn [result_arrays]. split; [reflexivity|]. split; [apply Frame; assumption|].
    split; [apply Frame; assumption|]. split; [apply Frame; assumption|].
    assert (Excess : Z.of_nat (Legacy.Permute.depth position - 16) =
        Z.of_nat d - Z.of_nat (nat_of_ord position) - 16).
    { change (Z.of_nat ((d - nat_of_ord position) - 16)%coq_nat =
        Z.of_nat d - Z.of_nat (nat_of_ord position) - 16).
      rewrite !Nat2Z.inj_sub; unfold addn, muln, subn in *; lia. }
    rewrite Excess. exact Output'.
  - split; [exact Steps|]. intros other xs ND NP NT NO A. apply Frame; assumption.
Qed.

Require Import ModelProofs ExchangePermutation ExchangeSuccess.

Section Main.
Context (layout : allocation_layout) (d : nat) (bd bp trace output : Values.block).
Hypotheses (DP : bd <> bp) (DT : bd <> trace) (DO : bd <> output)
    (PT : bp <> trace) (PO : bp <> output) (TO : trace <> output).
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypotheses (CD : (S d <= block_words layout bd)%coq_nat)
    (CP : (S d <= block_words layout bp)%coq_nat)
    (CT : (2 * S d <= block_words layout trace)%coq_nat)
    (CO : (3 <= block_words layout output)%coq_nat).

Theorem main_loop_refines fuel source (p : 'S_(S d)) depths c s from varargs :
  (Legacy.Permute.rank p ord_max < fuel)%coq_nat ->
  (List.length depths + fuel <= 2 * S d)%coq_nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  exists c' s' code, cells_related layout c' (fst s') /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output (solc_run fuel source p depths) c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs from (Name "while.cond106") s s'
      (word_value (Int.repr code)) /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  eapply (@main_loop_from_exchanges layout d bd bp trace output Size CP).
  - intros source0 p0 depths0 position0 c0 s0 from0 varargs0 Position Related Arrays Registers Binding Equal.
    destruct (@exchange_equal_choice layout d bd bp trace output source0 p0 depths0 position0 c0 s0 from0 varargs0
      Size CD CP DP ltac:(congruence) ltac:(congruence) Related Arrays Registers Binding Equal)
      as [c' [s' [Related' [Arrays' [Registers' [Steps Frame]]]]]].
    exists c', s'. split; [exact Related'|]. split; [exact Arrays'|].
    split; [exact Registers'|]. split; [exact Steps|].
    intros other xs ND NP NT NO A. apply Frame; assumption.
  - intros source0 p0 depths0 position0 c0 s0 from0 varargs0
      Position Values Different Near Capacity Related Arrays Registers Binding.
    destruct (@ExchangeSuccess.successful_exchange layout d bd bp trace output DP DT DO PT PO TO
      Size CD CP CT CO source0 p0 position0 depths0 c0 s0 from0 varargs0
      Values Position ltac:(congruence) Near Capacity Related Arrays Registers Binding)
      as [c' [s' [Related' [Arrays' [Registers' [Steps [Locals Frame]]]]]]].
    exists c', s'. split; [exact Related'|]. split; [exact Arrays'|].
    split; [exact Registers'|]. split; assumption.
  - intros source0 p0 depths0 position0 c0 s0 from0 varargs0
      Values Different Far Related Arrays Registers Binding.
    exact (@main_blocked_exchange layout d bd bp trace output source0 p0 depths0 position0 c0 s0 from0 varargs0
      DO PO TO Size CD CO Values Different Far Related Arrays Registers Binding).
Qed.

Corollary main_loop_nonempty source (p : 'S_(S d)) c s from varargs :
  (forall i, uint (Z.of_nat (source i))) ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p [] ->
  main_registers layout d bd bp trace output s ->
  exists c' s' code, cells_related layout c' (fst s') /\
    (code = 0 \/ code = 1) /\
    @result_arrays d bd bp trace output (solc_nonempty source p) c'
      (Out_return (Some (Vint (Int.repr code), Permute.u32))) /\
    block_path (blks FullCFG.body) varargs from (Name "while.cond106") s s'
      (word_value (Int.repr code)) /\
    @ClightMain.main_frame bd bp trace output c c'.
Proof.
  intros Values Related Arrays Registers.
  eapply main_loop_refines; try eassumption.
  - apply Nat.lt_succ_diag_r.
  - exact (elimT leP (rank_bound p)).
Qed.
End Main.
