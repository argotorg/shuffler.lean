(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_boot all_fingroup.
From compcert Require Import Integers AST Values Memory Events Ctypes ClightBigstep.
From Legacy Require Import Permute Proofs.
Require Import ClightMemory ClightScalar ModelArrays SolcModel ClightMain.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control FullCFG Entry Index
  MainPrefix MainInvariant Choose Cleanup.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Section Main.
Context (layout : allocation_layout) (d : nat) (bd bp trace output : Values.block).
Hypothesis Size : (S d <= 1024)%coq_nat.
Hypothesis CP : (S d <= block_words layout bp)%coq_nat.

(* Each branch premise is an execution of the actual LLVM blocks. The final
   theorem supplies these premises from the exchange proofs. *)
Hypothesis EqualExchange : forall source (p : 'S_(S d)) depths position c s from varargs,
  (nat_of_ord position < d)%coq_nat ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  choose_binding from s (Some (nat_of_ord position)) ->
  source ord_max = source position ->
  exists c' s', cells_related layout c' (fst s') /\
    @ClightMain.loop_arrays d bd bp trace output c' source
      (Legacy.Permute.exchange p ord_max position) depths /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.end169") (Name "while.cond106") s' /\
    @ClightMain.main_frame bd bp trace output c c'.

Hypothesis SuccessfulExchange : forall source (p : 'S_(S d)) depths position c s from varargs,
  (nat_of_ord position < d)%coq_nat ->
  (forall i, uint (Z.of_nat (source i))) ->
  source ord_max <> source position ->
  (d <= nat_of_ord position + 16)%coq_nat ->
  (List.length depths < 2 * S d)%coq_nat ->
  cells_related layout c (fst s) ->
  @ClightMain.loop_arrays d bd bp trace output c source p depths ->
  main_registers layout d bd bp trace output s ->
  choose_binding from s (Some (nat_of_ord position)) ->
  exists c' s', cells_related layout c' (fst s') /\
    @ClightMain.loop_arrays d bd bp trace output c' (Legacy.Permute.swap_stack source position)
      (Legacy.Permute.exchange p ord_max position) (depths ++ [Legacy.Permute.depth position]) /\
    main_registers layout d bd bp trace output s' /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end133") s
      (Name "if.end169") (Name "while.cond106") s' /\
    @ClightMain.main_frame bd bp trace output c c'.

Hypothesis BlockedExchange : forall source (p : 'S_(S d)) depths position c s from varargs,
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

Theorem main_loop_from_exchanges fuel source (p : 'S_(S d)) depths c s from varargs :
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
  revert source p depths c s from.
  induction fuel as [|fuel IH]; intros source p depths c s from Rank Capacity Values Related Arrays Registers.
  - lia.
  - destruct (@main_choose layout d bd bp trace output source p depths c s from varargs
      Size CP Related Arrays Registers)
      as [previous [s1 [Related1 [Registers1 [Choose Binding]]]]].
    case Choice: (Legacy.Permute.choose p ord_max) => [position|].
    + rewrite Choice /= in Choose Binding.
      destruct (@main_selected_bounds d p position fuel Choice Rank) as [Position NextRank].
      case Equal: (source ord_max == source position).
      * assert (Same : source ord_max = source position) by exact (elimT eqP Equal).
        destruct (EqualExchange source p depths position c s1 previous varargs
          Position Related1 Arrays Registers1 Binding Same)
          as [c1 [s2 [Related2 [Arrays2 [Registers2 [Exchange Frame1]]]]]].
        destruct (IH source (Legacy.Permute.exchange p ord_max position) depths c1 s2
          (Name "if.end169") NextRank ltac:(unfold addn, muln, subn in *; lia)
          Values Related2 Arrays2 Registers2)
          as [c' [s' [code [Related' [Code [Result [Path Frame]]]]]]].
        exists c', s', code. split; [exact Related'|]. split; [exact Code|]. split.
        -- cbn [solc_run]. rewrite Choice Equal. exact Result.
        -- split.
           ++ eapply block_steps_return; [exact Choose|].
              eapply block_steps_return; [exact Exchange|exact Path].
           ++ intros other xs ND NP NT NO A. apply Frame; try assumption.
              apply Frame1; assumption.
      * assert (Different : source ord_max <> source position).
        { intro Same. rewrite Same eqxx in Equal. discriminate. }
        case Near: (Legacy.Permute.depth position <= 16)%N.
        -- assert (NearNat : (d <= nat_of_ord position + 16)%coq_nat).
           { pose proof (elimT leP Near) as H.
             change ((d - nat_of_ord position)%coq_nat <= 16)%coq_nat in H.
             unfold addn, muln, subn in *; lia. }
           destruct (SuccessfulExchange source p depths position c s1 previous varargs
             Position Values Different NearNat ltac:(unfold addn, muln, subn in *; lia)
             Related1 Arrays Registers1 Binding)
             as [c1 [s2 [Related2 [Arrays2 [Registers2 [Exchange Frame1]]]]]].
           assert (Values2 : forall i, uint (Z.of_nat (Legacy.Permute.swap_stack source position i))).
           { intro i. apply Values. }
           destruct (IH (Legacy.Permute.swap_stack source position)
             (Legacy.Permute.exchange p ord_max position) (List.app depths [Legacy.Permute.depth position])
             c1 s2 (Name "if.end169") NextRank
             ltac:(rewrite List.length_app; cbn; unfold addn, muln, subn in *; lia)
             Values2 Related2 Arrays2 Registers2)
             as [c' [s' [code [Related' [Code [Result [Path Frame]]]]]]].
           exists c', s', code. split; [exact Related'|]. split; [exact Code|]. split.
           ++ cbn [solc_run]. rewrite Choice Equal Near. exact Result.
           ++ split.
              ** eapply block_steps_return; [exact Choose|].
                 eapply block_steps_return; [exact Exchange|exact Path].
              ** intros other xs ND NP NT NO A. apply Frame; try assumption.
                 apply Frame1; assumption.
        -- assert (Far : (nat_of_ord position + 16 < d)%coq_nat).
           { assert (H : (16 < Legacy.Permute.depth position)%N) by (rewrite ltnNge Near; reflexivity).
             pose proof (elimT ltP H) as Positive.
             change (16 < (d - nat_of_ord position)%coq_nat)%coq_nat in Positive.
             unfold addn, muln, subn in *; lia. }
           destruct (BlockedExchange source p depths position c s1 previous varargs
             Values Different Far Related1 Arrays Registers1 Binding)
             as [c1 [s2 [Related2 [Result [Exchange Frame]]]]].
           exists c1, (cleanup_state s2 1), 1. split.
           ++ rewrite cleanup_memory. exact Related2.
           ++ split; [right; reflexivity|]. split.
              ** cbn [solc_run]. rewrite Choice Equal Near. exact Result.
              ** split; [|exact Frame]. eapply block_steps_return; [exact Choose|].
                 eapply cleanup_after_steps; [exact Exchange|constructor].
    + rewrite Choice /= in Choose Binding. subst previous.
      exists c, (cleanup_state s1 0), 0. split.
      * rewrite cleanup_memory. exact Related1.
      * split; [left; reflexivity|]. split.
        -- cbn [solc_run]. rewrite Choice. cbn [result_arrays].
           destruct Arrays as [Data Perm Trace Output Writable].
           split; [reflexivity|]. split; [exact Data|].
           split; [exact Perm|]. split; assumption.
        -- split.
           ++ eapply cleanup_after_steps; [exact Choose|constructor].
           ++ intros other xs ND NP NT NO A. exact A.
Qed.
End Main.
