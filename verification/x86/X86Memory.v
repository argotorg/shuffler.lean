(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ITree Require Import ITree.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite
  Interfaces.Memory Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Tiny_x86.
From X86 Require Import X86Layout.
Open Scope Z_scope.

#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params :=
  @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition machine_word (x : Int.int) : bv 32 := Z_to_bv 32 (Int.unsigned x).
Definition machine_address (a : Z) : address := Z_to_bv 64 a.

Definition machine_word_at (machine : memoryMap) (a : Z) (x : Int.int) : Prop :=
  mem_lookup (machine_address a) 4 machine = Some (machine_word x).

(* The same CompCert memory witnesses both relations. Uninitialized scratch
   cells need mapped bytes but no particular initial integer value. *)
Definition machine_cells_related (layout : finite_layout) (c : Mem.mem)
    (machine : memoryMap) : Prop :=
  forall b k, (k < block_words (cell_layout layout) b)%nat ->
    mem_present (machine_address (cell_address (cell_layout layout) b k)) 4
      machine = true /\
    (forall x, Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x) ->
      machine_word_at machine (cell_address (cell_layout layout) b k) x).

Definition llvm_machine_related (layout : finite_layout) (c : Mem.mem)
    (llvm : Impl.State) (machine : memoryMap) : Prop :=
  cells_related (cell_layout layout) c llvm /\
  machine_cells_related layout c machine.

Lemma read_mem_is_lookup size addr state :
  read_mem_seq_state size addr state =
    mem_lookup addr size (archState.memory (sst state)).
Proof. reflexivity. Qed.

Lemma machine_cell_read layout c state b k x :
  machine_cells_related layout c (archState.memory (sst state)) ->
  (k < block_words (cell_layout layout) b)%nat ->
  Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x) ->
  read_mem_seq_state 4
    (machine_address (cell_address (cell_layout layout) b k)) state =
    Some (machine_word x).
Proof.
  intros Related K Load. rewrite read_mem_is_lookup.
  exact (proj2 (Related b k K) x Load).
Qed.

Lemma llvm_machine_cell_read layout c llvm state b k x :
  llvm_machine_related layout c llvm (archState.memory (sst state)) ->
  (k < block_words (cell_layout layout) b)%nat ->
  Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x) ->
  run_memory (Impl.read_dvalue (DTYPE_I 32)
    (cell_address (cell_layout layout) b k,
      block_provenance (cell_layout layout) b)) llvm =
    Ret (llvm, word_value x) /\
  read_mem_seq_state 4
    (machine_address (cell_address (cell_layout layout) b k)) state =
    Some (machine_word x).
Proof.
  intros [LLVM Machine] K Load. split.
  - eapply related_load; eassumption.
  - eapply machine_cell_read; eassumption.
Qed.

Lemma mem_lookup_bytes_frame addr size before after :
  (forall a, List.In a (addr_range addr size) -> before !! a = after !! a) ->
  mem_lookup_bytes addr size before = mem_lookup_bytes addr size after.
Proof.
  intro Frame. unfold mem_lookup_bytes.
  f_equal. apply List.map_ext_in. intros a In. apply Frame. exact In.
Qed.

Lemma mem_lookup_frame addr size before after :
  (forall a, List.In a (addr_range addr size) -> before !! a = after !! a) ->
  mem_lookup addr size before = mem_lookup addr size after.
Proof.
  intro Frame. unfold mem_lookup.
  now rewrite (mem_lookup_bytes_frame addr size before after Frame).
Qed.

Definition stored_byte_state (state : seq_state) (addr : address) (byte : bv 8)
    : seq_state :=
  {| sst := {| archState.memory := mem_insert_byte addr byte
        (archState.memory (sst state));
      archState.address_space := archState.address_space (sst state);
      archState.regs := archState.regs (sst state) |};
    written := written state ∪ {[addr]} |}.

Lemma write_seq_byte addr byte state :
  write_mem_seq_state addr (byte :: nil) state =
    Exec.make ((stored_byte_state state addr byte, tt) :: nil) nil.
Proof. destruct state as [[memory space registers] changed]. reflexivity. Qed.

Lemma stored_byte_here state addr byte :
  read_byte_seq_state (stored_byte_state state addr byte) addr = Some byte.
Proof. apply lookup_insert_eq. Qed.

Lemma stored_byte_elsewhere state addr other byte :
  other <> addr ->
  read_byte_seq_state (stored_byte_state state addr byte) other =
    read_byte_seq_state state other.
Proof. intro Different. apply lookup_insert_ne. congruence. Qed.

Lemma stored_byte_registers state addr byte :
  archState.regs (sst (stored_byte_state state addr byte)) =
    archState.regs (sst state).
Proof. reflexivity. Qed.

Lemma explicit_read_seq size addr state value :
  read_mem_seq_state size addr state = Some value ->
  sequential_model_outcome None
    (MemRead (MemReq.make (Tiny_x86.create_readAccessDescriptor tt)
      addr tt size 0)) state =
    Exec.make ((state, Ok (value, bv_0 0)) :: nil) nil.
Proof.
  destruct state as [[memory [] registers] changed].
  intro Read. cbn [sequential_model_outcome].
  change (is_ifetch (Tiny_x86.create_readAccessDescriptor tt)) with false.
  change (is_ttw (Tiny_x86.create_readAccessDescriptor tt)) with false.
  unfold check_address_space.
  cbv [Effects.mget mbind mret fmap Effects.mcall Exec.mbind_inst Exec.res_mbind_inst
    Exec.merge Exec.mret_inst Exec.res_mret_inst Exec.fmap_inst
    Exec.res_fmap_inst Exec.st_call_MState guard_or].
  cbn in Read |- *.
  case_decide; [|contradiction]. cbn.
  rewrite Read. reflexivity.
Qed.

Lemma fetch_read_seq size addr state value :
  read_mem_seq_state size addr state = Some value ->
  mem_was_written size addr state = false ->
  sequential_model_outcome None
    (MemRead (MemReq.make (Tiny_x86.create_iFetchAccessDescriptor tt)
      addr tt size 0)) state =
    Exec.make ((state, Ok (value, bv_0 0)) :: nil) nil.
Proof.
  destruct state as [[memory [] registers] changed].
  intros Read Clean. cbn [sequential_model_outcome].
  change (is_ifetch (Tiny_x86.create_iFetchAccessDescriptor tt)) with true.
  unfold check_address_space.
  cbv [Effects.mget mbind mret fmap Effects.mcall Exec.mbind_inst Exec.res_mbind_inst
    Exec.merge Exec.mret_inst Exec.res_mret_inst Exec.fmap_inst
    Exec.res_fmap_inst Exec.st_call_MState guard_or].
  cbn. case_decide; [|contradiction]. cbn.
  rewrite Clean. cbn. case_decide; [|contradiction]. cbn.
  rewrite Read. reflexivity.
Qed.

Lemma untouched_fetch size addr state :
  (forall a, List.In a (addr_range addr size) -> a ∉ written state) ->
  mem_was_written size addr state = false.
Proof.
  intro Clean. unfold mem_was_written. apply bool_decide_eq_false_2.
  intros [a [In Written]]. apply (Clean a); [|exact Written].
  apply list_elem_of_In, In.
Qed.

Fixpoint stored_bytes_state (state : seq_state) (addr : address)
    (contents : list (bv 8)) : seq_state :=
  match contents with
  | nil => state
  | byte :: rest => stored_bytes_state (stored_byte_state state addr byte)
      (addr `+Z` 1)%bv rest
  end.

Lemma write_seq_bytes contents addr state :
  write_mem_seq_state addr contents state =
    Exec.make ((stored_bytes_state state addr contents, tt) :: nil) nil.
Proof.
  revert addr state. induction contents as [|byte rest IH]; intros addr state.
  - reflexivity.
  - cbn [write_mem_seq_state stored_bytes_state].
    cbv [Effects.msetv Effects.mset Effects.mSet mbind mret Effects.mcall
      Exec.mbind_inst Exec.res_mbind_inst Exec.merge Exec.mret_inst
      Exec.res_mret_inst Exec.st_call_MState].
    cbn. rewrite IH. reflexivity.
Qed.

Lemma stored_bytes_memory contents addr state :
  archState.memory (sst (stored_bytes_state state addr contents)) =
    mem_insert_bytes addr contents (archState.memory (sst state)).
Proof.
  revert addr state. induction contents as [|byte rest IH]; intros addr state.
  - reflexivity.
  - cbn [stored_bytes_state mem_insert_bytes]. rewrite IH. reflexivity.
Qed.

Lemma stored_bytes_registers contents addr state :
  archState.regs (sst (stored_bytes_state state addr contents)) =
    archState.regs (sst state).
Proof.
  revert addr state. induction contents as [|byte rest IH]; intros addr state.
  - reflexivity.
  - cbn [stored_bytes_state]. rewrite IH. reflexivity.
Qed.

Lemma explicit_write_seq size addr state value :
  mem_present addr size (archState.memory (sst state)) = true ->
  sequential_model_outcome None
    (MemWrite (MemReq.make (Tiny_x86.create_writeAccessDescriptor tt)
      addr tt size 0) value (bv_0 0)) state =
    Exec.make ((stored_bytes_state state addr (bv_to_bytes 8 value), Ok tt) :: nil) nil.
Proof.
  destruct state as [[memory [] registers] changed].
  intro Mapped. cbn in Mapped. cbn [sequential_model_outcome].
  change (is_explicit (Tiny_x86.create_writeAccessDescriptor tt)) with true.
  unfold check_address_space.
  cbv [Effects.mget mbind mret fmap Effects.mcall Exec.mbind_inst Exec.res_mbind_inst
    Exec.merge Exec.mret_inst Exec.res_mret_inst Exec.fmap_inst
    Exec.res_fmap_inst Exec.st_call_MState guard_or].
  cbn. case_decide; [|contradiction]. cbn.
  case_decide; [|contradiction]. cbn.
  rewrite Mapped. cbn. case_decide; [|contradiction]. cbn.
  rewrite write_seq_bytes. reflexivity.
Qed.

Lemma memory_insert_here (machine : memoryMap) addr byte :
  (<[addr := byte]> machine) !! addr = Some byte.
Proof. apply stdpp.fin_maps.lookup_insert_eq. Qed.

Lemma memory_insert_elsewhere (machine : memoryMap) addr other byte :
  addr <> other ->
  (<[addr := byte]> machine) !! other = machine !! other.
Proof. apply stdpp.fin_maps.lookup_insert_ne. Qed.

Lemma read_insert_word machine addr (value : bv 32) :
  mem_lookup addr 4 (mem_insert addr 4 value machine) = Some value.
Proof.
  change (mem_lookup addr 4 (mem_insert_bytes addr (@bv_to_bytes 8 32 value) machine) = Some value).
  remember (bv_to_bytes 8 value) as contents eqn:Contents.
  assert (Length : List.length contents = 4%nat).
  { rewrite Contents, length_bv_to_bytes. reflexivity. }
  destruct contents as [|b0 [|b1 [|b2 [|b3 rest]]]];
    cbn in Length; try discriminate.
  destruct rest; [|discriminate].
  set (after := mem_insert_bytes addr [b0; b1; b2; b3] machine).
  change (option_map (bv_of_bytes 32) (list_of_options
    [after !! addr_addN addr 0; after !! addr_addN addr 1;
     after !! addr_addN addr 2; after !! addr_addN addr 3]) = Some value).
  unfold after. cbn [mem_insert_bytes].
  repeat rewrite addr_addN_assoc.
  repeat rewrite addr_addN_zero.
  cbn [N.add].
  repeat first [rewrite memory_insert_here |
    rewrite memory_insert_elsewhere by
      (unfold addr_addN; intro Equal;
       lazymatch type of Equal with
       | @eq _ (bv_add_Z ?a ?i) ?a =>
           rewrite <- (bv_add_Z_0 a) in Equal at 2
       | _ => idtac
       end;
       apply bv_add_Z_inj_l in Equal;
       [discriminate |
        lazymatch goal with |- 0 <= ?i < _ =>
          change (0 <= i < 18446744073709551616); lia end |
        lazymatch goal with |- 0 <= ?i < _ =>
          change (0 <= i < 18446744073709551616); lia end])].
  change (Some (bv_of_bytes 32 [b0; b1; b2; b3]) = Some value).
  rewrite Contents, bv_of_bytes_bv_to_bytes by discriminate. reflexivity.
Qed.
