(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From ITree Require Import ITree.
From Vellvm Require Import Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents Denotation InterpretationStack Implementations.Memory.
Require Import MemoryRelation WordMemory CellRelation Control Instructions FullCFG Entry Index FixedBlocks.
From ASCommon Require Import Common Exec.
From ArchSemX86 Require Import X86Inst.
From SailStdpp Require Import Operators_mwords.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Layout X86Memory X86ABI X86Instructions X86Control
  X86Program X86Entry X86Execution X86Decode X86DecodeReplay X86ArrayDecode X86CellAddress
  X86Address X86Compare X86Alu X86Flags X86Data X86StackMemory X86MemoryStore
  X86MemoryFrame X86Prologue X86StackFrame X86Call X86CallFrame X86Arguments
  X86UsedZero X86ValidationSteps.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
#[local] Instance parameters : Vellvm.Semantics.Interfaces.Params.Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

From X86 Require Export X86NormalizeStores.

Lemma normalize_llvm_branch layout bd bt bp index from varargs c middle s x y :
  (index <= 1024)%nat ->
  (index < block_words layout bd)%nat -> (index < block_words layout bt)%nat ->
  (index < block_words layout bp)%nat ->
  cells_related layout c (fst s) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  fixed_input from s (Z.of_nat index) ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  (if word_equal x y then
     Mem.store Mint32 c bp (4 * Z.of_nat index) (Vint (Int.repr (Z.of_nat index))) = Some middle
   else middle = c) ->
  exists final,
    cells_related layout middle (fst final) /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43") s
      (fixed_from (word_equal x y)) (Name "if.end57") final /\
    Maps.lookup (Name "indvars.iv301") (locals final) = Some (index_value (Z.of_nat index)) /\
    (forall id, ~ In id fixed_modified -> Maps.lookup id (locals final) = Maps.lookup id (locals s)).
Proof.
  intros Bound DataCapacity TargetCapacity PermCapacity Related LoadData LoadTarget Input Data Target Perm Store.
  pose (compared := fixed_compare_state s (Z.of_nat index)
    (block_address layout bd) (block_provenance layout bd)
    (block_address layout bt) (block_provenance layout bt) x y).
  assert (Compare : runs (denote_block (proj1_sig FullCFG.fixed_compare) from varargs) s compared
    (inl (if word_equal x y then Name "if.then49" else Name "if.end57"))).
  { apply fixed_compare_runs; try assumption; try lia;
      eapply related_load; eassumption. }
  assert (Other : forall id, ~ In id fixed_modified ->
    Maps.lookup id (locals compared) = Maps.lookup id (locals s)).
  { intros id Outside. apply fixed_compare_other, Outside. }
  assert (Index : Maps.lookup (Name "indvars.iv301") (locals compared) =
    Some (index_value (Z.of_nat index))).
  { unfold compared, fixed_compare_state.
    rewrite !lookup_local_other by discriminate. apply lookup_local_same. }
  destruct (word_equal x y) eqn:Choice.
  - destruct (@related_store layout c (fst s) bp index (Int.repr (Z.of_nat index))
      Related PermCapacity) as [actual [memory [Actual [Write [RelatedNext Rest]]]]].
    rewrite Store in Actual. inversion Actual; subst actual.
    pose (assigned := fixed_assign_state compared (Z.of_nat index)
      (block_address layout bp) (block_provenance layout bp) memory).
    assert (Assign : runs (denote_block (proj1_sig FullCFG.fixed_assign)
      (Name "if.end43") varargs) compared assigned (inl (Name "if.end57"))).
    { apply fixed_assign_runs; [lia|exact Index| |].
      - rewrite Other by (unfold fixed_modified; simpl; intuition discriminate). exact Perm.
      - unfold compared. rewrite fixed_compare_memory. exact Write. }
    exists assigned. split; [unfold assigned; rewrite fixed_assign_memory; exact RelatedNext|].
    split.
    + eapply steps_next; [exact (proj2_sig FullCFG.fixed_compare)|exact Compare|].
      eapply steps_next; [exact (proj2_sig FullCFG.fixed_assign)|exact Assign|constructor].
    + split.
      * unfold assigned, fixed_assign_state. rewrite locals_with_memory.
        rewrite !lookup_local_other by discriminate. exact Index.
      * intros id Outside. unfold assigned. rewrite fixed_assign_other by exact Outside.
        apply Other, Outside.
  - subst middle. exists compared. split.
    + unfold compared. rewrite fixed_compare_memory. exact Related.
    + split.
      * eapply steps_next; [exact (proj2_sig FullCFG.fixed_compare)|exact Compare|constructor].
      * split; assumption.
Qed.

Theorem normalize_llvm_iteration layout bd bt bp bu size index from varargs c c' s x y :
  (index < size <= 1024)%nat ->
  (index < block_words layout bd)%nat -> (index < block_words layout bt)%nat ->
  (index < block_words layout bp)%nat -> (index < block_words layout bu)%nat ->
  cells_related layout c (fst s) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  fixed_input from s (Z.of_nat index) ->
  Maps.lookup (Name "v2") (locals s) = Some (pointer_value (block_address layout bd) (block_provenance layout bd)) ->
  Maps.lookup (Name "v4") (locals s) = Some (pointer_value (block_address layout bt) (block_provenance layout bt)) ->
  Maps.lookup (Name "v3") (locals s) = Some (pointer_value (block_address layout bp) (block_provenance layout bp)) ->
  Maps.lookup (Name "v5") (locals s) = Some (pointer_value (block_address layout bu) (block_provenance layout bu)) ->
  Maps.lookup (Name "wide.trip.count304") (locals s) = Some (index_value (Z.of_nat size)) ->
  normalize_stores bp bu index (word_equal x y) c c' ->
  exists final,
    cells_related layout c' (fst final) /\
    block_steps (blks FullCFG.body) varargs from (Name "if.end43") s
      (Name "if.end57")
      (if Z.of_nat (S index) =? Z.of_nat size then Name "if.end65.preheader" else Name "if.end43") final /\
    fixed_input (Name "if.end57") final (Z.of_nat (S index)) /\
    (forall id, ~ In id fixed_modified -> Maps.lookup id (locals final) = Maps.lookup id (locals s)).
Proof.
  intros Range DataCapacity TargetCapacity PermCapacity UsedCapacity Related LoadData LoadTarget
    Input Data Target Perm Used Size [middle [AssignStore UsedStore]].
  destruct (normalize_llvm_branch layout bd bt bp index from varargs c middle s x y
    ltac:(lia) DataCapacity TargetCapacity PermCapacity Related LoadData LoadTarget Input
    Data Target Perm AssignStore)
    as [branch [RelatedBranch [Branch [Index Other]]]].
  destruct (@related_store layout middle (fst branch) bu index (flag_word (word_equal x y))
    RelatedBranch UsedCapacity) as [actual [memory [Actual [Write [RelatedFinal Rest]]]]].
  rewrite UsedStore in Actual. inversion Actual; subst actual.
  pose (final := fixed_merge_state branch (Z.of_nat index) (Z.of_nat size)
    (block_address layout bu) (block_provenance layout bu) (word_equal x y) memory).
  assert (Merge : runs (denote_block (proj1_sig FullCFG.fixed_merge)
      (fixed_from (word_equal x y)) varargs) branch final
    (inl (if Z.of_nat index + 1 =? Z.of_nat size then Name "if.end65.preheader" else Name "if.end43"))).
  { apply fixed_merge_runs; [lia|lia|exact Index| | |exact Write].
    - rewrite Other by (unfold fixed_modified; simpl; intuition discriminate). exact Size.
    - rewrite Other by (unfold fixed_modified; simpl; intuition discriminate). exact Used. }
  replace (Z.of_nat index + 1) with (Z.of_nat (S index)) in Merge by lia.
  exists final. split; [unfold final; rewrite fixed_merge_memory; exact RelatedFinal|]. split.
  - eapply block_steps_append; [exact Branch|].
    eapply steps_next; [exact (proj2_sig FullCFG.fixed_merge)|exact Merge|constructor].
  - split.
    + replace (Z.of_nat (S index)) with (Z.of_nat index + 1) by lia.
      apply fixed_merge_next.
    + intros id Outside. unfold final. rewrite fixed_merge_other by exact Outside.
      apply Other, Outside.
Qed.

Print Assumptions normalize_llvm_iteration.

Lemma normalize_low_gpr index value :
  low_register32 index (Values.from_ty (gpr_reference index) (@zero_extend 32 value 64)) = value.
Proof. unfold low_register32. rewrite gpr_reference_inverse. apply low32_zero_extend. Qed.

Lemma normalize_array_address layout state base index block position :
  read_reg_seq_state (Values.reg (gpr_reference base)) state =
    Some (Values.from_ty (gpr_reference base) (pointer_to_block layout block)) ->
  read_reg_seq_state (Values.reg (gpr_reference index)) state =
    Some (Values.from_ty (gpr_reference index) (machine_address (Z.of_nat position))) ->
  scaled_address (register_values_of state) base index =
    machine_address (cell_address (cell_layout layout) block position).
Proof.
  intros Base Index. unfold scaled_address, scaled_gprs, gpr64.
  rewrite (register_value_known state _ _ Base), (register_value_known state _ _ Index),
    !gpr_reference_inverse. apply scaled_cell_address.
Qed.

Lemma normalize_compare_step nondet layout (frame : call_frame layout program_bytes)
    state offset bytes first second first_old second_old first_number second_number :
  In (offset, bytes, first, second) [(156, 3, 11, 3); (181, 2, 0, 7)] ->
  0 <= first_number < 4294967296 -> 0 <= second_number < 4294967296 ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state (Values.reg (gpr_reference first)) state = Some first_old ->
  low_register32 first first_old = Z_to_bv 32 first_number ->
  read_reg_seq_state (Values.reg (gpr_reference second)) state = Some second_old ->
  low_register32 second second_old = Z_to_bv 32 second_number ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags (validation_pc state (entry_pc frame) (offset + bytes))) /\
    @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = negb (first_number =? second_number).
Proof.
  intros Site FirstRange SecondRange Code Present PC First FirstLow Second SecondLow.
  assert (FirstNotPC : Values.reg (gpr_reference first) <> rip).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction]; subst; discriminate. }
  assert (SecondNotPC : Values.reg (gpr_reference second) <> rip).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction]; subst; discriminate. }
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) (offset + bytes)).
  assert (FirstNext : read_reg_seq_state (Values.reg (gpr_reference first)) next = Some first_old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact First. }
  assert (SecondNext : read_reg_seq_state (Values.reg (gpr_reference second)) next = Some second_old).
  { unfold next, validation_pc. rewrite register_read_frame by congruence. exact Second. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_cmp32_registers nondet first second next first_old second_old flags
    FirstNext SecondNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite FirstLow, SecondLow in Execute.
  pose (result := @sub_vec 32 (Z_to_bv 32 first_number) (Z_to_bv 32 second_number)).
  exists (result_flags flags (sign_flag32 result) overflow carry
    (zero_flag32 result) auxiliary parity). split.
  - eapply framed_instruction with (offset := offset) (size := bytes)
      (instruction := CMP (32, rm_REG (REG_NORMAL first), rmi_REG (REG_NORMAL second)));
      [exact Code|exact Present|exact PC| | |].
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; vm_compute; tauto.
    + destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
        subst; destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + offset + bytes) with (entry_pc frame + (offset + bytes)) by lia.
      exact Execute.
  - unfold result. apply comparison_jne; assumption.
Qed.

Lemma normalize_flag_step nondet layout (frame : call_frame layout program_bytes)
    state offset value :
  In (offset, value) [(159, 0); (169, 1)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (write_reg_seq_state rbx (machine_address value)
      (validation_pc state (entry_pc frame) (offset + 5))).
Proof.
  intros Site Code Present PC.
  assert (Range : 0 <= value < Int.modulus).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; change Int.modulus with 4294967296; lia. }
  destruct (Present rbx) as [old Old].
  eapply framed_instruction with (offset := offset) (size := 5)
    (instruction := MOV (32, rm_REG (REG_NORMAL 3), rmi_IMM (IMM32 (Z_to_bv 32 value))));
    [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + offset + 5) with (entry_pc frame + (offset + 5)) by lia.
    rewrite <- (zero_extend32_word value Range).
    apply (execute_mov32_immediate nondet 3 _ old (Z_to_bv 32 value)).
    change (read_reg_seq_state rbx
      (write_reg_seq_state rip (machine_address (entry_pc frame + (offset + 5))) state) = Some old).
    rewrite register_read_frame by discriminate. exact Old.
Qed.

Lemma normalize_jne_step nondet layout (frame : call_frame layout program_bytes)
    state offset byte displacement flags taken :
  In (offset, byte, displacement) [(164, 8, 8); (183, 220, -36)] ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + offset)) ->
  read_reg_seq_state rflags state = Some flags ->
  @eq_vec 1 (_get_rflags_type_ZF flags) (Z_to_bv 1 0) = taken ->
  instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state
    (validation_pc state (entry_pc frame)
      (if taken then offset + 2 + displacement else offset + 2)).
Proof.
  intros Site Code Present PC Flags Taken.
  assert (Extend : @sign_extend 8 (Z_to_bv 8 byte) 64 = Z_to_bv 64 displacement).
  { destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; apply bv_eq; reflexivity. }
  eapply framed_instruction with (offset := offset) (size := 2)
    (instruction := JNE (Z_to_bv 8 byte)); [exact Code|exact Present|exact PC| | |].
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; vm_compute; tauto.
  - destruct Site as [Here|[Here|No]]; [inversion Here|inversion Here|contradiction];
      subst; destruct nondet; reflexivity.
  - rewrite machine_address_next.
    erewrite execute_jne with (pc := machine_address (entry_pc frame + offset + 2)) (flags := flags).
    + rewrite Taken. destruct taken.
      * rewrite Extend.
        change (@add_vec 64 (machine_address (entry_pc frame + offset + 2)) (Z_to_bv 64 displacement))
          with (@add_vec_int 64 (machine_address (entry_pc frame + offset + 2)) displacement).
        rewrite machine_address_next, register_write_overwrite.
        replace (entry_pc frame + offset + 2 + displacement) with
          (entry_pc frame + (offset + 2 + displacement)) by lia. reflexivity.
      * replace (entry_pc frame + offset + 2) with (entry_pc frame + (offset + 2)) by lia.
        reflexivity.
    + apply register_read_written.
    + rewrite register_read_frame by discriminate. exact Flags.
Qed.

Lemma normalize_increment nondet layout (frame : call_frame layout program_bytes) state index :
  (index < 1024)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 178)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  exists flags,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state
      (write_reg_seq_state rflags flags
        (write_reg_seq_state rax (machine_address (Z.of_nat (S index)))
          (validation_pc state (entry_pc frame) 181))).
Proof.
  intros Range Code Present PC Counter.
  destruct (Present rflags) as [flags Flags].
  pose (next := validation_pc state (entry_pc frame) 181).
  assert (CounterNext : read_reg_seq_state rax next = Some (machine_address (Z.of_nat index))).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Counter. }
  assert (FlagsNext : read_reg_seq_state rflags next = Some flags).
  { unfold next, validation_pc. rewrite register_read_frame by discriminate. exact Flags. }
  destruct (execute_add32_imm8 nondet 0 next (machine_address (Z.of_nat index)) flags
    (Z_to_bv 8 1) ltac:(discriminate) CounterNext FlagsNext)
    as [overflow [carry [auxiliary [parity Execute]]]].
  cbn beta zeta in Execute. rewrite machine_low32 in Execute by (change Int.modulus with 4294967296; lia).
  change (@sign_extend 8 (Z_to_bv 8 1) 32) with (Z_to_bv 32 1) in Execute.
  rewrite add32_words in Execute.
  replace (Z.of_nat index + 1) with (Z.of_nat (S index)) in Execute by lia.
  exists (result_flags flags (sign_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) overflow carry
    (zero_flag32 (Z_to_bv 32 (Z.of_nat (S index)))) auxiliary parity).
  eapply framed_instruction with (offset := 178) (size := 3)
    (instruction := ADD (false, 32, rm_REG (REG_NORMAL 0), rmi_IMM (IMM8 (Z_to_bv 8 1))));
    [exact Code|exact Present|exact PC| | |].
  - vm_compute; tauto.
  - destruct nondet; reflexivity.
  - rewrite machine_address_next.
    replace (entry_pc frame + 178 + 3) with (entry_pc frame + 181) by lia.
    unfold gpr32_written in Execute.
    change (Values.from_ty (gpr_reference 0)
      (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (S index))) 64))
      with (@zero_extend 32 (Z_to_bv 32 (Z.of_nat (S index))) 64) in Execute.
    rewrite zero_extend32_word in Execute by (change Int.modulus with 4294967296; lia).
    exact Execute.
Qed.

Ltac normalize_unfold :=
  repeat multimatch goal with
  | local := _ : seq_state |- _ =>
    match goal with |- context [local] => unfold local end
  end;
  unfold validation_pc.

Ltac normalize_reads :=
  normalize_unfold;
  repeat first [rewrite stored_register_read | rewrite register_read_written |
    rewrite register_read_frame by discriminate].

Ltac normalize_code :=
  normalize_unfold;
  repeat first [apply code_at_register_write | apply code_preserved_cell_store; [|lia]]; assumption.

Ltac normalize_present :=
  normalize_unfold;
  repeat first [apply registers_present_write | apply registers_present_store]; assumption.

Ltac normalize_arguments :=
  normalize_unfold;
  repeat first [apply core_arguments_write;
    [unfold argument_registers; simpl; intuition discriminate|] | apply core_arguments_store]; assumption.

Ltac normalize_stack :=
  normalize_unfold;
  repeat first [apply call_stack_register_write; [|discriminate|discriminate] |
    apply call_stack_cell_store; [|lia]]; assumption.

Print Assumptions normalize_compare_step.
Print Assumptions normalize_flag_step.
Print Assumptions normalize_jne_step.
Print Assumptions normalize_increment.

Lemma normalize_machine_branch nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output x y c middle :
  (index < size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bd)%nat ->
  (size <= block_words (cell_layout layout) bp)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 149)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  (if word_equal x y then
    Mem.store Mint32 c bp (4 * Z.of_nat index) (Vint (Int.repr (Z.of_nat index))) = Some middle
   else middle = c) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if word_equal x y then 7%nat else 5%nat) state final /\
    machine_cells_related layout middle (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 174)) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat index)) /\
    read_reg_seq_state rbx final = Some (machine_address (if word_equal x y then 1 else 0)).
Proof.
  intros Range DataCapacity PermCapacity TargetCapacity Code Present Arguments Stack PC Counter
    Related DataLoad TargetLoad Store.
  pose proof (core_data _ _ _ _ _ _ _ _ _ Arguments) as Data.
  pose proof (core_target _ _ _ _ _ _ _ _ _ Arguments) as Target.
  pose proof (core_permutation _ _ _ _ _ _ _ _ _ Arguments) as Perm.
  pose (s1 := write_reg_seq_state r11 (@zero_extend 32 (machine_word x) 64)
    (validation_pc state (entry_pc frame) 153)).
  assert (Step1 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 state s1).
  { exact (validation_array_load nondet layout frame state 149 4 11 6 0 bd index x c
      ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia) Code Present PC
      ltac:(apply normalize_array_address; [exact Data|exact Counter]) Related DataLoad). }
  pose (s2 := write_reg_seq_state rbx (@zero_extend 32 (machine_word y) 64)
    (validation_pc s1 (entry_pc frame) 156)).
  assert (Related1 : machine_cells_related layout c (archState.memory (sst s1))).
  { unfold s1, validation_pc. rewrite !register_write_memory. exact Related. }
  assert (Step2 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s1 s2).
  { exact (validation_array_load nondet layout frame s1 153 3 3 1 0 bt index y c
      ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia)
      ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
      ltac:(apply normalize_array_address; [normalize_reads; exact Target|normalize_reads; exact Counter])
      Related1 TargetLoad). }
  destruct (normalize_compare_step nondet layout frame s2 156 3 11 3
    (@zero_extend 32 (machine_word x) 64) (@zero_extend 32 (machine_word y) 64)
    (Int.unsigned x) (Int.unsigned y) ltac:(left; reflexivity)
    (Int.unsigned_range x) (Int.unsigned_range y)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(normalize_reads; reflexivity) ltac:(apply low32_zero_extend)
    ltac:(normalize_reads; reflexivity) ltac:(apply low32_zero_extend))
    as [f3 [Step3 Zero3]].
  change (@eq_vec 1 (_get_rflags_type_ZF f3) (Z_to_bv 1 0) = negb (word_equal x y)) in Zero3.
  pose (s3 := write_reg_seq_state rflags f3 (validation_pc s2 (entry_pc frame) 159)).
  pose (s4 := write_reg_seq_state rbx (machine_address 0) (validation_pc s3 (entry_pc frame) 164)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { exact (normalize_flag_step nondet layout frame s3 159 0 ltac:(left; reflexivity)
      ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)). }
  pose (s5 := validation_pc s4 (entry_pc frame) (if word_equal x y then 166 else 174)).
  assert (Step5 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s4 s5).
  { pose proof (normalize_jne_step nondet layout frame s4 164 8 8 f3 (negb (word_equal x y))
      ltac:(left; reflexivity) ltac:(normalize_code) ltac:(normalize_present)
      ltac:(normalize_reads; reflexivity) ltac:(normalize_reads; reflexivity) Zero3) as Jump.
    destruct (word_equal x y); exact Jump. }
  assert (Steps5 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 5 state s5).
  { eapply instruction_steps_append with (count := 1%nat) (rest := 4%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step3|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step4|exact Step5]. }
  assert (Related5 : machine_cells_related layout c (archState.memory (sst s5))).
  { unfold s5, s4, s3, s2, s1, validation_pc. rewrite !register_write_memory. exact Related. }
  destruct (word_equal x y) eqn:Choice.
  - pose (s6 := stored_bytes_state (validation_pc s5 (entry_pc frame) 169)
      (machine_address (cell_address (cell_layout layout) bp index))
      (bv_to_bytes 8 (machine_word (Int.repr (Z.of_nat index))))).
    destruct (validation_array_store nondet layout frame s5 166 3 0 2 0 bp index
      (Int.repr (Z.of_nat index)) (machine_address (Z.of_nat index)) c middle
      ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia)
      ltac:(normalize_code) ltac:(normalize_present)
      ltac:(normalize_reads; rewrite ?Choice; reflexivity)
      ltac:(apply normalize_array_address; [normalize_reads; exact Perm|normalize_reads; exact Counter])
      ltac:(normalize_reads; exact Counter)
      ltac:(unfold machine_word; rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia);
        apply machine_low32; change Int.modulus with 4294967296; lia)
      Related5 Store) as [Step6 Related6].
    pose (s7 := write_reg_seq_state rbx (machine_address 1) (validation_pc s6 (entry_pc frame) 174)).
    assert (Step7 : instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 s6 s7).
    { exact (normalize_flag_step nondet layout frame s6 169 1 ltac:(right; left; reflexivity)
        ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)). }
    exists s7. split.
    + eapply instruction_steps_append with (count := 5%nat) (rest := 2%nat); [exact Steps5|].
      eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); eassumption.
    + split.
      { unfold s7, validation_pc. rewrite !register_write_memory. exact Related6. }
      split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
      split; [normalize_stack|]. split; [normalize_reads; reflexivity|].
      split; normalize_reads; [exact Counter|reflexivity].
  - subst middle. exists s5. split; [exact Steps5|]. split; [exact Related5|].
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; [normalize_reads; rewrite ?Choice; reflexivity|].
    split; normalize_reads; [exact Counter|reflexivity].
Qed.

Lemma normalize_machine_merge nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output (choice : bool) c c' :
  (index < size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 174)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  read_reg_seq_state rbx state = Some (machine_address (if choice then 1 else 0)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.store Mint32 c bu (4 * Z.of_nat index) (Vint (flag_word choice)) = Some c' ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 4 state final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 185 else 149))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range UsedCapacity Code Present Arguments Stack PC Counter Flag Related Store.
  pose proof (core_used _ _ _ _ _ _ _ _ _ Arguments) as Used.
  destruct (core_size _ _ _ _ _ _ _ _ _ Arguments) as [size_old [SizeRead SizeLow]].
  assert (SizeLow32 : low_register32 7 size_old = Z_to_bv 32 (Z.of_nat size)).
  { change (bv_extract 0 32 size_old = Z_to_bv 32 (Z.of_nat size)).
    rewrite SizeLow. unfold machine_word. rewrite Int.unsigned_repr; [reflexivity|].
    change Int.max_unsigned with 4294967295. lia. }
  pose (s1 := stored_bytes_state (validation_pc state (entry_pc frame) 178)
    (machine_address (cell_address (cell_layout layout) bu index))
    (bv_to_bytes 8 (machine_word (flag_word choice)))).
  destruct (validation_array_store nondet layout frame state 174 4 3 8 0 bu index
    (flag_word choice) (machine_address (if choice then 1 else 0)) c c'
    ltac:(cbn; tauto) ltac:(discriminate) ltac:(lia) Code Present PC
    ltac:(apply normalize_array_address; [exact Used|exact Counter]) Flag
    ltac:(destruct choice; reflexivity) Related Store) as [Step1 Related1].
  destruct (normalize_increment nondet layout frame s1 index ltac:(lia)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(normalize_reads; exact Counter)) as [f2 Step2].
  pose (s2 := write_reg_seq_state rflags f2
    (write_reg_seq_state rax (machine_address (Z.of_nat (S index)))
      (validation_pc s1 (entry_pc frame) 181))).
  destruct (normalize_compare_step nondet layout frame s2 181 2 0 7
    (machine_address (Z.of_nat (S index))) size_old (Z.of_nat (S index)) (Z.of_nat size)
    ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
    ltac:(normalize_reads; reflexivity)
    ltac:(apply machine_low32; change Int.modulus with 4294967296; lia)
    ltac:(normalize_reads; exact SizeRead) SizeLow32) as [f3 [Step3 Zero3]].
  pose (s3 := write_reg_seq_state rflags f3 (validation_pc s2 (entry_pc frame) 183)).
  pose (s4 := validation_pc s3 (entry_pc frame)
    (if Z.of_nat (S index) =? Z.of_nat size then 185 else 149)).
  assert (Step4 : instruction_steps (sail_tiny_x86_sem nondet)
    (return_condition (machine_address (return_pc frame))) 1 s3 s4).
  { pose proof (normalize_jne_step nondet layout frame s3 183 220 (-36) f3
      (negb (Z.of_nat (S index) =? Z.of_nat size)) ltac:(right; left; reflexivity)
      ltac:(normalize_code) ltac:(normalize_present) ltac:(normalize_reads; reflexivity)
      ltac:(normalize_reads; reflexivity) Zero3) as Jump.
    destruct (Z.of_nat (S index) =? Z.of_nat size); exact Jump. }
  exists s4. split.
  - eapply instruction_steps_append with (count := 1%nat) (rest := 3%nat); [exact Step1|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 2%nat); [exact Step2|].
    eapply instruction_steps_append with (count := 1%nat) (rest := 1%nat); [exact Step3|exact Step4].
  - split.
    { unfold s4, s3, s2, validation_pc. rewrite !register_write_memory. exact Related1. }
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; normalize_reads; reflexivity.
Qed.

Theorem normalize_machine_iteration nondet layout (frame : call_frame layout program_bytes)
    initial state size index bd bp bt bu trace output x y c c' :
  (index < size <= 1024)%nat ->
  (size <= block_words (cell_layout layout) bd)%nat ->
  (size <= block_words (cell_layout layout) bp)%nat ->
  (size <= block_words (cell_layout layout) bt)%nat ->
  (size <= block_words (cell_layout layout) bu)%nat ->
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 149)) ->
  read_reg_seq_state rax state = Some (machine_address (Z.of_nat index)) ->
  machine_cells_related layout c (archState.memory (sst state)) ->
  Mem.load Mint32 c bd (4 * Z.of_nat index) = Some (Vint x) ->
  Mem.load Mint32 c bt (4 * Z.of_nat index) = Some (Vint y) ->
  normalize_stores bp bu index (word_equal x y) c c' ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame)))
      (if word_equal x y then 11%nat else 9%nat) state final /\
    machine_cells_related layout c' (archState.memory (sst final)) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address
      (entry_pc frame + (if Z.of_nat (S index) =? Z.of_nat size then 185 else 149))) /\
    read_reg_seq_state rax final = Some (machine_address (Z.of_nat (S index))).
Proof.
  intros Range DataCapacity PermCapacity TargetCapacity UsedCapacity Code Present Arguments Stack
    PC Counter Related DataLoad TargetLoad [middle [AssignStore UsedStore]].
  destruct (normalize_machine_branch nondet layout frame initial state size index bd bp bt bu trace output
    x y c middle Range DataCapacity PermCapacity TargetCapacity Code Present Arguments Stack PC Counter
    Related DataLoad TargetLoad AssignStore)
    as [branch [Branch [RelatedBranch [CodeBranch [PresentBranch [ArgumentsBranch
      [StackBranch [PCBranch [CounterBranch FlagBranch]]]]]]]]].
  destruct (normalize_machine_merge nondet layout frame initial branch size index bd bp bt bu trace output
    (word_equal x y) middle c' Range UsedCapacity CodeBranch PresentBranch ArgumentsBranch StackBranch
    PCBranch CounterBranch FlagBranch RelatedBranch UsedStore)
    as [final [Merge Result]].
  exists final. split; [|exact Result].
  replace (if word_equal x y then 11%nat else 9%nat)
    with ((if word_equal x y then 7 else 5) + 4)%nat by (destruct (word_equal x y); reflexivity).
  eapply instruction_steps_append; eassumption.
Qed.

Theorem normalize_preheader nondet layout (frame : call_frame layout program_bytes)
    initial state size bd bp bt bu trace output :
  code_at state (entry_pc frame) program_bytes -> registers_present state ->
  core_arguments layout size bd bp bt bu trace output state ->
  call_stack layout frame initial state ->
  read_reg_seq_state rip state = Some (machine_address (entry_pc frame + 147)) ->
  exists final,
    instruction_steps (sail_tiny_x86_sem nondet)
      (return_condition (machine_address (return_pc frame))) 1 state final /\
    archState.memory (sst final) = archState.memory (sst state) /\
    code_at final (entry_pc frame) program_bytes /\ registers_present final /\
    core_arguments layout size bd bp bt bu trace output final /\
    call_stack layout frame initial final /\
    read_reg_seq_state rip final = Some (machine_address (entry_pc frame + 149)) /\
    read_reg_seq_state rax final = Some (machine_address 0).
Proof.
  intros Code Present Arguments Stack PC.
  destruct (Present rax) as [old_ax OldAX]. destruct (Present rflags) as [flags Flags].
  pose (final := write_reg_seq_state rflags (xor_zero_flags flags)
    (write_reg_seq_state rax (Z_to_bv 64 0) (validation_pc state (entry_pc frame) 149))).
  exists final. split.
  - eapply framed_instruction with (offset := 147) (size := 2)
      (instruction := XOR (false, 32, rm_REG (REG_NORMAL 0), rmi_REG (REG_NORMAL 0)));
      [exact Code|exact Present|exact PC| | |].
    + vm_compute; tauto.
    + destruct nondet; reflexivity.
    + rewrite machine_address_next.
      replace (entry_pc frame + 147 + 2) with (entry_pc frame + 149) by lia.
      apply (execute_xor32_self nondet 0 _ old_ax flags).
      * discriminate.
      * change (read_reg_seq_state rax
          (write_reg_seq_state rip (machine_address (entry_pc frame + 149)) state) = Some old_ax).
        rewrite register_read_frame by discriminate. exact OldAX.
      * rewrite register_read_frame by discriminate. exact Flags.
  - split.
    { unfold final, validation_pc. rewrite !register_write_memory. reflexivity. }
    split; [normalize_code|]. split; [normalize_present|]. split; [normalize_arguments|].
    split; [normalize_stack|]. split; normalize_reads; reflexivity.
Qed.

Print Assumptions normalize_machine_branch.
Print Assumptions normalize_machine_merge.
Print Assumptions normalize_machine_iteration.
Print Assumptions normalize_preheader.
