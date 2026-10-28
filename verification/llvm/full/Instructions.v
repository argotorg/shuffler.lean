(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Utils Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents InterpretationStack Denotation EOU Operations.
Require Import Control.
Import ListNotations.
Import ITreeNotations.
Open Scope itree_scope.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.

Lemma runs_with_call_ret A s (x : A) : runs (withCall (Ret x)) s s x.
Proof.
  eapply runs_eutt; [unfold withCall; rewrite translate_ret; reflexivity|].
  apply runs_ret.
Qed.

Lemma runs_with_call_bind A B (t : MCFGtop A) (k : A -> MCFGtop B)
    s middle final x y :
  runs (withCall t) s middle x -> runs (withCall (k x)) middle final y ->
  runs (withCall (ITree.bind t k)) s final y.
Proof.
  intros First Last. eapply runs_eutt.
  - unfold withCall. rewrite translate_bind. reflexivity.
  - eapply runs_bind; eassumption.
Qed.

Lemma runs_eou A (c : EOU A) s value :
  c = raise_ret value ->
  runs (withCall (EOU_to_itree c)) s s value.
Proof.
  intros ->. change (runs (withCall (Ret value)) s s value).
  eapply runs_eutt.
  - unfold withCall. rewrite translate_ret. reflexivity.
  - apply runs_ret.
Qed.

Lemma runs_expression_local top id s value :
  Maps.lookup id (locals s) = Some value ->
  runs (denote_exp' top (EXP_Ident (ID_Local id))) s s value.
Proof.
  intro Found.
  change (runs (withCall (lread id)) s s value).
  eapply runs_eutt with (u := lread id).
  - unfold withCall, lread.
    rewrite translate_trigger. reflexivity.
  - apply runs_local_read, Found.
Qed.

Lemma runs_expression_integer dt literal s value :
  denote_int_syntax_as_int dt literal = raise_ret value ->
  runs (denote_exp' (Some dt) (EXP_Integer literal)) s s value.
Proof.
  intro Value. unfold denote_exp'. cbn [denote_exp].
  apply runs_eou, Value.
Qed.

Lemma runs_expression_ibinop top op dt a b s va vb value :
  runs (denote_exp' (Some dt) a) s s va ->
  runs (denote_exp' (Some dt) b) s s vb ->
  eval_iop op va vb = raise_ret value ->
  runs (denote_exp' top (OP_IBinop op dt a b)) s s value.
Proof.
  intros A B Value. unfold denote_exp'. cbn [denote_exp].
  eapply runs_with_call_bind; [exact A|].
  eapply runs_with_call_bind; [exact B|].
  apply runs_eou, Value.
Qed.

Lemma runs_expression_icmp top same cmp dt a b s va vb value :
  runs (denote_exp' (Some dt) a) s s va ->
  runs (denote_exp' (Some dt) b) s s vb ->
  eval_icmp same cmp va vb = raise_ret value ->
  runs (denote_exp' top (OP_ICmp same cmp dt a b)) s s value.
Proof.
  intros A B Value. unfold denote_exp'. cbn [denote_exp].
  eapply runs_with_call_bind; [exact A|].
  eapply runs_with_call_bind; [exact B|].
  apply runs_eou, Value.
Qed.

Lemma runs_expression_conversion top cv source target e s v value :
  runs (denote_exp' (Some source) e) s s v ->
  convert_pure cv source v target = raise_ret value ->
  runs (denote_exp' top (OP_Conversion (CONV_Pure cv) source e target)) s s value.
Proof.
  intros Operand Value. unfold denote_exp'. cbn [denote_exp].
  eapply runs_with_call_bind; [exact Operand|].
  cbn [convert]. apply runs_eou, Value.
Qed.

Lemma runs_expression_gep top element pointer_type pointer index_type index
    s p i value :
  runs (denote_exp' (Some pointer_type) pointer) s s p ->
  runs (denote_exp' (Some index_type) index) s s i ->
  eval_gep element p [i] = raise_ret value ->
  runs (denote_exp' top
    (OP_GetElementPtr element (pointer_type, pointer) [(index_type, index)]))
    s s value.
Proof.
  intros Pointer Index Value. unfold denote_exp'. cbn [denote_exp].
  eapply runs_with_call_bind; [exact Pointer|].
  cbn [map_monad].
  eapply runs_with_call_bind.
  - eapply runs_with_call_bind; [exact Index|].
    eapply runs_with_call_bind; apply runs_with_call_ret.
  - apply runs_eou, Value.
Qed.

Lemma runs_assign id op metadata varargs s value :
  runs (denote_exp' None op) s s value ->
  runs (denote_instr (IId id, INSTR_Op op, metadata) varargs) s
    (set_local s id value) tt.
Proof.
  intro Value. unfold denote_instr.
  eapply runs_bind; [exact Value|].
  eapply runs_bind; [apply runs_local_write|apply runs_ret].
Qed.

Lemma runs_instruction_load id dt pointer_type pointer annotations metadata varargs
    s p m value :
  runs (denote_exp' (Some pointer_type) pointer) s s
    (DVALUE_Base (DVALUE_Pointer p)) ->
  MemoryRelation.run_memory (MemoryRelation.Impl.read_dvalue dt p) (fst s) =
    Ret (m, value) ->
  runs (denote_instr
    (IId id, INSTR_Load dt (pointer_type, pointer) annotations, metadata) varargs) s
    (set_local (with_memory s m) id value) tt.
Proof.
  intros Pointer Read. unfold denote_instr.
  eapply runs_bind; [exact Pointer|].
  eapply runs_bind; [apply runs_load, Read|apply runs_local_write].
Qed.

Lemma runs_instruction_store id dt value pointer_type pointer annotations metadata
    varargs s v p m :
  runs (denote_exp' (Some dt) value) s s v ->
  runs (denote_exp' (Some pointer_type) pointer) s s
    (DVALUE_Base (DVALUE_Pointer p)) ->
  MemoryRelation.run_memory (MemoryRelation.Impl.write_dvalue p dt v) (fst s) =
    Ret (m, tt) ->
  runs (denote_instr
    (IVoid id, INSTR_Store (dt, value) (pointer_type, pointer) annotations, metadata)
    varargs) s (with_memory s m) tt.
Proof.
  intros Value Pointer Write. unfold denote_instr.
  eapply runs_bind; [exact Value|].
  eapply runs_bind; [exact Pointer|].
  eapply runs_bind; [apply runs_store, Write|apply runs_ret].
Qed.

Lemma runs_instruction_read id dt pointer_type pointer annotations metadata varargs
    s p value :
  runs (denote_exp' (Some pointer_type) pointer) s s
    (DVALUE_Base (DVALUE_Pointer p)) ->
  MemoryRelation.run_memory (MemoryRelation.Impl.read_dvalue dt p) (fst s) =
    Ret (fst s, value) ->
  runs (denote_instr
    (IId id, INSTR_Load dt (pointer_type, pointer) annotations, metadata) varargs) s
    (set_local s id value) tt.
Proof.
  intros Pointer Read.
  pose proof (@runs_instruction_load id dt pointer_type pointer annotations metadata
    varargs s p (fst s) value Pointer Read) as Step.
  rewrite with_memory_same in Step. exact Step.
Qed.

Lemma runs_code_nil varargs s : runs (denote_code [] varargs) s s tt.
Proof. apply runs_ret. Qed.

Lemma runs_code_cons i rest varargs s middle final :
  runs (denote_instr i varargs) s middle tt ->
  runs (denote_code rest varargs) middle final tt ->
  runs (denote_code (i :: rest) varargs) s final tt.
Proof. intros First Last; eapply runs_bind; eassumption. Qed.

Lemma runs_return id dt e metadata s value :
  runs (denote_exp' (Some dt) e) s s value ->
  runs (denote_terminator (id, TERM_Ret (dt, e), metadata)) s s (inr value).
Proof.
  intro Value. unfold denote_terminator.
  eapply runs_bind; [exact Value|apply runs_ret].
Qed.

Lemma runs_jump id target metadata s :
  runs (denote_terminator (id, TERM_Br_1 target, metadata)) s s (inl target).
Proof. apply runs_ret. Qed.

Definition boolean_value (b : bool) : dvalue :=
  DVALUE_Base (DVALUE_I 1
    (if b then Vellvm.Numeric.Integers.one else Vellvm.Numeric.Integers.zero)).

Lemma runs_branch id e yes no metadata s choice :
  runs (denote_exp' (Some (DTYPE_I 1 : dtyp)) e) s s (boolean_value choice) ->
  runs (denote_terminator (id, TERM_Br ((DTYPE_I 1 : dtyp), e) yes no, metadata)) s s
    (inl (if choice then yes else no)).
Proof.
  intro Value. unfold denote_terminator.
  eapply runs_bind; [exact Value|].
  destruct choice; apply runs_ret.
Qed.

Lemma runs_block_no_phis label code term comments from varargs s middle final result :
  runs (denote_code code varargs) s middle tt ->
  runs (denote_terminator term) middle final result ->
  runs (denote_block (mk_block label [] code term comments) from varargs) s final result.
Proof.
  intros Code Term. unfold denote_block.
  eapply runs_bind.
  - cbn [blk_phis denote_phis map_monad].
    eapply runs_bind; [apply runs_ret|].
    eapply runs_bind; apply runs_ret.
  - eapply runs_bind; eassumption.
Qed.

Lemma runs_phi from id dt args metadata operand s value :
  assoc from args = Some operand ->
  runs (denote_exp' (Some dt) operand) s s value ->
  runs (denote_phi from (id, Phi dt args, metadata)) s s (id, value).
Proof.
  intros Found Value. unfold denote_phi. rewrite Found.
  eapply runs_bind; [exact Value|apply runs_ret].
Qed.

Lemma runs_phis_single from id dt args metadata operand s value :
  assoc from args = Some operand ->
  runs (denote_exp' (Some dt) operand) s s value ->
  runs (denote_phis from [(id, Phi dt args, metadata)]) s
    (set_local s id value) tt.
Proof.
  intros Found Value. unfold denote_phis. cbn [map_monad].
  eapply runs_bind.
  - eapply runs_bind; [eapply runs_phi; eassumption|].
    eapply runs_bind; apply runs_ret.
  - cbn [map_monad]. eapply runs_bind.
    + eapply runs_bind; [apply runs_local_write|].
      eapply runs_bind; apply runs_ret.
    + apply runs_ret.
Qed.

Lemma runs_block_single_phi label id dt args metadata code term comments
    from varargs operand s middle final value result :
  assoc from args = Some operand ->
  runs (denote_exp' (Some dt) operand) s s value ->
  runs (denote_code code varargs) (set_local s id value) middle tt ->
  runs (denote_terminator term) middle final result ->
  runs (denote_block
    (mk_block label [(id, Phi dt args, metadata)] code term comments) from varargs)
    s final result.
Proof.
  intros Found Value Code Term. unfold denote_block.
  eapply runs_bind.
  - eapply runs_phis_single; eassumption.
  - eapply runs_bind; eassumption.
Qed.

Lemma runs_block b from varargs s after_phis middle final result :
  runs (denote_phis from (blk_phis b)) s after_phis tt ->
  runs (denote_code (blk_code b) varargs) after_phis middle tt ->
  runs (denote_terminator (blk_term b)) middle final result ->
  runs (denote_block b from varargs) s final result.
Proof.
  intros Phis Code Term. unfold denote_block.
  eapply runs_bind; [exact Phis|].
  eapply runs_bind; eassumption.
Qed.
