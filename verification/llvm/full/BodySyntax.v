(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String.
From Vellvm Require Import Syntax ScopeTheory.
Require Import FullCFG.
Import ListNotations.

Inductive plain_expression : exp dtyp -> Prop :=
| plain_local id : plain_expression (EXP_Ident (ID_Local id))
| plain_integer literal : plain_expression (EXP_Integer literal)
| plain_ibinop op dt a b : plain_expression a -> plain_expression b ->
    plain_expression (OP_IBinop op dt a b)
| plain_icmp same op dt a b : plain_expression a -> plain_expression b ->
    plain_expression (OP_ICmp same op dt a b)
| plain_conversion op source a target : plain_expression a ->
    plain_expression (OP_Conversion (CONV_Pure op) source a target)
| plain_gep element pt pointer it index : plain_expression pointer -> plain_expression index ->
    plain_expression (OP_GetElementPtr element (pt, pointer) [(it, index)]).

Inductive plain_instruction : instr_id * instr dtyp * list (metadata dtyp) -> Prop :=
| plain_op id op md : plain_expression op -> plain_instruction (IId id, INSTR_Op op, md)
| plain_load id dt pt pointer annotations md : plain_expression pointer ->
    plain_instruction (IId id, INSTR_Load dt (pt, pointer) annotations, md)
| plain_store id dt value pt pointer annotations md :
    plain_expression value -> plain_expression pointer ->
    plain_instruction (IVoid id, INSTR_Store (dt, value) (pt, pointer) annotations, md).

Inductive plain_terminator : instr_id * terminator dtyp * list (metadata dtyp) -> Prop :=
| plain_return id dt value md : plain_expression value ->
    plain_terminator (id, TERM_Ret (dt, value), md)
| plain_branch id dt value yes no md : plain_expression value ->
    plain_terminator (id, TERM_Br (dt, value) yes no, md)
| plain_jump id target md : plain_terminator (id, TERM_Br_1 target, md).

Inductive plain_phi : local_id * phi dtyp * list (metadata dtyp) -> Prop :=
| plain_phi_arms id dt arms md : Forall (fun arm => plain_expression (snd arm)) arms ->
    plain_phi (id, Phi dt arms, md).

Record plain_block (b : LLVMAst.block dtyp) : Prop := {
  plain_block_phis : Forall plain_phi (blk_phis b);
  plain_block_code : Forall plain_instruction (blk_code b);
  plain_block_terminator : plain_terminator (blk_term b)
}.

Theorem body_plain : Forall plain_block (blks FullCFG.body).
Proof. repeat constructor. Qed.

Lemma body_block_plain label b : find_block (blks FullCFG.body) label = Some b -> plain_block b.
Proof.
  intro Found. eapply Forall_forall; [exact body_plain|].
  unfold find_block in Found. apply find_some in Found. exact (proj1 Found).
Qed.
