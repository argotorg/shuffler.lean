(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List String ZArith.
From Vellvm Require Import LLVMAst.
Require Import FullNormalize.
Import ListNotations.
Open Scope string_scope.

Definition x : exp typ := EXP_Ident (ID_Local (Name "x")).
Definition p : exp typ := EXP_Ident (ID_Local (Name "p")).

Example store_uses_alignment_one :
  normalize_instruction (INSTR_Store (TYPE_I 32, x) (TYPE_Pointer None, p) []) =
  Some (INSTR_Store (TYPE_I 32, x) (TYPE_Pointer None, p) align_one).
Proof. reflexivity. Qed.

Example overflow_flags_removed :
  normalize_operation (OP_IBinop (Add true true) (TYPE_I 64) x x) =
  Some (OP_IBinop (Add false false) (TYPE_I 64) x x).
Proof. reflexivity. Qed.

Example conversion_flags_removed :
  normalize_operation (OP_Conversion (CONV_Pure (Zext true))
    (TYPE_I 32) x (TYPE_I 64)) =
  Some (OP_Conversion (CONV_Pure (Zext false)) (TYPE_I 32) x (TYPE_I 64)).
Proof. reflexivity. Qed.

Example volatile_store_rejected :
  normalize_instruction (INSTR_Store (TYPE_I 32, x) (TYPE_Pointer None, p)
    [ANN_volatile]) = None.
Proof. reflexivity. Qed.

Example atomic_store_rejected :
  normalize_instruction (INSTR_Store (TYPE_I 32, x) (TYPE_Pointer None, p)
    [ANN_atomic]) = None.
Proof. reflexivity. Qed.

Example wide_store_rejected :
  normalize_instruction (INSTR_Store (TYPE_I 64, x) (TYPE_Pointer None, p) []) = None.
Proof. reflexivity. Qed.

Example poison_store_rejected :
  normalize_instruction
    (INSTR_Store (TYPE_I 32, EXP_Poison) (TYPE_Pointer None, p) []) = None.
Proof. reflexivity. Qed.

Example alloca_rejected :
  normalize_instruction (INSTR_Alloca (TYPE_I 32) []) = None.
Proof. reflexivity. Qed.

Example call_rejected :
  normalize_instruction (INSTR_Call (TYPE_I 32, x) [] [] []) = None.
Proof. reflexivity. Qed.

Example changed_signature_rejected :
  has_signature (TYPE_Function (TYPE_I 64) [] false) = false.
Proof. reflexivity. Qed.

Example calling_convention_rejected :
  Normalize.removable_annotation (ANN_cconv CC_Fastcc) = false.
Proof. reflexivity. Qed.

Example empty_module_rejected : FullNormalize.normalize [] = None.
Proof. reflexivity. Qed.

Example wrong_target_rejected :
  FullNormalize.normalize_entities [TLE_Target "aarch64-unknown-linux-gnu"] = None.
Proof. reflexivity. Qed.

Example big_endian_layout_rejected :
  FullNormalize.normalize_entities [TLE_Datalayout "E-p:64:64"] = None.
Proof. reflexivity. Qed.

Example external_declaration_rejected :
  FullNormalize.normalize
    [TLE_Declaration (mk_declaration (Name "external") signature ([], []) [] [])] =
  None.
Proof. reflexivity. Qed.
