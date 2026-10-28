(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Bool String ZArith.
From Vellvm Require Import LLVMAst.
Require Import Normalize.
Import ListNotations.
Open Scope string_scope.

(* This constructs a new candidate. It does not claim that annotation removal
   preserves the input program. A full-call proof must check this AST before
   any LLVM or native object is exported for use. *)
Definition scalar_type (t : typ) :=
  match t with TYPE_I 1 | TYPE_I 32 | TYPE_I 64 => true | _ => false end.

Definition operand (v : exp typ) :=
  match v with
  | EXP_Ident (ID_Local _) | EXP_Integer _ | EXP_Bool _ => true
  | _ => false
  end.

Definition pointer_operand (v : exp typ) :=
  match v with EXP_Ident (ID_Local _) => true | _ => false end.

Definition normalize_binop (op : ibinop) : option ibinop :=
  match op with
  | Add _ _ => Some (Add false false)
  | Sub _ _ => Some (Sub false false)
  | Shl _ _ => Some (Shl false false)
  | And => Some And
  | _ => None
  end.

Definition normalize_operation (e : exp typ) : option (exp typ) :=
  match e with
  | OP_IBinop op t a b =>
      match normalize_binop op with
      | Some op' => if scalar_type t && operand a && operand b
          then Some (OP_IBinop op' t a b) else None
      | None => None
      end
  | OP_ICmp _ cmp t a b =>
      if scalar_type t && operand a && operand b
      then Some (OP_ICmp false cmp t a b) else None
  | OP_Conversion (CONV_Pure (Zext _)) (TYPE_I 32) v (TYPE_I 64) =>
      if operand v then Some
        (OP_Conversion (CONV_Pure (Zext false)) (TYPE_I 32) v (TYPE_I 64))
      else None
  | OP_Conversion (CONV_Pure (Trunc _ _)) (TYPE_I 64) v (TYPE_I 32) =>
      if operand v then Some
        (OP_Conversion (CONV_Pure (Trunc false false)) (TYPE_I 64) v (TYPE_I 32))
      else None
  | OP_GetElementPtr t (TYPE_Pointer None, p) [(TYPE_I 64, i)] =>
      let element_type := match t with TYPE_I 8 | TYPE_I 32 => true | _ => false end in
      if element_type && pointer_operand p && operand i then Some e else None
  | _ => None
  end.

Definition memory_annotation (a : annotation typ) :=
  match a with ANN_align _ => true | _ => false end.

Definition align_one : list (annotation typ) :=
  [ANN_align (Number.IntDecimal (Decimal.Pos (Decimal.D1 Decimal.Nil)))].

Definition normalize_instruction (i : instr typ) : option (instr typ) :=
  match i with
  | INSTR_Op e => option_map INSTR_Op (normalize_operation e)
  | INSTR_Load (TYPE_I 32) (TYPE_Pointer None, p) annotations =>
      if pointer_operand p && forallb memory_annotation annotations then
        Some (INSTR_Load (TYPE_I 32) (TYPE_Pointer None, p) align_one)
      else None
  | INSTR_Store (TYPE_I 32, v) (TYPE_Pointer None, p) annotations =>
      if operand v && pointer_operand p && forallb memory_annotation annotations then
        Some (INSTR_Store (TYPE_I 32, v) (TYPE_Pointer None, p) align_one)
      else None
  | _ => None
  end.

Fixpoint traverse {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: rest =>
      match f x, traverse f rest with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition normalize_phi (p : local_id * phi typ * list (metadata typ))
    : option (local_id * phi typ * list (metadata typ)) :=
  let '(id, Phi t entries, _) := p in
  if scalar_type t && forallb (fun entry => operand (snd entry)) entries then
    Some (id, Phi t entries, []) else None.

Definition normalize_code (c : code typ) : option (code typ) :=
  traverse (fun '(id, i, _) =>
    option_map (fun i' => (id, i', [])) (normalize_instruction i)) c.

Definition terminator_supported (t : terminator typ) :=
  match t with
  | TERM_Ret (TYPE_I 32, v) | TERM_Br (TYPE_I 1, v) _ _ => operand v
  | TERM_Br_1 _ => true
  | _ => false
  end.

Definition normalize_block (b : block typ) : option (block typ) :=
  let '(id, term, _) := blk_term b in
  if terminator_supported term then
    match traverse normalize_phi (blk_phis b), normalize_code (blk_code b) with
    | Some phis, Some code =>
        Some (mk_block (blk_id b) phis code (id, term, []) None)
    | _, _ => None
    end
  else None.

Definition parameter_attribute (a : param_attr) :=
  match a with
  | PARAMATTR_Noundef | PARAMATTR_Nocapture | PARAMATTR_Writeonly
  | PARAMATTR_Range _ _ _ | PARAMATTR_Initializes _ => true
  | _ => false
  end.

Definition function_attribute (a : fn_attr) :=
  match a with
  | FNATTR_String "no-builtins" => true
  | _ => Normalize.removable_function_attribute a
  end.

Definition signature := TYPE_Function (TYPE_I 32)
  [TYPE_I 32; TYPE_Pointer None; TYPE_Pointer None; TYPE_Pointer None;
   TYPE_Pointer None; TYPE_Pointer None; TYPE_Pointer None] false.

Definition has_signature (t : typ) :=
  match t with
  | TYPE_Function (TYPE_I 32)
      [TYPE_I 32; TYPE_Pointer None; TYPE_Pointer None; TYPE_Pointer None;
       TYPE_Pointer None; TYPE_Pointer None; TYPE_Pointer None] false => true
  | _ => false
  end.

Definition target := "x86_64-unknown-linux-gnu".
Definition data_layout :=
  "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128".

Definition normalize_function (f : definition typ (block typ * list (block typ)))
    : option (definition typ (block typ * list (block typ))) :=
  let p := df_prototype f in
  let '(entry, blocks) := df_instrs f in
  if has_signature (dc_type p) && Nat.eqb (List.length (df_args f)) 7 &&
      Nat.eqb (List.length (snd (dc_param_attrs p))) 7 &&
      forallb parameter_attribute (fst (dc_param_attrs p)) &&
      forallb (forallb parameter_attribute) (snd (dc_param_attrs p)) &&
      forallb function_attribute (dc_attrs p) &&
      forallb Normalize.removable_annotation (dc_annotations p) then
    match normalize_block entry, traverse normalize_block blocks with
    | Some entry', Some blocks' => Some (mk_definition
        (mk_declaration (dc_name p) signature ([], repeat [] 7) [] [])
        (df_args f) (entry', blocks'))
    | _, _ => None
    end
  else None.

Fixpoint normalize_entities (p : llvm_module) : option llvm_module :=
  match p with
  | [] => Some []
  | h :: t =>
      match normalize_entities t with
      | None => None
      | Some tail =>
          match h with
          | TLE_Definition f => option_map (fun f' => TLE_Definition f' :: tail)
              (normalize_function f)
          | TLE_Target t => if String.eqb t target then Some (h :: tail) else None
          | TLE_Datalayout d =>
              if String.eqb d data_layout then Some (h :: tail) else None
          | TLE_Attribute_group _ attrs =>
              if forallb function_attribute attrs then Some tail else None
          | TLE_Metadata _ _ _ | TLE_Source_filename _ | TLE_Comment _ => Some tail
          | _ => None
          end
      end
  end.

Definition normalize (p : llvm_module) : option llvm_module :=
  match normalize_entities p with
  | None => None
  | Some p' =>
      let count f := List.length (filter f p') in
      if Nat.eqb (count
          (fun e => match e with TLE_Definition _ => true | _ => false end)) 1 &&
        Nat.eqb (count
          (fun e => match e with TLE_Target _ => true | _ => false end)) 1 &&
        Nat.eqb (count
          (fun e => match e with TLE_Datalayout _ => true | _ => false end)) 1
      then Some p' else None
  end.
