(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Bool String ZArith.
From Vellvm Require Import LLVMAst.
Import ListNotations.
Open Scope string_scope.

Definition llvm_module := list (toplevel_entity typ (block typ * list (block typ))).

(* This projection constructs a candidate for a NEW module. It makes no claim
   that the input module has the same behavior. The theorem checks the result.
   Only a scalar, non-variadic C ABI is accepted at this first stage. *)
Definition source_location (m : metadata typ) : bool :=
  match m with METADATA_File_info _ => true | _ => false end.

Definition removable_parameter_attribute (a : param_attr) : bool :=
  match a with PARAMATTR_Noundef => true | _ => false end.

Definition removable_function_attribute (a : fn_attr) : bool :=
  match a with
  | FNATTR_Mustprogress | FNATTR_Nofree | FNATTR_Norecurse | FNATTR_Nosync
  | FNATTR_Nounwind | FNATTR_Sspstrong | FNATTR_Willreturn | FNATTR_Uwtable _
  | FNATTR_Memory _ | FNATTR_Attr_grp _ => true
  | FNATTR_Key_value (key, _) =>
      existsb (String.eqb key)
        ["frame-pointer"; "min-legal-vector-width"; "no-trapping-math";
         "probe-stack"; "stack-protector-buffer-size"; "target-cpu";
         "target-features"; "tune-cpu"; "zero-call-used-regs"]
  | _ => false
  end.

Definition removable_annotation (a : annotation typ) : bool :=
  match a with ANN_unnamed_addr _ => true | _ => false end.

Definition normalize_definition (f : definition typ (block typ * list (block typ)))
    : option (definition typ (block typ * list (block typ))) :=
  match f with
  | mk_definition
      (mk_declaration name (TYPE_Function (TYPE_I 32) [TYPE_I 32; TYPE_I 32] false)
        (ret_attrs, [a1; a2]) attrs annotations)
      [arg1; arg2]
      (mk_block label []
        [(id, INSTR_Op (OP_IBinop op (TYPE_I 32) lhs rhs), md)]
        (ret_id, TERM_Ret (TYPE_I 32, result), ret_md) comments, []) =>
      let accepted_op :=
        match op with Sub false false | Add false false => true | _ => false end in
      let local_value v := match v with EXP_Ident (ID_Local _) => true | _ => false end in
      if accepted_op && local_value lhs && local_value rhs && local_value result &&
         forallb source_location md && forallb source_location ret_md &&
         forallb removable_parameter_attribute (ret_attrs ++ a1 ++ a2) &&
         forallb removable_function_attribute attrs &&
         forallb removable_annotation annotations then
        Some (mk_definition
          (mk_declaration name (TYPE_Function (TYPE_I 32) [TYPE_I 32; TYPE_I 32] false)
            ([], [[]; []]) [] [])
          [arg1; arg2]
          (mk_block label []
            [(id, INSTR_Op (OP_IBinop op (TYPE_I 32) lhs rhs), [])]
            (ret_id, TERM_Ret (TYPE_I 32, result), []) None, []))
      else None
  | _ => None
  end.

Fixpoint normalize_entities (p : llvm_module) : option llvm_module :=
  match p with
  | [] => Some []
  | h :: t =>
      match normalize_entities t with
      | None => None
      | Some tail =>
          match h with
          | TLE_Definition f =>
              match normalize_definition f with
              | Some f' => Some (TLE_Definition f' :: tail)
              | None => None
              end
          | TLE_Target _ | TLE_Datalayout _ => Some (h :: tail)
          | TLE_Attribute_group _ attrs =>
              if forallb removable_function_attribute attrs then Some tail else None
          (* Detached metadata and module flags do not enter the new module.
             Instruction metadata other than source locations is rejected. *)
          | TLE_Metadata _ _ _ | TLE_Source_filename _ | TLE_Comment _ => Some tail
          | _ => None
          end
      end
  end.

Definition normalize (p : llvm_module) : option llvm_module :=
  match normalize_entities p with
  | None => None
  | Some p' =>
      if Nat.eqb (List.length (filter
        (fun e => match e with TLE_Definition _ => true | _ => false end) p')) 1
      then Some p' else None
  end.
