(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* A printer for one function and one ABI. No output is written until the
   complete function passes these checks. Bounds and initialization are
   proof obligations, not properties of this syntax check. *)
open Extracted

exception Unsupported of string
let reject why = raise (Unsupported why)
let require condition why = if not condition then reject why
let chars cs = String.of_seq (List.to_seq cs)
let name id = "v" ^ chars (decimal_ident id)

let declared fn id ty =
  List.assoc_opt id (fn.fn_params @ fn.fn_temps) = Some ty

let rec unsigned fn = function
  | Econst_int (value, ty) when ty = u32 ->
      chars (decimal_int value) ^ "U"
  | Etempvar (id, ty) when ty = u32 && declared fn id u32 -> name id
  | Ederef (address, ty) when ty = u32 -> indexed fn address
  | Ebinop (op, left, right, ty) when ty = u32 ->
      let symbol = match op with
        | Oadd -> "+" | Osub -> "-"
        | _ -> reject "unsigned operator" in
      "(" ^ unsigned fn left ^ " " ^ symbol ^ " " ^ unsigned fn right ^ ")"
  | _ -> reject "unsigned expression"
and indexed fn = function
  | Ebinop (Oadd, Etempvar (id, base_ty), index, result_ty)
      when base_ty = ptr && result_ty = ptr && declared fn id ptr ->
      name id ^ "[" ^ unsigned fn index ^ "]"
  | _ -> reject "array address"

let condition fn = function
  | Ebinop (op, left, right, ty) when ty = i32 ->
      let symbol = match op with
        | Oeq -> "==" | One -> "!=" | Olt -> ">" | Ogt -> ">" | Oge -> ">="
        | _ -> reject "condition operator" in
      "(" ^ unsigned fn left ^ " " ^ symbol ^ " " ^ unsigned fn right ^ ")"
  | _ -> reject "condition"

(* Return whether a statement can reach its end. This conservative check
   rejects a nonvoid function with a path that can fall through. *)
let rec falls_through = function
  | Sreturn _ | Sbreak -> false
  | Ssequence (a, b) -> falls_through a && falls_through b
  | Sifthenelse (_, a, b) -> falls_through a || falls_through b
  | Sloop (body, Sskip) -> breaks_loop body
  | _ -> true
and breaks_loop = function
  | Sbreak -> true
  | Ssequence (a, b) -> breaks_loop a || (falls_through a && breaks_loop b)
  | Sifthenelse (_, a, b) -> breaks_loop a || breaks_loop b
  | _ -> false

let rec statement fn indent in_loop stmt =
  let pad = String.make indent ' ' in
  let line s = pad ^ s ^ "\n" in
  let block s = statement fn (indent + 2) in_loop s in
  match stmt with
  | Sskip -> ""
  | Sset (id, value) ->
      require (declared fn id u32) "scalar assignment target";
      line (name id ^ " = " ^ unsigned fn value ^ ";")
  | Sassign (Ederef (address, ty), value) when ty = u32 ->
      line (indexed fn address ^ " = " ^ unsigned fn value ^ ";")
  | Ssequence (a, b) ->
      statement fn indent in_loop a ^ statement fn indent in_loop b
  | Sifthenelse (test, yes, no) ->
      line ("if " ^ condition fn test ^ " {") ^ block yes ^
      line "} else {" ^ block no ^ line "}"
  | Sloop (body, Sskip) ->
      line "while (1) {" ^ statement fn (indent + 2) true body ^ line "}"
  | Sbreak when in_loop -> line "break;"
  | Sreturn (Some value) -> line ("return " ^ unsigned fn value ^ ";")
  | _ -> reject "statement"

let preamble = "/* SPDX-License-Identifier: GPL-3.0-or-later */\n\
/* Generated from Permute.permute by printer.ml. Do not edit. */\n\
#include <limits.h>\n\
#include \"permute.h\"\n\
_Static_assert(CHAR_BIT == 8, \"8-bit bytes required\");\n\
_Static_assert(sizeof(unsigned int) == 4, \"32-bit unsigned int required\");\n\
_Static_assert(UINT_MAX == 4294967295U, \"32-bit unsigned int required\");\n\
_Static_assert(INT_MAX == 2147483647, \"32-bit int required\");\n\
_Static_assert(_Alignof(unsigned int) == 4, \"4-byte alignment required\");\n\
_Static_assert(sizeof(void *) == 8, \"64-bit pointers required\");\n\n"

let print fn =
  (* This printer supports only the reviewed interface. Keeping these checks
     independent of fn prevents a changed declaration from changing the ABI. *)
  let ids = List.map fst (fn.fn_params @ fn.fn_temps) in
  require (List.length ids = List.length (List.sort_uniq compare ids))
    "duplicate identifier";
  require (List.map snd fn.fn_params = [u32; ptr; ptr; ptr; ptr; ptr; ptr])
    "parameters";
  require (List.for_all (fun (_, ty) -> ty = u32) fn.fn_temps) "temporaries";
  require (fn.fn_return = u32 && fn.fn_vars = [] &&
           fn.fn_callconv = {cc_vararg = None; cc_unproto = false; cc_structret = false})
    "function declaration";
  require (not (falls_through fn.fn_body)) "function can fall through";
  let declaration (id, ty) =
    (if ty = u32 then "unsigned int "
     else if ty = ptr then "unsigned int *"
     else reject "declaration type") ^ name id in
  let body = statement fn 2 false fn.fn_body in
  preamble ^ "unsigned int permute(" ^
  String.concat ", " (List.map declaration fn.fn_params) ^ ")\n{\n" ^
  String.concat "" (List.map (fun d -> "  " ^ declaration d ^ ";\n") fn.fn_temps) ^
  body ^ "}\n"
