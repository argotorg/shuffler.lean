(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Extracted

let rec positive n =
  if n = 1 then XH else if n mod 2 = 0 then XO (positive (n / 2))
  else XI (positive (n / 2))
let z n = if n = 0 then Z0 else if n > 0 then Zpos (positive n)
          else Zneg (positive (-n))
let literal n = lit (z n)
let return e = Sreturn (Some e)
let body s = {permute with fn_body = s}
let rejects label fn =
  match Printer.print fn with
  | _ -> failwith ("printer accepted " ^ label)
  | exception Printer.Unsupported _ -> ()
let equal label actual expected =
  if actual <> expected then failwith ("printer mismatch: " ^ label)

let () =
  equal "maximum unsigned literal" (Printer.unsigned permute (literal (-1)))
    "4294967295U";
  equal "precedence" (Printer.unsigned permute
    (sub0 (reg i) (add0 (reg j) (literal 1)))) "(v8 - (v9 + 1U))";
  equal "array index" (Printer.unsigned permute (cell data (literal 0))) "v2[0U]";
  equal "identifier" (Printer.name (positive 123)) "v123";
  equal "loop" (Printer.statement permute 0 false (Sloop (Sbreak, Sskip)))
    "while (1) {\n  break;\n}\n";
  equal "sequence" (Printer.statement permute 0 false
    (seq [Sset (i, literal 1); Sset (j, reg i); return (reg j)]))
    "v8 = 1U;\nv9 = v8;\nreturn v9;\n";
  ignore (Printer.print permute);
  ignore (Printer.print (body (Sloop (Sloop (Sbreak, Sskip), Sskip))));
  ignore (Printer.print (body (Sifthenelse (eq0 (reg i) (reg j),
    return (literal 0), return (literal 1)))));
  equal "nested loop break scope" (Printer.falls_through
    (Sloop (Sloop (Sbreak, Sskip), Sskip))) false;
  equal "outer loop break scope" (Printer.falls_through
    (Sloop (Ssequence (Sloop (Sbreak, Sskip), Sbreak), Sskip))) true;
  let bad_expressions = [
    "signed literal", Econst_int (Int.repr (z 1), i32);
    "float", Econst_float (B754_zero false, Tfloat0 (F64, noattr));
    "single", Econst_single (B754_zero false, Tfloat0 (F32, noattr));
    "long", Econst_long (Z0, Tlong0 (Unsigned, noattr));
    "variable", Evar (i, u32);
    "unknown temp", Etempvar (positive 100, u32);
    "wrong temp type", Etempvar (data, u32);
    "address of", Eaddrof (cell data (literal 0), ptr);
    "unary", Eunop (Onotint, reg i, u32);
    "cast", Ecast (reg i, u32);
    "field", Efield (reg i, j, u32);
    "sizeof", Esizeof (u32, u32);
    "alignof", Ealignof (u32, u32);
    "pointer literal", Econst_int (Int.repr (z 0), ptr);
    "pointer subtraction", Ederef (Ebinop (Osub, Etempvar (data, ptr), literal 0, ptr), u32);
    "wrong pointer result", Ederef (Ebinop (Oadd, Etempvar (data, ptr), literal 0, u32), u32);
    "undeclared pointer", cell (positive 100) (literal 0);
    "scalar as pointer", cell i (literal 0);
    "comparison as index", cell data (eq0 (reg i) (reg j));
    "commuted pointer addition", Ederef (Ebinop (Oadd, literal 0, Etempvar (data, ptr), ptr), u32);
    "wrong dereference type", Ederef (Etempvar (data, ptr), i32);
    "volatile", Etempvar (i, Tint0 (I32, Unsigned, {noattr with attr_volatile = true}));
    "unsigned comparison", Ebinop (Oeq, reg i, reg j, u32)
  ] in
  List.iter (fun (label, expr) -> rejects label (body (return expr))) bad_expressions;
  List.iter (fun op -> rejects "excluded binary operator"
    (body (return (Ebinop (op, reg i, reg j, u32)))))
    [Omul; Odiv; Omod; Oand; Oor; Oxor; Oshl; Oshr; Oeq; One; Olt; Ogt; Ole; Oge];
  let bad_statements = [
    "comparison stored without cast", Sset (i, eq0 (reg i) (reg j));
    "pointer temp assignment", Sset (data, reg i);
    "unknown assignment", Sset (positive 100, literal 0);
    "non-indexed store", Sassign (reg i, literal 0);
    "signed store", Sassign (Ederef
      (Ebinop (Oadd, Etempvar (data, ptr), literal 0, ptr), i32), literal 0);
    "bare pointer store", Sassign (Ederef (Etempvar (data, ptr), u32), literal 0);
    "wrong store value", Sassign (cell data (literal 0), eq0 (reg i) (reg j));
    "call", Scall (None, reg i, []);
    "builtin", Sbuiltin (None, EF_malloc, [], []);
    "bare condition", Sifthenelse (reg i, Sskip, Sskip);
    "unsigned condition type", Sifthenelse (Ebinop (Olt, reg i, reg j, u32), Sskip, Sskip);
    "loop second body", Sloop (Sskip, Sbreak);
    "continue", Sloop (Scontinue, Sskip);
    "break outside loop", Sbreak;
    "break after closed loop", Ssequence (Sloop (Sbreak, Sskip), Sbreak);
    "void return", Sreturn None;
    "switch", Sswitch (reg i, LSnil);
    "label", Slabel (i, Sskip);
    "goto", Sgoto i
  ] in
  List.iter (fun (label, stmt) -> rejects label
    (body (Ssequence (stmt, return (literal 0))))) bad_statements;
  rejects "fallthrough" (body Sskip);
  rejects "loop fallthrough" (body (Sloop (Sbreak, Sskip)));
  rejects "one branch fallthrough" (body
    (Sifthenelse (eq0 (reg i) (reg j), return (literal 0), Sskip)));
  rejects "conditional loop break" (body (Sloop
    (Sifthenelse (eq0 (reg i) (reg j), return (literal 0), Sbreak), Sskip)));
  List.iter (fun op -> rejects "excluded condition operator" (body
    (Sifthenelse (Ebinop (op, reg i, reg j, i32),
      return (literal 0), return (literal 1)))))
    [Oadd; Osub; Omul; Odiv; Omod; Oand; Oor; Oxor; Oshl; Oshr; Ole];
  rejects "duplicate identifier"
    {permute with fn_temps = (i, u32) :: permute.fn_temps};
  rejects "changed parameter" {permute with fn_params = []};
  rejects "extra parameter" {permute with fn_params = permute.fn_params @ [(positive 100, ptr)]};
  rejects "changed parameter order" {permute with fn_params =
    (data, ptr) :: (n0, u32) :: List.tl (List.tl permute.fn_params)};
  rejects "parameter temporary collision" {permute with fn_temps =
    (n0, u32) :: permute.fn_temps};
  rejects "volatile pointee" {permute with fn_params = (n0, u32) ::
    (data, Tpointer (Tint0 (I32, Unsigned, {noattr with attr_volatile = true}), noattr)) ::
    List.tl (List.tl permute.fn_params)};
  rejects "volatile pointer" {permute with fn_params = (n0, u32) ::
    (data, Tpointer (u32, {noattr with attr_volatile = true})) ::
    List.tl (List.tl permute.fn_params)};
  rejects "pointer temporary" {permute with fn_temps = [(i, ptr)]};
  rejects "local storage" {permute with fn_vars = [(positive 100, u32)]};
  rejects "return type" {permute with fn_return = i32};
  rejects "varargs" {permute with fn_callconv = {permute.fn_callconv with cc_vararg = Some (z 1)}};
  rejects "unprototyped" {permute with fn_callconv = {permute.fn_callconv with cc_unproto = true}};
  rejects "struct return" {permute with fn_callconv = {permute.fn_callconv with cc_structret = true}};
  rejects "aligned parameter" {permute with fn_params =
    (n0, Tint0 (I32, Unsigned, {noattr with attr_alignas = Some N0})) :: List.tl permute.fn_params};
  print_endline "printer: output and rejection tests pass"
