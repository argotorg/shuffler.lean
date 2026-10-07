(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Extracted

(* Extraction disambiguates names also used by arithmetic libraries. *)
let n = n0
let add = add0
let sub = sub0
let eq = eq0
let lt = lt0

let rec positive value =
  if value = 1 then XH
  else if value land 1 = 0 then XO (positive (value lsr 1))
  else XI (positive (value lsr 1))
let integer value = if value = 0 then Z0 else Zpos (positive value)
let literal value = lit (integer value)
let rec natural value = if value = 0 then O else S (natural (value - 1))

(* Pure, deterministic selection. Generator arithmetic is separate from
   the Rocq arithmetic used to execute each generated expression. *)
let choose seed tag count =
  let open Stdlib.Int64 in
  let x = add (of_int seed) (mul (of_int tag) 0x9e3779b97f4a7c15L) in
  let x = mul (logxor x (shift_right_logical x 30)) 0xbf58476d1ce4e5b9L in
  let x = mul (logxor x (shift_right_logical x 27)) 0x94d049bb133111ebL in
  let x = logxor x (shift_right_logical x 31) in
  to_int (rem (logand x 0x3fffffffL) (of_int count))

let at values index = List.nth values index
let constants = [0; 1; 7; 8; 16; 2147483647; 2147483648; 4294967294; 4294967295]
let writable = [n; top; pos; tmp; depth]

let index seed tag =
  let k = choose seed tag 8 in
  match choose seed (tag + 71) 5 with
  | 0 -> literal k
  | 1 -> add (literal 4294967295) (literal (k + 1))
  | 2 -> sub (literal (k + 8)) (literal 8)
  | 3 -> add (literal k) (sub (literal 4294967295) (literal 4294967295))
  | _ -> sub (literal (2147483648 + k)) (literal 2147483648)

let rec expression seed tag level =
  if level = 0 then
    match choose seed tag 5 with
    | 0 -> literal (at constants (choose seed (tag + 1) (List.length constants)))
    | 1 -> reg (at writable (choose seed (tag + 2) (List.length writable)))
    | 2 -> cell data (index seed (tag + 3))
    | 3 -> cell permutation (index seed (tag + 4))
    | _ -> cell out (literal (1 + choose seed (tag + 5) 2))
  else
    let left = expression seed (tag * 2 + 1) (level - 1) in
    let right = expression seed (tag * 2 + 2) (level - 1) in
    if choose seed tag 2 = 0 then add left right else sub left right

let condition seed tag =
  let left = expression seed (tag + 1) 2 in
  let right = expression seed (tag + 2) 2 in
  (at [eq; ne; lt; gt; ge] (choose seed tag 5)) left right

let assignment seed tag =
  let value = expression seed (tag + 1) 3 in
  match choose seed tag 4 with
  | 0 -> set1 (at writable (choose seed (tag + 2) (List.length writable))) value
  | 1 -> put data (index seed (tag + 3)) value
  | 2 -> put permutation (index seed (tag + 4)) value
  | _ -> put out (literal (1 + choose seed (tag + 5) 2)) value

let rec statement seed tag level =
  if level = 0 then assignment seed tag
  else match choose seed tag 3 with
  | 0 -> assignment seed tag
  | 1 -> Ssequence (statement seed (tag * 2 + 1) (level - 1),
                    statement seed (tag * 2 + 2) (level - 1))
  | _ -> Sifthenelse (condition seed tag,
                      statement seed (tag * 2 + 1) (level - 1),
                      statement seed (tag * 2 + 2) (level - 1))

let rec shift_id count id = if count = 0 then id else XO (shift_id (count - 1) id)
let rename_id seed id = match seed mod 3 with
  | 0 -> id
  | 1 -> XI id
  | _ -> shift_id 80 id

let rec rename_expression rename = function
  | Econst_int _ as e -> e
  | Etempvar (id, ty) -> Etempvar (rename id, ty)
  | Ederef (e, ty) -> Ederef (rename_expression rename e, ty)
  | Ebinop (op, a, b, ty) -> Ebinop (op, rename_expression rename a,
                                    rename_expression rename b, ty)
  | _ -> invalid_arg "unexpected generated expression"

let rec rename_statement rename value =
  let exp = rename_expression rename in
  let stmt = rename_statement rename in
  match value with
  | Sskip -> Sskip
  | Sbreak -> Sbreak
  | Sset (id, e) -> Sset (rename id, exp e)
  | Sassign (a, b) -> Sassign (exp a, exp b)
  | Ssequence (a, b) -> Ssequence (stmt a, stmt b)
  | Sifthenelse (e, a, b) -> Sifthenelse (exp e, stmt a, stmt b)
  | Sloop (a, b) -> Sloop (stmt a, stmt b)
  | Sreturn (Some e) -> Sreturn (Some (exp e))
  | _ -> invalid_arg "unexpected generated statement"

let program seed =
  if seed < 0 || seed > 1000000 then invalid_arg "program seed outside domain";
  let initialize = List.mapi (fun tag (id, _) ->
      set1 id (literal (at constants (choose seed tag (List.length constants)))))
      permute.fn_temps in
  let body = seq (initialize @ [
    put out (literal 0) (literal 0);
    put out (literal 1) (literal 0);
    put out (literal 2) (literal 0);
    statement seed 100 3;
    set1 i (literal 0);
    loop (lt (reg i) (literal 4)) (seq [
      set1 j (literal 0);
      loop (lt (reg j) (literal 3)) (seq [
        statement seed 200 2;
        inc j;
        when0 (condition seed 300) Sbreak;
        when0 (condition seed 400)
          (Sreturn (Some (expression seed 500 2)))
      ]);
      statement seed 600 2;
      inc i
    ]);
    statement seed 700 3;
    Sreturn (Some (expression seed 800 3))
  ]) in
  let rename = rename_id seed in
  let declarations = List.map (fun (id, ty) -> rename id, ty) in
  { permute with fn_params = declarations permute.fn_params;
                 fn_temps = declarations permute.fn_temps;
                 fn_body = rename_statement rename body }
