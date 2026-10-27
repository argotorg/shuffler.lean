(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Extracted
open Generator

let body = seq [
  put out (literal 0) (literal 0);
  put out (literal 1) (sub (literal 0) (literal 1));
  put out (literal 2) (cell data (add (literal 4294967295) (literal 1)));
  put data (literal 1) (add (cell data (literal 0)) (cell permutation (literal 1)));
  put permutation (literal 2) (sub (cell data (literal 2)) (cell permutation (literal 0)));
  Sreturn (Some (cell out (literal 2)))
]

let rename = rename_id 2
let declarations = List.map (fun (id, ty) -> rename id, ty)
let fn = { permute with fn_params = declarations permute.fn_params;
                       fn_temps = [];
                       fn_body = rename_statement rename body }

let () = match Sys.argv.(1) with
  | "print" -> print_string (Printer.print fn)
  | "run" -> begin match run_generated (natural 100) fn
      (List.map integer [4294967295; 0; 2; 3; 4; 5; 6; 7])
      (List.map integer [1; 2; 3; 4; 5; 6; 7; 8]) with
    | None -> failwith "literal control is incomplete"
    | Some values -> print_endline (String.concat " " (List.map
        (fun x -> String.of_seq (List.to_seq (decimal x))) values))
    end
  | _ -> invalid_arg "expected print or run"
