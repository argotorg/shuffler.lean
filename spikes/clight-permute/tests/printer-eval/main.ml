(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Extracted

let unsigned token =
  let value = int_of_string token in
  if value < 0 || value > 4294967295 then invalid_arg "not a uint32";
  value
let rec split count xs =
  if count = 0 then [], xs
  else match xs with
    | x :: rest -> let a, b = split (count - 1) rest in x :: a, b
    | [] -> invalid_arg "missing input word"
let text chars = String.of_seq (List.to_seq chars)

let evaluate fn line =
  let fields = List.filter ((<>) "") (String.split_on_char ' ' line) in
  match List.map unsigned fields with
  | 8 :: fuel :: words when fuel <= 100000 ->
      let xs, tail = split 8 words in
      let ys, rest = split 8 tail in
      if rest <> [] then invalid_arg "extra input words";
      begin match run_generated (Generator.natural fuel) fn
        (List.map Generator.integer xs) (List.map Generator.integer ys) with
      | None -> print_endline "INCOMPLETE"
      | Some values -> print_endline (String.concat " "
          (List.map (fun v -> text (decimal v)) values))
      end
  | _ -> invalid_arg "expected size 8 and bounded fuel"

let () =
  if Array.length Sys.argv <> 3 then invalid_arg "usage: printer-eval print|run SEED";
  let fn = Generator.program (int_of_string Sys.argv.(2)) in
  match Sys.argv.(1) with
  | "print" -> print_string (Printer.print fn)
  | "run" -> (try while true do evaluate fn (read_line ()) done with End_of_file -> ())
  | _ -> invalid_arg "unknown operation"
