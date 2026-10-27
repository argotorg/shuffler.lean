(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Evaluation

let rec positive value =
  if value = 1 then XH
  else if value land 1 = 0 then XO (positive (value lsr 1))
  else XI (positive (value lsr 1))

let integer value = if value = 0 then Z0 else Zpos (positive value)
let rec natural value = if value = 0 then O else S (natural (value - 1))
let text chars = String.of_seq (List.to_seq chars)

let unsigned token =
  let value = int_of_string token in
  if value < 0 || value > 4294967295 then invalid_arg "not a uint32";
  value

let rec split count xs =
  if count = 0 then ([], xs)
  else match xs with
  | x :: rest -> let first, second = split (count - 1) rest in (x :: first, second)
  | [] -> invalid_arg "missing input word"

let evaluate line =
  let fields = List.filter ((<>) "") (String.split_on_char ' ' line) in
  match List.map unsigned fields with
  | size :: fuel :: words ->
      if fuel > 100000 then invalid_arg "fuel exceeds adapter limit";
      let count = if size > 0 && size <= 1024 then size else 0 in
      let data, tail = split count words in
      let permutation, rest = split count tail in
      if rest <> [] then invalid_arg "extra input words";
      begin match run (natural fuel) (integer size)
          (List.map integer data) (List.map integer permutation) with
      | None -> print_endline "INCOMPLETE"
      | Some values -> print_endline
          (String.concat " " (List.map (fun v -> text (decimal v)) values))
      end
  | _ -> invalid_arg "missing size or fuel"

let () =
  try while true do evaluate (read_line ()) done
  with End_of_file -> ()
