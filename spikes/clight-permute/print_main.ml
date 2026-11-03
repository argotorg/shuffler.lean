(* SPDX-License-Identifier: GPL-3.0-or-later *)
let () =
  try print_string (Printer.print Extracted.permute)
  with Printer.Unsupported why ->
    prerr_endline ("Clight printer rejected input: " ^ why); exit 1
