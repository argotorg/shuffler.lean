(* SPDX-License-Identifier: GPL-3.0-or-later *)
open Extracted
let () = print_string (Printer.print
  {permute with fn_body = Ssequence (Sset (i, reg i), permute.fn_body)})
