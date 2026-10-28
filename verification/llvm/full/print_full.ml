(* SPDX-License-Identifier: GPL-3.0-or-later *)
let () =
  List.iter print_char Full_exported.emitted_llvm;
  print_newline ()
