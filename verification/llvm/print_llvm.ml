(* SPDX-License-Identifier: GPL-3.0-or-later *)
let () =
  List.iter print_char Exported.emitted_llvm;
  print_newline ()
