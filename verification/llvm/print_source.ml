(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* This C generation step is untrusted. The LLVM candidate is checked later. *)
let () =
  let fn = Extracted.depth_function in
  let parameter (id, _) = "unsigned int " ^ Printer.name id in
  print_string "_Static_assert(sizeof(unsigned int) == 4, \"requires uint32\");\n";
  print_string ("unsigned int shuffler_depth(" ^
    String.concat ", " (List.map parameter fn.Extracted.fn_params) ^ ") {\n");
  print_string (Printer.statement fn 2 false fn.Extracted.fn_body);
  print_string "}\n"
