<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Clight undefined-value copy and C initialization

The printer's syntax check and a Clight call proof do not by themselves
exclude C reads of uninitialized local variables.

`UndefCopy.v` prefixes the actual Permute AST with `Sset i (reg i)`.
At function entry, temporary `i` contains Clight `Vundef`. Copying it to
itself leaves the complete temporary map unchanged. The theorem
`prefix_preserves_call` proves that every original call result, final
memory, and empty external-event trace also holds for the prefixed AST.
Thus all existing postconditions on the returned value and memory transfer.
No production source or existing theorem is changed.

The unchanged printer accepts this AST and emits `v8 = v8;` before any
assignment to `v8`. C11 section 6.3.2.1 paragraph 2 makes this read undefined:
`v8` is an uninitialized automatic scalar whose address is never taken.
Its unsigned type does not remove that rule. Both GCC and Clang report the
uninitialized read. The proof therefore does not give the printed C the
same guarantees without a separate initialization condition.

Current Permute does assign its temporaries before their reads. This probe
shows a limit of the general transfer argument. It does not show that the
current printed Permute has this defect. The printer already states that
initialization is a separate proof obligation; Clight execution correctness
alone cannot discharge that obligation.

After the normal audited dependency build, run:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix' \
  --command sh spikes/clight-permute/tests/equiv-saw/undef-copy/check.sh
```

The script copies current source into an isolated ignored build directory,
extracts the AST, compiles and kernel-checks the transfer theorem, and uses
the unchanged printer. It first compiles the unchanged C with
`-Werror=uninitialized`; it then requires both compilers to reject the
printed variant with an uninitialized-`v8` diagnostic. Logs are in
`build/equiv-saw/undef-copy/`. This test uses the existing Rocq/OCaml/C
compiler environment, not the SAW environment.
