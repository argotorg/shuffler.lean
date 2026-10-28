# Full call proofs

`FullCall.permute_call_refines` covers the actual Vellvm function call. It includes
argument binding, the local and memory frame pushes, Vellvm's empty varargs
allocation and store, the complete body, exception handling, and both frame pops.
The theorem derives execution from input conditions. It does not assume successful
body execution or preserved frames.

For a nonempty input, the conditions are:

- At most 1024 positions, with each source value in the unsigned 32-bit range.
- A permutation supplied through the existing finite permutation type.
- Six separate buffers with the capacities required by the Clight contract.
- Data and permutation arrays initialized in the related Clight and LLVM memories.

The result includes the return code, data array, permutation array, trace, and
three output fields. These agree with `SolcModel.solc_permute`, including the
blocked result. The caller's locals, call stack, and global environment are
restored. Arrays outside the six buffers keep their contents. Scratch buffers
need capacity but do not need initial values.

`empty_call_refines` and `oversized_call_refines` cover the early returns. They
prove that the three output fields become zero and that other arrays are
unchanged. They require only the output buffer capacity and the memory relation.

`BodyFrame` proves frame preservation from the actual module's syntax.
`BodyNoException` proves that its body cannot raise an LLVM exception.
`CallBoundary` proves the actual frame and argument operations. Vellvm allocates
an empty varargs struct even for this fixed-arity function. This advances its
provenance counter and changes no memory bytes.

`ModuleCall.permute_module_call` uses the function table obtained from the exact
single-function module. `FullEquivalence.permute_calls_agree` joins the LLVM call
and PR #6's Clight call theorem. Both calls return the same model result and code.
The companion theorems cover empty and oversized calls on both sides.

`FullContract.certified_module` pairs the module AST with these three call
contracts. `FullExport` gives that AST to Vellvm's printer. The package assembles
the printed text, verifies it with LLVM, and compiles it to an object file.
It also compares the compiled object with the generated Clight C on boundary
cases and generated inputs, including every buffer and its guard cells.

Build the module, object, proofs, and check reports with:

```sh
nix build .#verified-permute-llvm
cat result/permute.proved.ll
```

The package contains `permute.proved.ll`, `permute.proved.bc`, and
`permute.proved.o`. The `proof` directory contains the source and compiled proofs.
The theorem refers to the normalized AST that is printed. It does not require
the original Clang output and the normalized AST to have the same semantics.

Run the proof, assumption, kernel, and mutation checks with:

```sh
nix build .#checks.x86_64-linux.llvm-call -L
```

The check retains the existing per-theorem axiom policy. Its mutations change the
actual LLVM argument order, empty-input comparison, return-phi values, and return
operand. The changed modules must parse and normalize before a proof rejects them.
A comment-only control must still pass.

These theorems use Vellvm's infinite-address memory implementation. The nonempty
contract uses typed permutations. It covers the return code and result arrays;
it does not assert equality of scratch buffers or unused trace cells between
Clight and LLVM. Arbitrary malformed destination arrays are outside the contract.

The proof ends at the Vellvm AST. Export relies on Rocq extraction and Vellvm's
printer. The object also relies on LLVM's optimizer, backend, and the target ABI.
The proof checks the AST produced by candidate generation, so it does not assume
that the earlier Clang optimization preserves semantics. Compilation of the
printed LLVM occurs after the proof and remains trusted. Native tests check the
printed object, but do not prove the compiler correct. Proofs for finite machine
addresses and the original C++ implementation remain separate work.
