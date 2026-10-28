# Clight to printed LLVM

This work starts from PR #6 (`8756da64fcd6e21a1b89ae519e43636ceadbeb6b`).
It uses `spikes/clight-permute/Permute.v` and its C printer from this checkout.
There is no second copy of the shuffler repository in the Nix inputs.

Build and run the checks:

```sh
nix build .#verified-llvm
cat result/depth.proved.ll
```

The full `permute` call has a separate package:

```sh
nix build .#verified-permute-llvm
cat result/permute.proved.ll
```

See [the full-call proof and export](full/README.md) for its memory conditions,
observed results, and remaining finite-address and Lean-model limits.

For local work:

```sh
nix develop .#verified-llvm
sh verification/llvm/build.sh
```

The package contains the generated C, Clang's LLVM candidate, the imported Rocq
term, the theorem's assumption report, Rocq proof objects and source under
`proof/`, and the printed LLVM in text, bitcode, and object form.
**Use `depth.proved.ll`, `depth.proved.bc`, or
`depth.proved.o`.** The original `depth.ll` is only a candidate.

## First statement

`ClightDepth.v` places the unsigned subtraction from `Permute.exchange` in a
function with two unsigned 32-bit parameters. It uses PR #6's `u32`, `reg`,
`sub`, `top`, and `pos` definitions. This first function has no memory accesses.

`Equivalence.depth_equivalence` proves, for every pair of CompCert `Int.int`
values and every Clight global environment and memory:

- The complete Clight call terminates with `Int.sub x y`, no output events,
  and the same memory.
- The complete Vellvm interpreter call, including module initialization,
  function entry, and return, is equal up to silent steps (`eutt eq`) to a
  pure return of the same unsigned 32-bit value.

The integer relation maps `Int.unsigned x` to Vellvm's 32-bit `repr`.
Subtraction wraps modulo 2^32. There is no `x >= y` premise.

The Vellvm call uses `ParamsV IPZ IPZTheory` and the default initial interpreter
state. The comparison observes its return value and events. It hides the
private final interpreter state. The finite `pure_result` check is used to
construct a proof for **all inputs**; it is not a set of sample executions.
`pure_result_sound` proves that a successful check implies `eutt` to `Ret`.
It rejects visible events, including undefined behavior and failure.

This is not a proof of `swap_cells`, `permute`, arbitrary caller memory, or
the Lean-to-Rocq model relation. It is not a bisimulation between the full
Clight and LLVM machine states. The [full-call proof](full/README.md) adds memory,
control flow, argument binding, frame operations, and a printed `permute` module.

## Build path

1. Check the vendored CompCert subset and compile the Clight function proof.
2. Extract the Clight AST and print C with PR #6's statement printer.
3. Compile the C with the pinned Clang 20 at `-O2`.
4. Parse the LLVM with the pinned Vellvm frontend and import its Rocq term.
5. Construct a restricted LLVM module with `Normalize.normalize`.
6. Check the complete Vellvm call against the Clight function.
7. Print the AST in `certified_module` with Vellvm's `ShowAST.showProg`.
8. Verify and compile that printed LLVM with LLVM tools.

The importer repairs three defects in the pinned Rocq-term exporter: quote
escaping, `LOC_Armem`, and `ANN_tail tail`. These repairs are part of candidate
generation. Its token check excludes Rocq command terminators and tactic
escapes from the imported term.

The normalizer accepts one scalar function with two `i32` arguments, one
unflagged `add` or `sub`, and a return of a local value. It preserves names,
operands, the operation, the return operand, target, and data layout. It drops
source locations and a listed set of function/parameter annotations. It drops
detached metadata and module flags when constructing the new module. Other
instruction metadata is rejected. Calls, memory operations, declarations,
globals, non-default calling conventions, and other shapes are rejected.

**There is no claim that normalization preserves the input module's behavior.**
The proof checks the resulting module directly. For example, `add` is accepted
by the syntax filter but fails the subtraction proof. The final printed module
has no `noundef`, attribute groups, or semantic metadata.

## Trust boundary

The generated C, C printer, Clang optimization, input parser, import repairs,
and normalization construct a candidate. Their semantic correctness is not
assumed by the final theorem.

The foundations still include Rocq's kernel, the reported logical axioms,
CompCert's Clight semantics, Vellvm's semantics, and the chosen observation and
state relation. PR #6's model theorem and its remaining Lean link are separate.
The build applies PR #6's existing assumption policy to the new theorem.
The report lists classical logic, dependent functional extensionality, two
classical-real decision axioms, and CompCert's abstract external-function and
inline-assembly semantics. The scalar function makes no external calls.

The output path trusts Vellvm's LLVM printer, Rocq extraction, and the OCaml
compiler/runtime used to run it. `Export.v` applies that printer to the exact
AST in the proof-bearing `certified_module`; it does not print the earlier
OCaml parser value. LLVM's backend and the target ABI remain trusted when
using the native object.

The LLVM verifier and native tests check the export path, but do not prove
printer fidelity or native code equivalence. A round-trip through the same
input parser would not establish that either.

## Checks

The build checks the Rocq theorem and the printed LLVM. Native tests include
unsigned boundaries and reproducible random inputs. Negative tests feed
modified LLVM through the production parser and importer. Addition and a
changed return operand must fail the semantic proof. Multiplication, a changed
calling convention, and an external declaration must fail normalization.
Importer tests cover missing markers, malformed terms, quote repairs, and
attempted Rocq command injection.
