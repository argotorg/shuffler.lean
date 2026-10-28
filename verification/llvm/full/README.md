# Full-call proofs and LLVM export

`FullEquivalence` proves agreement of complete Clight and LLVM calls to
`permute`. It covers nonempty valid permutations of at most 1024 positions,
empty input, and oversized input. The nonempty result includes the same model
result, return code, data, permutation, trace prefix, and three output fields.
This uses PR #6's Clight-to-Rocq-model theorem. The Lean-to-Rocq model relation
remains separate.

Build the proof checks and printed module:

```sh
nix build .#verified-permute-llvm
cat result/permute.proved.ll
```

Use `permute.proved.ll`, `permute.proved.bc`, or `permute.proved.o`.
`permute.ll` is the Clang candidate before the syntax transformation and proof.
The package also contains proof sources and objects, assumption reports,
mutation results, and native export test results.

This directory contains the memory and control-flow proofs for the full call:

- `MemoryRelation.v` proves four-byte reads and writes using Vellvm's actual
  memory handler. The proofs check allocation and provenance for each byte.
  Stores preserve all bytes outside the destination, allocation IDs, the
  frame stack, the heap, and the provenance counter.
- `WordMemory.v` maps a CompCert `Int.int` to four bytes with Vellvm's integer
  serializer. The upstream integer round-trip theorem proves the load
  result. Scratch storage requires allocated bytes with access permission;
  its initial contents need not be defined integers.
- `CellRelation.v` maps each Clight block to a flat LLVM address, a provenance
  token, and a number of 32-bit cells. The layout type requires non-overlapping
  blocks. `related_store` proves that the actual CompCert and Vellvm stores
  preserve this relation for every mapped cell. `related_load` proves that
  related initialized cells give the same integer value.
- `MemoryTests.v` evaluates the production handler. It checks unsigned
  boundaries, unaligned and adjacent cells, unallocated memory, invalid
  provenance, and a read that crosses the allocation boundary.
- `Control.v` connects finite paths and path prefixes to Vellvm's actual
  control-flow, call, and state interpreters. `Instructions.v` proves rules
  for the instructions and phi nodes used in the first blocks.
- `Entry.v` proves the three output stores and the size branch of the actual
  imported entry block. These stores preserve the Clight-to-LLVM cell relation.
- `Initialize.v` proves every iteration of the actual used-array initialization
  loop for sizes 1 through 1024. It matches each write with a CompCert store,
  proves that the array contains zeros, and preserves other mapped cells and
  unrelated local values. Scratch cells need not contain defined integers.
- `Prefix.v` joins the entry block, the nonempty-input branch, the preheader,
  and the initialization loop. `initialized_prefix_semantics` states equality
  up to silent steps under the actual Vellvm interpreters. Execution continues
  at the first validation preheader in a state related to the CompCert memory.
- `ValidationBlocks.v` proves the range check, unused-cell check, and writes
  in the validation loop. `Validation.v` proves all iterations using
  `ClightValidation.validation_memory` from PR #6. It preserves the relation
  after the actual CompCert and LLVM stores and proves the target values.
- `CheckedPrefix.v` joins initialization and validation. Its semantic theorem
  starts at the actual entry block and continues at the first normalization
  preheader. It assumes a permutation with distinct destinations in range,
  as required by PR #6's valid-call contract.
- `FixedBlocks.v` proves the comparison, conditional destination store, and
  flag store in the first normalization loop. `Fixed.v` proves all iterations
  for sizes 1 through 1024. Its final destination and flag arrays match
  `ClightNormalize.fixed_pass_correct` from PR #6. It preserves other arrays
  and local values outside the loop's writes.
- `FixedPrefix.v` joins entry, initialization, validation, and the first
  normalization pass. It uses PR #6's `target_array_from_destinations` to
  derive the target array from the input permutation. Only the input data
  and permutation need initialized contents.
- `SearchBlocks.v` and `Search.v` prove the inner search in the second pass.
  Given a first matching unused target, the search reaches the assignment
  block with that target's index and preserves memory. `SearchModel.v`
  connects that result to the model's `first_free` choice.
- `FillBlocks.v` and `Fill.v` prove the second pass's comparison, search,
  assignment stores, and increment. `FillLoop.v` proves all outer-loop
  iterations. Its final permutation array matches PR #6's `raw_fill` result.
- `NormalizedPrefix.v` joins entry, initialization, validation, and both
  normalization passes. `raw_normalize_complete` supplies the successful
  search choices and connects the final array to `SolcModel.normalize`.
  The theorem starts with only the data and permutation contents defined.
  It ends at the main-loop preheader.
- `MainSetup.v` and `MainPrefix.v` establish the main-loop registers and the
  same array invariant used by the Clight proof. `ChooseBlocks.v`,
  `ChooseScan.v`, `Choose.v`, and `ChoosePermutation.v` connect the actual
  descending LLVM scan to the permutation model's `choose` function.
- `ExchangeBlocks.v` proves the value comparison, depth test, capacity test,
  blocked output stores, and permutation swap. `ExchangeData.v` proves the
  data swap, trace append, and count update. `ExchangePermutation.v`,
  `ExchangeSuccess.v`, and `ExchangeBlocked.v` derive these effects from the
  memory relation and arrays, without load-success or store-success premises.
- `Cleanup.v` covers all eight return-phi predecessors. `EarlyExit.v` proves
  the complete body paths for empty and oversized input, including output
  initialization and preservation of other arrays.
- `MainInvariant.v` preserves the main-loop registers across position choice.
  `MainLoopCore.v` proves the rank induction with explicit branch contracts.
  `MainLoop.v` supplies those contracts from the actual exchange proofs.
- `MainBody.v` joins the entry prefix, normalization, main loop, and return.
  `permute_body_refines` proves execution of the complete `denote_cfg` body
  and the exact `solc_permute` result, including partial data and trace when
  a swap depth exceeds 16. It also preserves the cell relation and arrays
  outside the six argument buffers.
- `BodyEquivalence.v` connects that LLVM body theorem to PR #6's complete
  Clight call theorem. Both executions produce the same return word and model
  result, encoded in their respective memories. The LLVM side of this theorem
  still starts after argument binding.
- `BodySyntax.v`, `BodyFrame.v`, and `BodyNoException.v` prove that the actual
  body preserves the call frame and cannot raise an LLVM exception.
  `NoException.v` connects this property to the exception interpreter.
- `CallBoundary.v` proves argument binding, the empty varargs allocation,
  frame pushes, and frame pops. `FullCall.v` joins these operations to the
  complete body proof, starting from the input memory and caller state.
- `ModuleCall.v` connects the call to the function table built from the exact
  module. `FullEquivalence.v` joins this LLVM call to the Clight call and
  proves equal results. `FullContract.v` packages all three call statements,
  the single-function shape, and the `permute` symbol with that module AST.
- `FullExport.v` prints the AST from this proof-bearing package with Vellvm's
  printer. `export.sh` compiles the extracted printer, verifies the emitted
  LLVM, and compiles it to a native object.

These proofs use `ParamsV IPZ IPZTheory`, with infinite integer addresses.
A proof for a finite machine address space remains open. The module call uses
the function table and initial memory supplied by the caller; it does not
prove a separate module-loader implementation. The complete-call theorem
includes argument binding and call-frame allocation and removal.

The final memory comparison observes the data array, permutation array,
written trace prefix, and output fields. It does not prove equality of scratch
buffers or unused trace cells between the final Clight and LLVM memories.
The LLVM theorem separately preserves arrays outside the six argument buffers.
Malformed destination arrays are outside the typed-permutation contract.

`memory_steps` is a proof relation for finite successful memory effects.
`memory_steps_sound` connects it to the actual Vellvm handler; it does not
replace that handler in the statement or in the tests.

Run the independent kernel check and PR #6's existing assumption policy:

```sh
nix build .#checks.x86_64-linux.llvm-memory
```

Check the imported entry and initialization proofs:

```sh
nix build .#checks.x86_64-linux.llvm-prefix
```

This check recompiles the generated C with Clang, imports the LLVM AST, and
checks the proofs and assumptions. It also changes the actual LLVM source,
parses and imports each variant, and requires proof rejection. The mutations
change an output store, the size limit, the loop store, the initial phi value,
and the loop increment. A comment-only change must still pass. These tests
check the production import and proof path; they do not use a copied AST.

Check the path from entry through validation:

```sh
nix build .#checks.x86_64-linux.llvm-validation
```

This adds the unchanged Clight invariant sources from PR #6 and checks the
combined semantic theorem. Extra mutations change the range comparison,
the used-cell marker, the data load, and the target-store address.

The theorem assumption check uses PR #6's policy without changes. The memory
theorems use at most its four classical logic and extensionality axioms. The
load proof uses the integer round-trip theorem; the more general aggregate
theorem adds `Eq_rect_eq` and fails that policy.

Check the first normalization pass and its composition with the entry prefix:

```sh
nix build .#checks.x86_64-linux.llvm-fixed
```

This adds the unchanged Clight and model proof dependencies from PR #6.
Six mutations change the comparison, destination store, flag phi, initial
index, index increment, and trip count. Each mutated LLVM program must pass
LLVM verification, parsing, and normalization, then fail the affected proof.
A comment-only control must still pass. The separate `llvm-validation`
check covers the earlier blocks' mutations.
Four more mutations check the search flag test, value comparison, increment,
and result check. A timeout fails the test and retains the proof-step log.

Check both normalization passes and the combined path from entry:

```sh
nix build .#checks.x86_64-linux.llvm-normalization
```

This check adds the second pass, the model's successful normalization result,
and the combined semantic theorem. Mutations change the output-field address,
second-pass comparison, assignment, used flag, initial index, increment,
and trip count. The separate `llvm-fixed` check covers the first pass and
inner search. Each check includes a comment-only control.

Check the main-loop setup and position choice:

```sh
nix build .#checks.x86_64-linux.llvm-choice
```

This adds the model's position choice and mutations of the top index, trace
capacity, comparisons, phi input, scan decrement, and stopping condition.
Eleven mutations must pass normalization, then fail the affected proof. They
include an AND with a changed operand. A twelfth mutation changes AND to OR
and must fail normalization. A comment-only control must still pass.

Check the complete body:

```sh
nix build .#checks.x86_64-linux.llvm-main
```

This checks every body proof, the theorem assumption policy, and the kernel
context. Fifteen mutations change the exchange phi, value comparison, depth
calculation and limit, blocked output fields, trace capacity test, both data
stores, trace index and value, count increment, both permutation stores, and
blocked return code. Each changed LLVM program is verified, parsed, and
imported again before its affected block proof must fail. The comment-only
control recompiles the exchange and return blocks and their dependencies.

Check the complete call and export:

```sh
nix build .#checks.x86_64-linux.llvm-call
```

This adds the call-boundary, full-equivalence, and export contracts to the
assumption and kernel checks. Six mutations change argument order, the empty
comparison, three return-phi values, and the return operand. Native export
tests compare the printed LLVM object with the generated Clight C on 996
cases. They compare all six buffers, both buffer guards, unused trace cells,
and all return branches. A modified printed return instruction must fail the
native comparison. These tests cover more final memory than the theorem does;
they do not extend its formal statement. See [CALL.md](CALL.md) for the call
conditions.

The independent kernel check reports the entire imported environment, including
unused library axioms. `kernel-axioms.txt` records the 14 names in the Vellvm,
ITree, Stdlib, and CompCert imports. This is a separate context check, since
PR #6's kernel context covers only its own dependencies. Both added axioms and
unsafe typing settings fail this check. The per-theorem policy still rejects
these extra context axioms if a project theorem depends on them.

The validation check also imports Clight execution libraries. Its import-only
baseline has the same 14 axioms plus CompCert's four external-function and
inline-assembly declarations. `kernel-axioms-clight.txt` records those 18 names.
The theorem assumption policy remains PR #6's unchanged policy.

The output path trusts Rocq extraction, the OCaml compiler and runtime, and
Vellvm's LLVM printer. The native object also trusts LLVM's optimizer, backend,
and the target ABI. LLVM verification and native tests do not prove those
components correct. The candidate C printer, Clang optimization before the AST
proof, parser, importer, and syntax transformation are not trusted for semantic
preservation. The proof checks their resulting AST directly. Compilation of
the printed LLVM occurs after this proof and remains trusted.

Prepare the full Clang candidate:

```sh
nix develop .#full-llvm -c sh verification/llvm/full/prepare.sh
```

This compiles PR #6's generated `permute.c` at `-O1`, imports the full Vellvm
AST, and checks a restricted syntax transformation. The input uses no runtime
calls, allocation instructions, or vector instructions. The transformation
preserves operands and control flow. It removes arithmetic and conversion
constraints, parameter and function attributes, and metadata. It sets loads
and stores to `align 1`. It accepts only the specified x86-64 target and data
layout. Tests reject calls, allocation, volatile and atomic stores, poison
operands, other store widths, an external declaration, and a different target
or data layout.

`candidate/FullProgram.v` proves only that this syntax transformation succeeds.
It makes no equivalence claim. The preparation step creates no printed module.
`FullContract.full_module_equivalence` checks the complete-call contract for
that exact AST. Only then does `FullExport.v` print it.
