# Printer review

Review date: 2026-10-06. Scope: `printer.ml`, `Extract.v`, `Permute.v`,
`print_main.ml`, and the generated `permute.c`. The C language contract is
in [the memory-model review](../../docs/verified-permute/c-semantics-review.md).
This is a source review and a set of tests. It is not a proved translation
from Clight to ISO C.

## Findings

The admitted expressions and statements have the intended C spelling.
The review found no mismatch in that translation. The printer checks
types, attributes, declarations, and control-flow forms before it returns
any output. It does not check index bounds, object validity, initialized
values, or termination. The program proof and caller contract must supply
those properties.

`Permute.v` constructs the actual Clight function. `Extract.v` extracts
that function, its three supported types, and decimal formatting functions.
`print_main.ml` passes that extracted function directly to the printer.
There is no second C algorithm or C template. The generated C file is
checked byte for byte against a fresh extraction by `build.sh`.

## Accepted forms

| Clight form | Printed C and reason |
| --- | --- |
| `Tint I32 Unsigned noattr` | `unsigned int`; the preamble checks its width and alignment |
| Pointer to that type, with no attributes | `unsigned int *`; the ABI has six such parameters |
| Unsigned `Econst_int` | Decimal `Int.unsigned` value with `U`; formatting keeps Rocq integers |
| Declared unsigned `Etempvar` | An injective name `v` followed by the positive identifier's decimal value |
| Unsigned addition and subtraction | Fully parenthesized expressions; both languages use modulo 2^32 arithmetic |
| Unsigned equality, inequality, `<`, `>`, `>=` | Parenthesized conditions with Clight's signed `int` result type |
| `Ederef (base + index)` | `base[index]`; base is a declared pointer and index is an unsigned expression |
| `Sset` and indexed `Sassign` | A separate assignment statement; declared and expression types must match |
| `Ssequence` and `Sskip` | Statements in order; skip emits no statement |
| `Sifthenelse` | Braced `if` and `else` blocks |
| `Sloop body Sskip` | `while (1)`; the constant condition also preserves possible nontermination under ISO C's loop rule |
| `Sbreak` | `break`, accepted only inside a loop |
| `Sreturn (Some value)` | Return of an unsigned expression |

The function has one unsigned size parameter, six pointer parameters,
unsigned temporaries, no addressable locals, and the default calling
convention. Identifiers are unique across parameters and temporaries.
The external function name is fixed to `permute`, matching `permute.h`.
The printer handles a function rather than a complete Clight program;
it does not emit globals, composites, external definitions, or startup code.

No expression has an effect. This avoids a difference in C operand order.
Every load and store uses the declared unsigned element type. Type
attributes, including attributes nested inside pointer types, must match
the exact supported types. No qualifier or cast is silently discarded.
The expression printer never emits signed arithmetic, pointer casts,
pointer ordering, shifts, calls, or pointer subtraction.

The loop printer rejects a second loop body and `continue`. The traversal
checks the scope of every break, including unreachable statements. The
fallthrough check tracks breaks in the current loop and ignores breaks
inside nested loops. It rejects a possible normal path out of the end of
the nonvoid function. It does not require a return from an infinite loop.

The printer accepts only values represented by the extracted Rocq types.
Rocq's `Int.int` range proof is erased during extraction. This interface
does not accept externally supplied OCaml values that forge that erased
representation. A future parser or external AST input would require a new
checked boundary.

## Program-specific obligations

The first three stores initialize `out`. Thus `out` must be valid even
when the size is rejected. The size checks then return before any other
buffer access for zero or oversized inputs.

For a nonempty accepted size, permutation validation precedes each use of
an input destination as an index. Distinct in-range destinations must also
establish that every `target` element has been written before normalization
reads it. The normalization proof must show that its result is a valid
permutation and that its free-destination search succeeds. These are
semantic obligations; they do not follow from the printer checks.

The permutation invariant must bound the selected position. The countdown
checks for zero before subtraction. A swap must establish `pos <= top`
before computing its depth. The trace store has a runtime capacity check;
the model proof must show that valid inputs never reach this defensive
error. Equal values skip both the depth check and the physical swap, as
the upstream solc method requires.

The buffers must remain separate, live unsigned arrays with the stated
capacities. The proof must establish valid pointer formation as well as
valid loads and stores. CompCert's byte-level permission checks alone do
not establish ISO C effective types or all C array-bound restrictions.

## Tests and trust boundary

`test_printer.ml` checks literal formatting, precedence, array indices,
identifier names, statement order, and loop output. Rejection tests cover
excluded expression and statement constructors, operators, wrong type
annotations, invalid store forms, unsupported conditions, declaration
changes, parameter and temporary collisions, nested pointer attributes,
calling conventions, loop scope, and normal fallthrough paths.

The generated core passed differential tests under GCC 15.3.0 and Clang
21.1.8 at `-O2`, at `-O3`, and with address and undefined-behavior sanitizers.
These runs exercised 4,435 exhaustive input cases and 20,000 random cases
per configuration, plus boundary and invalid-input tests. They do not prove
the translation or the absence of undefined behavior.

The remaining trusted parts include the Rocq kernel and used axioms,
extraction, the OCaml compiler/runtime, this printer, the ABI and subset
contract, the C compiler, and the execution platform. GCC and Clang are not
covered by CompCert's compiler-correctness theorem. Licensing and source
allowlists are checked separately in [LICENSING.md](LICENSING.md).
