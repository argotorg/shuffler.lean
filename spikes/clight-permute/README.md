# Clight Permute prototype

For review, start with the [public contract and core definitions](../../docs/verified-permute/README.md)
and the [trust boundary](../../docs/verified-permute/trust-boundary.md).
The readable theorem is `PermuteCorrect.clight_refines_model`; its named
predicates are in `PermuteSpec.v`, and the model postcondition is in
`ModelSpec.v`. Proof scripts are separate from these specification definitions.

This directory constructs a Clight implementation of Permute in Rocq and
prints it as C11. The complete Clight call has a proof of defined execution
and refinement of the duplicate-aware Rocq model for valid permutations
of length one through 1024. The generated C also matches the pinned solc
Permute operation in differential tests, including duplicate values.
The C printer and compilation with GCC or Clang remain trusted steps.

The new development uses GPL-3.0-or-later. Its copied CompCert sources use
the explicit LGPL-2.1-or-later alternative. No CompCert compiler pass,
driver, parser, `clightgen`, or non-commercial source is needed. See
[LICENSING.md](LICENSING.md) for the source allowlist and dependency terms.

## Build and run

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
sh spikes/clight-permute/check-proofs.sh
sh spikes/clight-permute/tests/matrix.sh
```

The shell reads `flake.lock` directly. It avoids the worktree `getFlake`
hash error. `check-proofs.sh` audits dependencies, compiles the actual
Clight AST, extracts it, tests the printer, checks that regenerated C
matches `permute.c`, compiles the proof modules, and runs `coqchk`.
Build files stay under `build/`. The assumptions of the checked theorems
are written to `build/proof-assumptions.txt`.

For only the AST, extraction, and printer checks, run `sh
spikes/clight-permute/build.sh`. This shorter command does not check the
model or memory proofs.

Compile the generated file with an ordinary compiler:

```sh
gcc -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
  -O2 -c spikes/clight-permute/permute.c -o /tmp/permute.o
```

The test matrix uses GCC and Clang at `-O2`, at `-O3`, and with address and
undefined-behavior sanitizers. In this execution environment LeakSanitizer
cannot start. `ASAN_OPTIONS=detect_leaks=0 sh
spikes/clight-permute/tests/matrix.sh` disables only the leak check; address
and undefined-behavior checks remain active. Use that setting only for an
unsupported LeakSanitizer runtime, not for an actual leak report.

## C interface

The prototype targets x86-64 Linux with the normal system ABI. Its header
is [permute.h](permute.h):

```c
unsigned int permute(unsigned int n, unsigned int *data,
    unsigned int *permutation, unsigned int *target, unsigned int *used,
    unsigned int *trace, unsigned int *out);
```

`data` is ordered from the bottom of the stack to the top. Input
`permutation[i]` is the desired destination of the value at source index
`i`. For `0 < n <= 1024`, each of `data`, `permutation`, `target`, and
`used` has at least `n` unsigned elements. `trace` has at least `2*n`
elements. `data` and `permutation` are initialized inputs. The other
arrays are work or output space. `out` always has at least three elements.

Use separate live unsigned array objects and pass pointers to their first
elements. The memory lemmas represent each array by a separate CompCert
block at offset zero. They do not establish a contract for disjoint slices
of one larger allocation. No other thread, signal handler, or callback may
access the arrays during the call. The implementation cannot check these
pointer, object, capacity, or concurrency preconditions.

| Return value | Meaning |
| --- | --- |
| `0` | Success; `data[permutation_input[i]]` equals `data_input[i]` |
| `1` | A required swap exceeds depth 16 |
| `2` | Invalid size or permutation, or a defensive internal check failed |

`out[0]` is the trace length. `out[1]` is the blocked position and `out[2]`
is the excess depth. The last two fields are zero unless the return value
is one. Trace elements are depths from one through sixteen. Only the
written prefix of the trace may be read. On a blocked return, `data` and
`trace` describe the swaps completed before the error. The other work
arrays have unspecified output contents.

For `n == 0`, the function succeeds without reading the other arrays.
For `n > 1024`, it rejects the input before reading them. Those five other
pointers may be null in these cases; `out` must still be valid. Rejection
of an input permutation leaves `data` and `permutation` unchanged.

## Algorithm and source

[Permute.v](Permute.v) contains the actual Clight objects. There is no C
parser. The implementation first checks the input permutation and builds
the desired value array. It fixes positions that already contain a correct
value. It then pairs each remaining source position with the first free
destination that requires that value. Both scans are in ascending order.
This implements solc's pairing of equal-value groups without sorting or
allocating storage. Normalization takes quadratic time in the worst case.

The swap loop follows the top value's destination. When the top is fixed,
it selects the largest misplaced position. Equal values exchange only
their destinations; they emit no physical swap and do not fail the depth
check. Other exchanges emit a swap at depth at most sixteen or return a
blocked result.

[printer.ml](printer.ml) accepts only the types and syntax needed here:
unsigned scalars, pointers to unsigned arrays, pure expressions, indexed
loads and stores, unsigned addition and subtraction, comparisons, `if`,
a restricted loop, `break`, and return. It rejects other forms before
writing output. It adds target checks but no algorithm logic. See
[PRINTER_REVIEW.md](PRINTER_REVIEW.md) for the translation review and
[the memory review](../../docs/verified-permute/c-semantics-review.md) for
the restrictions needed when GCC or Clang compiles the output.

## Proof status

The model adds duplicate normalization and suppression of equal-value
swaps. The earlier Lean and Rocq models did not include these solc rules.
This is a specification change; no cross-prover equivalence to the current
Lean implementation is claimed.

The model proofs establish that normalization produces a permutation with
the required values, preserves correct positions, and agrees with the
finite-function form of the greedy array writes. The duplicate-aware loop
has a decreasing rank. Its theorems cover termination, successful output,
legal swap traces, a `2*n` trace bound, and the state and excess depth on a
blocked result. These are proofs about the mathematical model.

The Clight development uses actual CompCert memory and upstream Clight
big-step semantics. In [ClightCorrect.v](ClightCorrect.v),
`permute_call_correct` proves a complete function-call execution, including
parameter binding, return conversion, and cleanup. It gives the same
result as `SolcModel.solc_permute` and connects memory to the model's final or blocked
data, permutation, trace, and three output fields. It also supplies the
model's result specification. The theorem proves that an execution exists;
it does not assume that the implementation first executes successfully.
The relation to the C++ solc implementation is tested, not proved.

The full `check-proofs.sh` run passed on 2026-10-06, including regeneration
of the C file and `coqchk` on all project, legacy, and allowed CompCert
modules. The assumption report is in `build/proof-assumptions.txt`.

Its preconditions are a valid finite permutation, `1 <= n <= 1024`, data
values from zero through `UINT_MAX`, and the separate writable array
objects and capacities specified above. Only `data` and `permutation`
need initialized contents on entry. Validation initializes the target
array; normalization initializes its work array. The theorem covers both
success and a blocked swap. A valid input cannot return the defensive
error code two.

In [ClightCall.v](ClightCall.v), `permute_empty_call` and
`permute_oversized_call` prove the other size cases with only writable
`out` storage required. Rejection of a malformed input permutation is
tested, but has no universal proof in this development. The ISO C typed
object, effective type, and pointer-bound obligations remain part of the
reviewed C contract; a Clight memory proof alone does not establish them.

## Differential tests and trusted parts

[tests/fuzz.c](tests/fuzz.c) is the small C fuzz driver. The C++ adapter runs
the actual pinned upstream solc Permute body and its reached stack helpers.
A preparation step checks full source hashes before copying these bodies
without changes. The adapter uses unsigned value IDs and swap-depth trace
storage. It does not build the full solc compiler. See
[tests/README.md](tests/README.md) for its precise boundary.

GCC 15.3.0 and Clang 21.1.8 passed all six compiler configurations. Each ran
4,435 exhaustive cases, 20,000 random cases with seed 2654435769, and
boundary and invalid-input cases. The tests compare return codes, the full
trace, error fields, and final or partial data. They also replay the trace
and check final values against the input permutation. The random cases
are the same inputs across compiler configurations, not 120,000 distinct
inputs.

The trust boundary includes the Rocq kernel and used axioms, extraction,
the OCaml toolchain, the printer, the C subset and ABI contract, GCC or
Clang, and the execution platform. The checked Clight semantics does not
make GCC or Clang a verified compiler. CompCert's compiler-correctness
theorem is not used. The source and license audit is a separate check.
