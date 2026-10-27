# Translation and verification review

Review date: 2026-10-06. This review used four passes over the source: syntax
translation, memory and call contracts, oracle observations, and test/proof
result checks. It is a source review, not a translation theorem.

The reviewed production hashes are:

```text
c03fd138ad37c039a0adfa1470ab3c0711c7d4b83a9b39a25949a44420e33dec  printer.ml
530f90b26b042e59f028dc0f62ec101361e7f81ca78d4c86c2de532386c1807d  Extract.v
c20f4070499460175c14a77c7ba2f00b67b70562572868d5465cd399789127c1  Permute.v
a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78  permute.c
```

## Findings that limit the claim

1. **The Clight-to-C translation remains trusted.** The review found no
   wrong spelling or evaluation order in the accepted subset. Neither
   extraction nor the OCaml printer has a semantic preservation theorem.
   Byte-for-byte regeneration detects a stale C file; it cannot detect an
   error shared by the printer and the regenerated file. GCC/Clang are also
   outside the CompCert compiler theorem used by other CompCert projects.

2. **A proof for every C++ input through length 1024 is still missing.**
   The Rocq theorem relates the Clight call to the Rocq model. The KLEE
   checks relate actual C and C++ bodies for complete small-size domains.
   Neither a small-size symbolic result nor the fuzz corpus extends that
   C++ relation to length 1024. Lengths below 18 cannot reach a blocked swap.
   Thus small-size results cannot establish the two blocked-return paths,
   even when they compare the blocked fields on every execution. The new
   success-if-and-only-if depth condition also needs its own proof.

3. **ISO C object conditions are additional preconditions.**
   `permute_call_correct` starts with separate CompCert blocks at offset
   zero. The C header requires separate, live, writable unsigned array
   objects and excludes concurrent access. A byte permission in CompCert
   does not establish ISO C effective type, array object bounds, lifetime,
   or race freedom. Disjoint slices of one allocation are not covered by
   the current theorem. The source checks widths and alignment, but does
   not automatically reject every platform outside the documented
   x86-64 Linux target.

4. **The universal Clight call theorem assumes a valid permutation.**
   Empty and oversized calls have separate call theorems. Malformed
   permutations have rejection tests; the reviewed call theorem does not
   universally prove this rejection contract. Do not combine these into
   a claim of one proved total C API without a further theorem.

5. **Symbolic runtime models have a narrower scope than the full C++
   environment.** KLEE uses modeled successful allocations with eight-byte
   alignment, and built-in new/delete handling. The successful small runs
   do not enter allocation-failure, exception, large temporary-buffer, or
   unsupported library paths. C++ is compiled with exceptions disabled in
   this KLEE experiment. SAW's experiment links selected actual allocator
   wrapper bodies, then uses its malloc/free model. These choices must
   remain explicit. Neither result proves behavior under out-of-memory
   conditions. The oracle represents `StackSlot` values as unsigned IDs;
   full `StackSlot` construction and its operators are outside the adapter.

6. **Coverage reporting must be tied to build inputs.**
   `guided-coverage.sh` replays an existing coverage executable and selects
   current source paths. It does not check a source-hash manifest against
   the binary's build before it exports or shows coverage. A future source
   edit without a rebuild can therefore label old counter mappings with
   current source text. The archived campaign hashes match the reviewed
   C and printer, so this finding does not invalidate those recorded runs.
   Add a build-input manifest check before using the script for changed
   source. A warning from `llvm-cov` is not such a check.

7. **A new KLEE coverage parser initially counted call summaries.**
   Callgrind rows after `calls=` attribute the whole callee to one call
   site. Counting them as individual instruction coverage made a covered
   count exceed its denominator. This did not affect the equality checks,
   path totals, or error files. The parser now skips call-arc summaries,
   checks the counter layout, and rejects nonboolean instruction coverage.
   Four regression tests include the actual failing record form. Reports
   must be recomputed from raw `run.istats` with the corrected parser.

8. **The first KLEE result gate accepted an early process exit.**
   An actual solc-body copy with `if (m_data[0] == 0U) std::exit(0);`
   passed the length-three comparison for permutation `[1,0,2]`:
   17 completed paths, zero partial paths, and no error files. Four paths
   exited before the result comparisons. Positive function coverage did
   not establish that each path reached the comparisons. The corrected
   harness adds a final symbolic `checks_completed` object after the
   comparison function returns. The result gate checks every KTest for
   the expected input object followed by this marker, and requires one
   witness per completed path. The same mutant is now rejected for four
   missing markers. The unchanged case passes with 13 marked paths.
   The before/after evidence remains under `build/equiv-alive2/klee-exit-probe`
   and `klee-exit-probe-fixed`. This is a verifier-harness defect; it is
   not a found mismatch in the unchanged C implementation.

9. **SAW also accepted a partial symbolic result.**
   The same early-exit pattern was reported proved at length two despite
   a required return value of one. SAW 1.5 retained the surviving result
   and printed `Symbolic simulation completed with side conditions.`
   Its runner now rejects that result marker. The SAW review also found
   and fixed a stale-results case after build failure. See the separate
   [SAW report](../../spikes/clight-permute/tests/equiv-saw/README.md) for
   its source controls and evidence.

10. **Defined Clight execution does not by itself establish C definite
    assignment.** A checked Clight probe with the normal ABI and body
    `v8 = v9; return 0U;` returns zero for all arguments. The initial v9
    holds `Vundef`; `eval_Etempvar` and `exec_Sset` can copy it without
    making the execution stuck. The unchanged printer accepts the AST.
    GCC 15.3 reports that the generated C reads v9 before initialization.
    The printer header delegates initialization to proof obligations, but
    an ordinary Clight call-correctness theorem is not that obligation.
    A separate definite-assignment condition is needed for a general
    translation claim. This probe does not show an uninitialized read in
    the current Permute body. The memory-review agent preserves the probe
    under `build/equiv-saw/undef-probe/`.

    A later [candidate assignment check](../../spikes/clight-permute/tests/initialization/README.md)
    accepts the actual AST and rejects the self-copy prefix. It has a
    checked proofs for control paths and terminating Clight executions.
    Execution records retain real branch choices and intermediate states.
    Memory initialization and the C translation remain separate. The
    concrete link for divergent prefixes is still open. This check is
    not installed in the production pipeline.

## Pass 1: extraction and printer

Read `Extract.v`, `printer.ml`, `print_main.ml`, `test_printer.ml`, and
`build.sh` in full, then compared the accepted forms with the generated C.

`Extract.v` extracts the actual `Permute.permute` value. Decimal integers
use `Int.unsigned`; they are not converted through OCaml machine integers.
An integer literal becomes a decimal value with `U`. With the target's
32-bit unsigned type, addition and subtraction have the same modular
value behavior. Comparison operands remain unsigned and the comparison
result has Clight's signed `int` type, as C requires.

An indexed load or store accepts only a declared pointer of the exact
unsigned element type plus an unsigned index. Its spelling is
`base[index]`. There are no casts, calls, volatile accesses, increments,
or assignments inside expressions. Thus changing C operand evaluation
order cannot change an expression's effects. Evaluation order can still
affect whether an invalid access happens, so the semantic proof and object
contract remain required.

The statement review checked sequencing, both conditional arms, return,
and nested break scope. `Sloop body Sskip` maps to `while (1)`. Other loop
tails and `continue` are rejected. A break in an inner loop does not mark
the outer loop as exiting. The fallthrough check is conservative for the
accepted syntax. The full function is checked and rendered before
`print_main.ml` writes it. This prevents an unsupported later statement
from producing a partial accepted C file.

Parameter and temporary identifiers must be unique. Types, qualifiers,
alignment attributes, local-storage declarations, and calling convention
must match the allowed forms. The output function name and header are
fixed. The range proof inside an extracted integer is erased; the printer
entry point therefore depends on receiving the extracted Rocq AST, not
arbitrary externally constructed OCaml values.

No translation defect was found in these lines. The rejection tests do
not prove that every accepted AST has a corresponding defined ISO C
execution; they test the syntax boundary.

## Pass 2: calls, memory, and undefined behavior

Read the final `permute_call_correct` statement, the entry and call
composition, the array predicates, and the public header contract.

The full theorem constructs an actual `eval_funcall` result. Defined
execution is a conclusion, not an assumed successful execution. Only
data and permutation need initialized input contents. The output and
scratch capacities are writable; the proof derives the writes needed
before subsequent reads. The theorem returns the model result, memory
relation, result specification, and a return code restricted to zero or
one. The statement is existential execution; the accepted subset has no
external calls or assembly that can introduce differing external results.

Unsigned arithmetic and separately sequenced scalar assignments avoid
signed arithmetic and unsequenced side effects in the generated C.
Pointer bounds, initialized loads, and trace capacity still need proof.
The public header correctly requires `out` even for size rejection,
because its three stores occur before the size checks. Other buffers may
be null for the two early size-return cases.

No `restrict`, type punning, packed objects, pointer-integer conversion,
pointer ordering, or cross-object pointer subtraction occurs in this
subset. The retained contract excludes byte-buffer and overlapping-slice
uses that would need a different C/proof relation.

## Pass 3: observed behavior and source identity

Read the C fuzz checker, byte-input decoder, upstream preparation code,
C++ adapter, KLEE wrapper, and SAW miter/specification.

The comparison covers status, complete final or partial data, trace
length, every written trace element, blocked offset, and excess depth.
The scratch permutation/target/used arrays are omitted because the public
contract makes their returned contents unspecified. The original input
permutation is preserved separately for the oracle. Trace suffixes are
not read. The fuzz checker also replays the trace and checks desired
values on success.

The hash-checked upstream preparation copies the selected actual
`Emission::permute` and reached helper bodies. The adapter supplies
storage and value IDs. It does not replace sorting or duplicate handling
with a second hand-written implementation. KLEE executes the reached
vector and range-v3 template bodies. No proof of their behavior can be
inferred from an unresolved call declaration; all reached calls must
have a supported implementation or an explicit runtime model.

The symbolic inputs contain unrestricted 32-bit values. Each concrete
permutation case is valid by construction; the union of all cases gives
all valid permutations at that length. There is no assumption of distinct
data values. Error and equivalent mutations use the same observation
checks. Mutant source paths and hashes must remain separate from the
hashes of the unmodified source.

## Pass 4: result meaning and loss of paths

The LLVM coverage report keeps the three C defensive outcomes and the C++
assertion failure in its denominators. It reports `72/76` standard LLVM
outcomes and `72/84` exported outcomes. The latter includes constant-loop
alternatives. The claim that all 72 reachable outcomes were covered is a
measured result plus a separate reachability argument; it is not raw
100% coverage. Helpers, adapters, and library code are outside these two
source totals. Fuzzer bitmap coverage and KLEE instruction coverage are
different measures.

The KLEE runner requires a nonzero completed-path count, zero partial
paths, no error files, no reported execution error, and execution of both
implementation functions. It sets `--external-calls=none` and also rejects
logged concrete external calls. A timeout or killed state does not pass.
The run uses `-O0`, active assertions, memory checks, and signed overflow,
shift, division, and array-bound instrumentation. Negative mutations
produce both pointer-error and signed-overflow reports. No loop-unroll
cutoff is used. Allocation and LLVM-model limits still apply.

The SAW specification requires the comparison function to return one for
all fresh input values. This return condition alone did not reject a
partial result after symbolic early exit; the runner now also rejects
SAW's side-condition marker, as described above. It does not assume the
desired result. Its
specification reads the entire input array and leaves memory checks
enabled. Its current core uses `-O1`; there is no explicit signed-overflow
instrumentation in that runner. Do not turn its LLVM result into a claim
about every form of ISO C undefined behavior without reviewing compiler
and LLVM poison handling.

The Alive2 trial is inconclusive. Some unsupported wrapper metadata can
be avoided, but surviving recursive C++ helper calls are not equivalent
to verifying their bodies. An accepted intraprocedural result with those
calls abstracted would not prove the required C-to-C++ relation.

Fil-C and sanitizer results remain execution tests. Fil-C's negative
controls found that a one-word overrun can stay inside allocator rounding;
the report retains that limit. MSan retries are restricted to its exact
pre-main shadow-mapping failure signature and retain failed logs. A real
uninitialized-read report is not accepted as a retryable startup failure.

## Work needed for the full requested domain

A scalable relation must connect the C target/used scans with solc's
stable sorting and set operations for duplicate groups. It must then
relate the two loop states, including partial data, mapping state, trace,
and both blocked-return sites. Required library contracts include vector
allocation and lifetime, stable sorting, set difference/intersection,
and the reached stack/mapping operations. Those contracts must be proved
or stated as additional trust, not silently substituted.

Loop invariants can avoid enumerating `1024!` permutations and all value
order/equality classes. Termination and resource bounds must also be
proved if an invariant tool supplies only partial correctness. A small
completed symbolic run, mutation score, or observed coverage percentage
does not replace these obligations.
