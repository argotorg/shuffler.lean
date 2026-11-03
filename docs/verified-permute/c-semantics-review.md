# Clight to C: memory and language review

Review date: 2026-10-06. CompCert source:
[`7e980792eeabe20285cabace5a5bd93fcc3c01d7`](https://github.com/AbsInt/CompCert/tree/7e980792eeabe20285cabace5a5bd93fcc3c01d7).
The review uses the original Rocq Clight semantics. It does not use the Lean
translation, a C parser, or a compiler pass. The C reference is the public
[C11 draft N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

The planned build uses CompCert 3.17, pinned at
[`7b1f02b09954b9b916eb2a91d283c9b5355bf172`](https://github.com/AbsInt/CompCert/tree/7b1f02b09954b9b916eb2a91d283c9b5355bf172).
I also compared its `Clight.v`, `Cop.v`, `Ctypes.v`, `Memory.v`,
`x86_64/Archi.v`, and `LICENSE` against the first pin. `Clight.v`,
`Archi.v`, and `LICENSE` are identical. `Cop.v` only adds a `Proof.`
command. The relevant 32-bit type size, alignment, and arithmetic rules
are unchanged. The later `Memory.v` adds a pointer-width bound to
`loadv` and `storev`; 3.17 does not enforce that bound there. Our array
invariant must enforce it explicitly. The bound is satisfied by the
selected maximum sizes when the array starts at block offset zero.
For an array at a nonzero block offset, prove the bound on the sum of
that offset and the array size. Neither version removes the C obligations
listed below. The source links below retain the first review pin.

## Result

A small array program can use behavior shared by Clight, GCC, and Clang.
The proof and printer must impose more restrictions than Clight alone.
Three differences need particular care:

1. Clight defines signed addition, subtraction, and multiplication modulo
   the integer width. ISO C gives signed overflow undefined behavior.
2. Clight permits pointer addition outside an object. ISO C can give the
   addition itself undefined behavior, before a load or store occurs.
3. CompCert memory checks do not enforce ISO C effective types. A load can
   be defined in Clight and violate the alias rules used by GCC and Clang.

Use unsigned integer data, typed array objects, in-range indices, and
separate buffers. Do not rely on compiler flags to remove these differences.

This review does not prove a translation theorem from Clight to ISO C.
The subset contract, printer, target configuration, and GCC or Clang remain
trusted. A proof of a Clight program does not invoke CompCert's compiler
correctness theorem when GCC or Clang compiles the printed program.

## Proposed subset contract

These rules are the proposed boundary for the first implementation.
Changes to this boundary need a further review.

The selected interface is:

```c
unsigned int permute(unsigned int n, unsigned int *data,
    unsigned int *permutation, unsigned int *target, unsigned int *used,
    unsigned int *trace, unsigned int *out);
```

For accepted inputs, `n <= 1024U`. The `data`, `permutation`, `target`, and
`used` arrays each contain at least `n` elements. The trace has at least
`2*n` elements; `out` has at least three elements. All six array ranges are
pairwise disjoint. `out` contains the trace length, blocked position, and
excess depth. Return values are zero for success, one for a blocked swap,
and two for invalid input. The implementation writes the three `out`
elements first. It must check the size before access to the other arrays
and validate each permutation index before indexing `target` by it.
These runtime checks cannot establish the caller's buffer capacities or
pointer validity. Those remain preconditions, including for rejected input
where a buffer is accessed. Define all three output fields on each return
path, and specify whether input arrays can have changed before an error.

At this bound, a byte offset into an `n`-element array is at most 4092,
and a byte offset into the trace is at most 8188. These fit the selected
pointer representation. The proof still has to establish each actual
index bound, alignment, and permission before each access.

| Part | Permit | Exclude |
| --- | --- | --- |
| Target | x86-64 Linux, the normal system C ABI, C11 or C17 | Other targets until their configuration is checked |
| Data | `unsigned int`, 32 bits, and pointers to arrays of that type | Narrow integer types, floating point, enums, structs, unions, bit fields, vector types |
| Conditions | Integer comparisons with `int` results, zero or one | Signed arithmetic and mixed signed/unsigned arithmetic |
| Expressions | Unsigned constants, temporary reads, indexed array reads, `+`, `-`, and integer comparisons | Calls, updates, assignments, volatile accesses, or other effects inside expressions |
| Memory | `a[i]`, where `a` names a live array and `i` is proved within that array | Pointer casts, integer/pointer conversions, pointer subtraction, pointer ordering, out-of-range pointer formation |
| Statements | Scalar assignment, indexed store, sequence, `if`/`else`, a restricted loop, `break`, and return | `goto`, labels, `switch`, `continue`, inline assembly, builtins, external calls, recursion |
| Loop AST | `Sloop body Sskip`, printed as `while (1) { body }` | A general second loop body |
| Storage | Caller-owned arrays and scalar temporaries; no mutable globals | Allocation, deallocation, variable-length local arrays, escaping local addresses |
| Attributes | No attributes in Clight or C | `restrict`, `volatile`, atomics, packed layout, custom alignment, assumptions about aliasing |

If the first implementation does not need one of these operations, leave it
out of the printer. In particular, no multiplication, division, remainder,
bitwise operation, or shift is needed for the permutation loop itself.
An unsigned-to-unsigned cast adds no value when all data have the same type.

The C file should contain compile-time checks for `CHAR_BIT == 8`,
`sizeof(unsigned int) == 4`, `UINT_MAX == 4294967295U`,
`INT_MAX == 2147483647`, `_Alignof(unsigned int) == 4`, and
`sizeof(void *) == 8`. These checks detect some target errors. They do not
prove the calling convention or identify the target by themselves. Record
the compiler target and options in the build. Do not claim support for all
machines that happen to pass these checks.

### Memory preconditions

For every call, state and prove the following where applicable:

- Each buffer designates an actual array of `unsigned int`, with its stated
  capacity, correct alignment, and a lifetime that covers the call.
- All input elements that can be read have initialized values. Output
  elements need initialization only before their first read.
- Array ranges for the permutation, values, trace, and output counters are
  disjoint. This is an API and proof precondition; do not add `restrict`.
- Inputs satisfy the chosen size bound. The permutation contains each
  index from zero through `n - 1` exactly once. An untrusted caller needs a
  checked boundary before it can call a function proved only for this case.
- Each trace write has space. Prove a bound on the trace length, or check
  capacity before each write and specify the resulting error behavior.
- No other thread, signal handler, or callback accesses the buffers during
  the call. This implementation has no concurrent memory semantics.
- For `n == 0`, only the three `out` elements are accessed. No pointer
  arithmetic or access occurs on the other five arrays. Their pointers may
  be null in that case. The contract and proof must preserve this rule.
  Zero elements do not make `null + 0` a valid C expression.

Separate arrays are sufficient. They are not a general requirement of C:
overlap between same-type arrays is possible without undefined behavior.
Here the restriction makes the representation invariant and updates clear.
Do not attempt to check separation by ordering unrelated pointers in C.

Use actual typed arrays in the C harness. In a C++ adapter, use
`unsigned int` objects and copy solc values into integer IDs. Do not pass
solc object storage by casting it to `unsigned int *`. Matching byte size
does not establish type, lifetime, or representation compatibility.

### Arithmetic preconditions

Unsigned arithmetic is modulo 2^32 in both languages. The mathematical
model usually uses unbounded natural numbers, so the proof must also show
that index, size, depth, trace-count, and loop arithmetic do not wrap.

Check `n > 0` before computing `n - 1U`. Establish `pos <= top` before
computing `top - pos`. Establish the capacity and upper bound before an
increment. If a buffer capacity is computed as `2U * n`, prove that this
product fits before using it. Do not assume a small intended use is a
formal size bound.

Print unsigned literals with a `U` suffix. All operands of data arithmetic
must have the same unsigned type. C comparisons return `int`, even when
their operands are unsigned. Keep comparison results in conditions, or
model any conversion to an unsigned temporary explicitly. Avoid unsigned
countdown loops such as `i >= 0U`: the condition cannot become false.

## Differences that the contract addresses

### Overflow, conversions, and shifts

In the pinned [`Cop.v`](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/cfrontend/Cop.v#L677),
`sem_add`, `sem_sub`, and `sem_mul` use `Int.add`, `Int.sub`, and `Int.mul`
without a signed-overflow check. The
[CompCert C manual, section 6.5](https://compcert.org/man/manual005.html)
states that signed arithmetic wraps. N1570 6.5 paragraph 5 gives a different
rule. Thus a successful Clight proof of signed wrap does not justify the
same expression in ordinary GCC or Clang C.

C integer promotions can turn arithmetic on narrow unsigned types into
signed `int` arithmetic. Avoid those types. Do not use an out-of-range
conversion to a signed type. Avoid all shifts initially; C shift counts and
signed left-shift operands have additional restrictions (N1570 6.5.7).
Division also needs separate zero and signed-minimum cases (6.5.5).

[`-fwrapv`](https://gcc.gnu.org/onlinedocs/gcc/Code-Gen-Options.html#index-fwrapv)
addresses signed addition, subtraction, and multiplication. It does not
establish array bounds, effective types, initialization, or all shift and
division rules. The proposed implementation should not need it.

### Pointer bounds, provenance, and alignment

[`sem_add_ptr_int`](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/cfrontend/Cop.v#L653)
computes a block and modular byte offset. It has no array-bound premise.
N1570 6.5.6 paragraph 8 restricts the result to the same array, including
its one-past position. Computing `a - 1` and later adding one is therefore
outside this subset even if the final load would be valid in Clight.

[`Mem.valid_access`](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/common/Memory.v#L220)
requires access permissions for every byte and an aligned offset. This is
necessary evidence for each load and store. It does not prove that pointer
formation stayed inside the corresponding C array. State that property
in the array representation invariant as well.

Keep a base pointer and an integer index. Form `a + i` only as part of an
access with `i < capacity`; this avoids even one-past pointers in the
generated core. Never synthesize pointers from integer addresses, combine
pointer fragments, or inspect pointer bytes. This avoids dependence on
the differences in pointer provenance rules and compiler extensions.

Clight blocks do not by themselves describe every C subobject boundary.
Do not traverse several struct members or rows of a nested array as one
flat array. Use one declared array per buffer. Keep every byte offset
within the configured pointer range as well as the array bound.

### Effective types, aliasing, and lifetime

CompCert memory stores bytes and pointer fragments with permissions.
Its access rules have no ISO C effective-type history. The
[CompCert manual, section 6.5](https://compcert.org/man/manual005.html)
explicitly permits some integer/float representation accesses that are
outside the ordinary C alias rules.

N1570 6.5 paragraphs 6 and 7 define effective types and allowed access
types. [GCC enables strict alias analysis at `-O2` and `-O3`](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html#index-fstrict-aliasing).
[Clang also uses these rules](https://clang.llvm.org/docs/UsersManual.html#strict-aliasing).
Use the declared element type for all loads and stores. Exclude unions,
byte-buffer casts, and custom allocator tricks. This keeps the implementation
valid with strict alias analysis enabled.

N1570 6.2.4 requires live objects. A Clight memory proof must track live
blocks and permissions. The C caller must supply live objects too. No
freeing, reallocation, placement construction, or returning local pointers
occurs in the generated core. No `restrict` qualifier is printed: it would
introduce a further C access contract (N1570 6.7.3.1).

### Initialization and expression order

Clight expressions are pure; see the
[`Clight.v` introduction](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/cfrontend/Clight.v#L17).
Keep this property in the printed C. Use separate statements for a load,
an update, and a store. Do not introduce `++`, compound assignments, calls,
or comma expressions as printer shortcuts. Pure nonvolatile expressions
avoid dependence on C's unspecified operand order and the unsequenced
side-effect rule (N1570 6.5 paragraphs 2 and 3).

Clight initializes temporaries to `Vundef`, and a load can return an
undefined value. A proof must exclude undefined values where C reads an
object. It is not sufficient merely to permit such a value in an execution
relation. Assign every temporary on every path before its first read.
Represent those initial assignments in the AST; the printer must not add
initialization that the proof never examined. Read only the written prefix
of an output trace. Do not compare uninitialized output storage or padding.

## Printer obligations

Clight constructors accept type annotations; they do not ensure that those
annotations describe a valid C program. In particular,
[`step_set`](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/cfrontend/Clight.v#L569)
copies an evaluated value into a temporary without a cast. C assignment
converts to the declared destination type. Arbitrary annotated Clight
therefore cannot be printed safely by discarding its types.

The printer must accept only the subset above, and must reject the entire
output on any unsupported input. A constructor for a typed restricted AST,
or a small checked boundary, can supply these restrictions:

1. Each identifier has one declared type. All parameter and temporary names
   are unique. Every use agrees with that declaration. Each assignment has
   the required type; each operator and result annotation has its C type.
2. Every pointer load/store has the one supported pointee type. No volatile
   or alignment attribute is silently discarded. There are no composites,
   global data, external definitions, builtins, or nondefault call options.
3. Map identifiers injectively to C names, such as `v123`. Never use raw
   input text as a name. Reserve function names separately. Avoid `$`,
   keywords, and implementation-reserved identifiers.
4. Print each expression with explicit parentheses. Print integer constants
   from their unsigned mathematical value, without host-integer truncation.
   Do not reorder, combine, or remove statements.
5. Print `Sloop body Sskip` as `while (1) { body }`. Reject a nonempty second
   body and reject `continue`. In Clight, `continue` in the first body runs
   the second body; a naive C `while` translation could skip it. See
   [`step_skip_or_continue_loop1`](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/cfrontend/Clight.v#L608).
   Permit `break` only within a loop.
6. Require a result on every normal return path of a nonvoid function.
   Use the same prototype in the C definition and every caller. Compile
   generated files as C. Give the separate C++ adapter an `extern "C"`
   declaration; do not compile the C core as C++.

Keep the printer's formatting code free of algorithm logic. Its input must
be the actual AST named by the proof. A parallel handwritten C body, or a
printer that ignores the AST and emits a template, does not give that link.
The extraction setup, if used, is another part of this link and needs review.

## Checks for the first implementation

Build with both GCC and Clang, using C11, `-pedantic-errors`, `-Wall`,
`-Wextra`, `-Wconversion`, and `-Wsign-conversion`. Test optimized output
with strict alias analysis enabled, including `-O2` and `-O3`. Also test
with AddressSanitizer and UndefinedBehaviorSanitizer. These checks can find
errors; they do not prove the absence of effective-type, provenance, or
other undefined behavior. Do not present a sanitizer pass as a substitute
for the proof preconditions.

Test the printer's rejection path for every excluded constructor and for
bad type annotations, duplicate names, invalid constant types, nondefault
attributes, and unsupported loop forms. Check fixed output examples so that
operator precedence, signedness, and statement order remain visible in review.

The proof must establish defined execution and termination under explicit
preconditions. A theorem that only says “if execution succeeds, the result
is correct” leaves memory faults and stuck states open. Include error paths,
trace capacity, empty inputs, and maximum accepted lengths. State what the
stack and trace contain after an error, since C updates can occur before it.

The existing Lean and Rocq spike intentionally differ from solc on equal
values. See `Shuffler/Permute/Defs.lean`: it lists destination reassignment
and suppression of swaps of equal values as TODOs. The user selected exact
solc behavior, including duplicates. The new model and implementation must
therefore add these rules before claiming equivalence. Differential tests
must include duplicates and compare the selected observable behavior. They
must not silently discard these cases. This specification difference is
separate from C undefined behavior.

## License boundary

The pinned [CompCert license](https://github.com/AbsInt/CompCert/blob/7e980792eeabe20285cabace5a5bd93fcc3c01d7/LICENSE#L20)
offers LGPL-2.1-or-later for `Clight.v`, `Ctypes.v`, `Cop.v`, all files in
`common/` and `lib/`, and the listed architecture definitions. These are
the sources used for this semantics review. Flocq has LGPL-3.0-or-later
terms. The referenced manuals and C standard draft are review references;
they are not code imported into the build.

The implementation build must use an explicit list of LGPL-covered files
and inspect their transitive imports. Do not import compiler passes,
CompCert's top-level compiler driver, or its default extraction dependency
closure. An LGPL license on an extraction script does not make all modules
imported by that script LGPL. Do not require `clightgen` or `ccomp` for
generation, proof, testing, or printer review.

The output can be licensed GPL-3.0-or-later. Preserve the original licenses
and notices on copied LGPL sources. A declaration that the new project is
GPL cannot authorize a dependency on CompCert's non-commercial fragment.
