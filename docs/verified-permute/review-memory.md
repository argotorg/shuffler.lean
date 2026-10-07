# Independent review of the generated C and Clight memory contract

Review date: 2026-10-06. Reviewed `spikes/clight-permute/permute.c`
against `Permute.v`, `permute.h`, `ClightMemory.v`, `ClightCorrect.v`, and
the existing C semantics review. The generated C SHA-256 is
`a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78`.
No translation or sequencing mismatch was found. This review does not
prove an ISO C translation theorem or the correctness of GCC/Clang.

## Statement review

The line references below are for the unchanged `permute.c`.

| C lines | Check against the AST and memory contract |
| --- | --- |
| 1–10 | License/generation notices, headers, and target checks. The checks match the selected integer sizes and alignment. They do not identify the ABI or prove the full target contract. |
| 12 | One unsigned scalar and six unsigned-array pointers match `Permute.permute`'s parameters. Pointers require the caller's validity, capacity, lifetime, type, and separation contract. |
| 14–19 | Unsigned temporaries match `fn_temps`. No initializer is added by the printer. The reads below follow assignments on their paths. |
| 20–22 | The first stores initialize all three output fields. `out` needs valid writable storage even for an empty or rejected size. |
| 23–30 | Size rejection and empty success precede every other buffer access. Other pointers may be null on these paths. No `null + 0` is formed. |
| 31–39 | The first `each` loop sets every `used` element to zero. The comparison bounds each access; the increment remains at most 1024. |
| 40–58 | The second `each` loop reads initialized input destinations. The range guard precedes `used[destination]`. The duplicate guard precedes target writes. Target receives `data[source]` at its destination. A valid finite permutation covers every target element. The universal valid-input proof supplies this fact; invalid-permutation rejection is a separate tested API behavior. |
| 59–72 | The first normalization pass reads the fully initialized target. Correct values fix their destinations; every used flag is reset to zero or one. No old scratch contents are needed. |
| 73–104 | The second pass searches from zero for the first unused equal target. The loop condition precedes both indexed reads. The `j == n` guard prevents an out-of-range store if search fails. Proving that valid inputs cannot reach that defensive return requires the matching/permutation invariant, not just index bounds. |
| 105 | `n - 1` follows the nonempty check. With accepted size, `top` is in 0 through 1023. |
| 106–124 | The selected position first comes from the normalized permutation. If the top is fixed, the countdown tests for zero before subtraction and reads only positions below `n`. Returning success requires that the permutation is identity. This depends on the permutation invariant. |
| 126 | Equal values skip the physical exchange, depth failure, and trace update. Their destinations still exchange at lines 145–147. This matches the selected solc behavior. |
| 127–133 | `top - pos` needs `pos <= top`. The permutation and selection invariants provide it. A blocked return records the selected position and positive excess depth before returning one. Data and trace retain prior exchanges. |
| 134–137 | The trace capacity check precedes its store. `n + n` is at most 2048. Proving the defensive return unreachable on valid input also needs the model's trace/rank bound. |
| 138–140 | Three separate statements swap unsigned values. The saved temporary prevents the first store from changing the second store's source. Both positions are within the data array. |
| 141–142 | The trace store uses the checked old count; only then is the count incremented. Consumers may read only the written prefix. The unused tail has no output-value contract. |
| 145–147 | The same three-statement pattern exchanges destinations. Array separation prevents this from changing the data or trace objects. |
| 148–149 | The outer loop and function close. The constant `while (1)` spelling retains C's constant-condition loop behavior. Termination comes from the proved rank argument; it is not supplied by the printer. |

Empty `else` blocks and braces preserve the AST's `Sskip` and statement
nesting. Every array expression is a typed unsigned access. All expressions
are free of side effects. There are no signed arithmetic operations,
pointer casts, pointer ordering, shifts, `restrict`, volatile/atomic
accesses, allocation, calls, mutable globals, or escaping local addresses.

## Caller and memory model boundary

`ClightMemory.v:8` defines writable array capacity as valid aligned
four-byte accesses. `ClightMemory.v:20` adds initialized word contents.
`ClightCorrect.v`'s `separate_arrays` requires different CompCert blocks
for all six arrays; its call theorem uses pointers at offset zero.
Only data and permutation require initialized contents on entry. The
other buffers require writable capacity. Every ordinary temporary read
has a preceding assignment; no read of an undefined temporary was found.

CompCert's byte permissions alone do not establish ISO C effective types,
array-subobject boundaries, or object lifetime. The caller must pass the
first element of six separate live `unsigned int` array objects, with the
stated capacities. The proof is not a contract for slices of one larger
allocation. A cast from solc object storage would not meet the contract.
No other thread, signal handler, or callback may access the arrays during
the call. The generated function cannot check these conditions.

Within this contract, every pointer is formed only for an indexed access.
The largest possible accessed byte offsets are 4092 for an `n`-element
work array, 8188 for the trace, and eight for output. The bounds fit the
64-bit pointer model and require no modular pointer wrap. Byte order is
not observed by the algorithm: all loads and stores use the same declared
unsigned type.

## Remaining proof obligations

The existing complete Clight call theorem does not by itself prove the
printed C correct under ISO C or prove the unverified C compiler correct.
Extraction, the printer, target/ABI selection, and the compiler remain
trusted parts of that route. The direct Frama-C effort must prove its own
source-C obligations and cannot cite a Clight execution as a substitute.

For the new Frama-C claim, safety and final target values are insufficient.
The required result is success with the exact valid swap trace if and only
if every initially wrong value lies within depth 16. For duplicates, a
position is wrong when its initial value differs from the value required
there, not when its original permutation entry differs from its index.
Otherwise the result must be blocked with a valid partial trace and exact
blocked fields. The source-C proof needs normalization completeness,
permutation preservation, the decreasing rank, trace capacity, trace
replay, and preservation of initially correct inaccessible positions.
Every unproved obligation must remain visible in the Frama-C results.
