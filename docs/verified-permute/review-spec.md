<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Review of the Permute specification

Review date: 2026-10-06. This review reads the model, invariant definitions,
and public theorem statements. It does not replace kernel checking. No
proof source was changed in this review.

## Pass 1: input domain and memory

`ClightCorrect.permute_call_correct` quantifies over a finite permutation
`p : 'S_(d+1)` and a source function from indices to natural numbers.
It requires `d+1 <= 1024` and a 32-bit unsigned bound for every source value.
Thus it covers nonempty valid permutations and the full unsigned value
range, including duplicates. It does not cover malformed permutations.

The six block identifiers must be distinct. `array_at` requires both the
specified loads and writable access. `writable_array` requires writable
access at each element offset. These hypotheses require initialized data
and permutation arrays, but only capacity for target, used, trace, and
output arrays. They do not require the work arrays to contain zero on
entry. Output initialization and valid-permutation validation supply the
initial contents used later.

I found no contradictory premise in this domain. Finite permutations
exist at each permitted size; all-zero source values meet the value bound;
six separate allocations with initialized input elements can meet the
memory predicates. This is a source-level satisfiability argument, not a
new Rocq theorem constructing those six allocations.

The API requires more than byte-level Clight memory. Actual C object type,
lifetime, alignment, separation, and writable storage remain caller
obligations. All pointers in the theorem start at block offset zero.
Disjoint slices within one allocation are outside this theorem's stated
representation.

The empty and oversized call theorems require only writable `out` storage.
Malformed-permutation rejection remains a tested C behavior without a
universal call theorem. A general statement that all API inputs are
formally verified would therefore be too broad.

## Pass 2: target direction and duplicate normalization

In `SolcModel.v`, `target_of s p = s ∘ p⁻¹`. Thus `p` maps a source index
to its destination, as the C header and differential checker intend.
The success equation `result j = s (p⁻¹ j)` implies
`result (p i) = s i`; the inverse is in the correct direction.

`normalize_complete` establishes all three of the following:

* normalization returns a permutation;
* that permutation is compatible with the required target values;
* every position whose value is already correct is fixed by the new
  permutation.

The third property matters for duplicate values and for the requested
depth criterion below. It is stronger than compatibility alone. A
compatible permutation can still move equal values between positions
that already contain the required values.

`raw_normalize_complete` connects the permutation-valued model to the
finite-function form of the actual greedy writes. The model visits source
indices and free destination indices in ascending order. This is the
intended duplicate pairing. It is not itself a proof of the C++
`stable_sort`, grouping, and set-difference implementations. That source
connection remains separate work.

The loop exchanges destinations even when the selected values are equal.
It omits the physical swap and depth check in that case. This matches the
intended solc behavior. Decreasing rank counts these steps too, so equal
values cannot defeat the model's termination argument.

## Pass 3: observations and postconditions

`solc_result_spec` alone permits any legal trace with the stated final or
blocked state. It is not an exact-trace equivalence specification by itself.
However, the public Clight theorem also requires
`SolcModel.solc_permute source p = Some result`. Its `result_arrays`
postcondition maps that same result to the C-visible data, trace prefix,
trace length, blocked position, excess depth, and return value. Together,
these clauses establish the exact mathematical model trace.

For a blocked result, the specification retains the partial data and trace,
the selected position, unequal selected values, depth greater than 16, and
the exact excess depth. It also retains the target relation through the
remaining permutation. It does not pretend that a blocked call completed
the requested permutation.

Only the trace prefix is initialized and specified. The unwritten suffix
must remain outside comparisons. The test miter follows this rule.

The full Clight theorem constructs an `eval_funcall` execution and permits
only return codes zero and one on its valid-input domain. Its premises do
not assume an already successful execution. The target initialization and
normalization steps are included before the swap loop.

The mathematical model lemmas have no 1024 size bound. The Clight theorem
does have that bound. Neither theorem states a C++ execution relation.
Small symbolic C/C++ proofs must not be described as a proof for every
permutation through 1024.

## Success-if-and-only-if theorem

Let `target = target_of source p`. For a nonempty stack, let the depth of
position `j` be `top - j`, where `top = n-1`. The requested property is:

```text
the result is SolcDone
    iff
for every j with depth(j) > 16, source(j) = target(j).
```

This was absent during the first review. `Reachability.v` now proves it
as `solc_success_iff_reachable`. It also proves that failure of this
condition is equivalent to a `SolcBlocked` result. I read both proofs and
the Clight call corollary after these files were added.

The proof of necessity uses `trace_preserves_deep`: each legal physical
swap touches only the top and a position whose depth is at most 16.
The successful final-array equation then gives the required equality
at every deeper initial slot.

The proof of sufficiency uses the fixed-point clause of
`normalize_complete`. All initially correct deep positions are fixed
by the normalized permutation. `choose_some` excludes those fixed
positions, and `exchange_keeps_deep` preserves them through each step,
including steps between equal values. Thus no selected position can
have depth greater than 16. Termination and no-exhaustion leave a
successful result.

`ClightReachability.permute_call_reachability` carries this result to the
actual Clight function call. It retains the memory and valid-input
premises of `permute_call_correct`, with `n <= 1024`. The postcondition
relates return code zero to `values_reachable`, and return code one to
its negation. The mathematical theorem has no 1024 size bound.

The strict boundary is `depth > 16`, not `depth >= 16`. For `n <= 17`
there are no such positions, so every valid permutation must succeed.
For `n = 18`, only position zero is deeper than 16. With duplicates,
the test is equality of the initial and required **values**, not whether
the original permutation fixes the position.

## Remaining proof links

The principal open links are source-level C++ equivalence for the full
domain and malformed-permutation rejection.
The printer, extraction, C subset contract, source compiler, and execution
platform also remain in the trust boundary. A symbolic LLVM proof can add
evidence about particular compiled functions, but does not remove those
source-to-LLVM and model-to-source links.
