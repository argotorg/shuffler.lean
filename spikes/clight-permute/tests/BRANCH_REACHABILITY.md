# Branch reachability

Review date: 2026-10-06. This is a source analysis, not a coverage result.
Keep all measured branch outcomes in the coverage denominator. An
unreachable outcome is still uncovered; it must not be reported as covered.

The C input domain is the contract in [permute.h](../permute.h), including
invalid sizes and invalid permutations that the function rejects. Buffers
must have the required capacities, types, separation, and lifetime. No
other code may change them during the call. The upstream C++ Permute domain
is a nonempty stack and a valid permutation; its caller establishes these
conditions. Invalid C inputs must not be passed to the C++ oracle.

Line numbers below refer to the current generated [permute.c](../permute.c)
and the unmodified `.inc` files from `prepare_oracle.py`. The reviewed C
file has SHA-256
`a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78`.
The reviewed `solc_permute.inc` has SHA-256
`6d2864500674270821ee5702ccf1787ef27716d598c98c6cc139e80c67f53476`.
The oracle source is Solidity commit
`cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`.

## Generated C

| Line and condition | Unreachable outcome | Reason and proof link |
| --- | --- | --- |
| 82: `v9 < v1` | False: the free-destination search reaches `n` | A destination with the required value remains for each source that needs assignment. The scan stops at that destination before `n`. `ModelProofs.raw_normalize_complete` establishes successful greedy assignment. `ClightSearch.search_scan_found`, `ClightFill.fill_body_found`, `ClightFillLoop.fill_pass_correct`, and `ClightNormalization.normalize_correct` connect it to the actual AST. |
| 95: `v9 == v1` | True: return 2 after failed search | The same invariant gives a selected ordinal strictly below `n`. This guard is defensive. `fill_body_found` proves that its condition evaluates to false. |
| 134: `v7[0U] >= v1 + v1` | True: return 2 for exhausted trace capacity | `ModelProofs.rank_bound` gives initial fuel at most `2*n`. `ClightMain.main_loop_refines` maintains `length(trace) + fuel <= 2*n` and proves positive remaining fuel before an emitted swap. It derives a strict bound on the trace count before the store. `main_loop_nonempty` and `ClightCorrect.permute_call_correct` discharge that invariant from the API preconditions. |

Invalid permutations cannot make these outcomes reachable. Before
normalization, lines 47 and 51 reject every out-of-range or repeated
destination. Finishing that loop means that the `n` entries are distinct
members of `0..n-1`, hence a permutation. The zero and oversized cases
return earlier. This converse argument about the validation code is a
source review; the current universal Rocq call theorem assumes a valid
permutation.

There are 21 nonconstant conditions in this C source. These three
outcomes alone prevent coverage of all 42 outcomes. Use the actual LLVM
report for the measured denominator. Do not delete the defensive guards,
change their conditions, corrupt work buffers, or violate the pointer
contract to reach them. Initial contents of `out`, `used`, or `target`
cannot force them: the implementation writes the required contents first.

## Upstream C++ Permute body

| `solc_permute.inc` line and condition | Unreachable outcome | Reason |
| --- | --- | --- |
| 61: `yulAssert(movers.size() == vacant.size())` | Failed assertion: the sizes differ | `group` is a set of positions. A valid permutation makes `desired` a set of the same size. Both set differences remove the same intersection, so `|group - desired| = |desired - group|`. In the upstream `Shuffler.cpp`, this is line 671. |

The assertion remains enabled. If LLVM records its failure outcome, that
outcome remains in the denominator. No Rocq theorem about execution of the
C++ source is claimed; this is the finite-set argument written above.

The comment at line 35 mentions an empty group. `chunk_by` emits nonempty
groups, but this does not make either outcome of line 36 unreachable:
`distance(group) < 2` is true for a singleton and false for a duplicate
group. Equal-value exchanges at line 70 are also reachable after
normalization. Do not exclude either outcome of that condition. Both
blocked-return sites, lines 89 and 106, can be reached with large enough
stacks. A top-to-bottom exchange reaches line 89; a cycle below a fixed
top can reach line 106.

## Reached C++ helpers

If the coverage scope includes these helper files, retain their outcomes
too. They add unreachable outcomes beyond the Permute body itself.

| File and line | Unreachable outcome | Reason under the oracle call contract |
| --- | --- | --- |
| `solc_mapping.inc:43` and `:44` | Either `bind` assertion fails | The adapter binds each source once to a distinct destination. |
| `solc_mapping.inc:53` and `:55` | Either destination is absent | All mapping entries start present. Permute only exchanges entries; it does not remove them. |
| `solc_emission_helpers.inc:41` | `!isFinal(_pos)` is false | A physical swap selects a value that is not at its desired position. See the argument below. |
| `solc_emission_helpers.inc:48` | `_excess > 0` is false | The caller computes `depth - 16` only after establishing `depth > 16`. |
| `solc_stack_helpers.inc:21` | `isValidSwapTarget` is false | The selected position is below the top and within the stack; the preceding reachability test establishes depth at most 16. |
| `solc_stack_helpers.inc:23` | `m_trace` is null | This adapter always supplies `&m_trace`. This restriction comes from the adapter, not from the general upstream Stack API. |
| `solc_stack_helpers.inc:29` | Any of its three `&&` operands is false | At this call, `1 <= depth <= 16` and `depth < size`. Each short-circuit false outcome is unreachable if LLVM counts it separately. |
| `solc_stack_helpers.inc:37` | `_offset < size()` is false | Permute selects a permutation destination or an index from its descending in-range scan. |

For the `isFinal` assertion, both destination mappings remain compatible
with the desired values. When following the top's destination, a selected
value different from the top cannot already be correct at that destination.
At a cycle start, normalization has fixed every initially correct-valued
position. Each completed cycle fixes the non-top positions it visits, so
any remaining moved position is still incorrect. These facts exclude a
physical swap of a final slot. The Rocq `choose_some` and `chosen_depth`
lemmas establish the related bounds for the model; they are not a proof
of the separate C++ mapping code.

The copied `Mapping` class also contains methods that Permute never calls,
such as `pop` and `push`. This review does not claim that those methods or
all range-v3 and standard-library branches are covered. Report their
coverage separately if they are included in the instrumented source scope.

Coverage-guided fuzzing can increase coverage of reachable outcomes. It
cannot satisfy literal 100% branch coverage of these unchanged sources
under their contracts. Report the raw result and this reachability analysis
together; do not replace the raw result with an adjusted percentage.
