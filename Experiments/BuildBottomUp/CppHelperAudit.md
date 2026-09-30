# C++ helper comparison

Reviewed on 2026-09-30 against the checked Lean working tree and Solidity commit
`cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`.
Updated after the helper control-flow changes described below.

The final permutation's handling of equal values is a known divergence that
the user accepted for now during this review. It can emit extra swaps and
report a blocked operation where C++ succeeds. No change to that behavior is
proposed here. The remaining helpers agree on successful effects within the
common input domain described below. Several checks and failure results
differ outside that domain.

The final permutation branch was moved from `finish` into `buildBottomUp`
during this review. This moves the code to the same branch as C++. It does not
change the permutation routine or resolve its behavior differences.

## Sources and comparison domain

- [Checked.lean](Checked.lean): checked predicates, stack queries, helpers,
  scans, and the loop with its final permutation branch.
- [C++ Shuffler.cpp](../../solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp):
  `Emission` and `Mapping`.
- [C++ Stack.h](../../solidity/libyul/backends/evm/ssa/Stack.h): the stack changes
  and trace emission called by `Emission`.
- [Lean State.lean](../../Shuffler/State.lean): shared state type.
- [Lean Permute/Defs.lean](../../Shuffler/Permute/Defs.lean): final permutation.

The common domain uses valid offsets, a consistent partial bijection, an
unbound generation destination, the pending-generation invariant, and the
default EVM reach: SWAP depth 16 and DUP source depth 15. Slot values are
limited to literals, non-literal variables, and junk. Lean's `.Wildcard` is
the junk value for these helper operations.

C++ also supports function call return labels, function return labels, and
configurable reach. Lean's current `Value` and trace types do not model those
cases. C++ compares literal instruction IDs; Lean compares literal words.
`InstructionStore::appendLiteral` deduplicates words within one store, which
supports the intended correspondence for literals from that store.

Lean uses `StateT` to pass immutable state values between actions. An error
stops later actions and returns no state. The C++ helpers change `m_data`,
`m_trace`, and `m_mapping` in sequence. The comparison below distinguishes
the resulting successful state from the order of checks and partial changes
on failure. Proof terms and equality casts do not emit stack operations.

## Check and query helpers

| Lean statement | C++ counterpart | Finding |
| --- | --- | --- |
| `requires`: decide the condition | `yulAssert`, `Exceptions.h:68` | Both test the condition at runtime. |
| `requires`: return the proof on success | Continue after `yulAssert` | `PLift` supplies Lean's construction proof; no stack, mapping, counter, or trace effect. |
| `requires`: return `.assertion reason` on failure | Throw `YulAssertion` | Different failure interface. C++ also uses exception metadata and a default description for an empty message. |
| `ensure`: call `requires`, discard the proof, return `Unit` | Continue after `yulAssert` | Same check; the proof is not used by the caller. |
| `liftResult`: preserve success and rename `Blocked` | No direct helper | This adapts the old Lean error type. It cannot recover the C++ blocked offset or working state. |
| `index`: check `offset < size`, construct `Fin` | Bounds needed by stack access | Added checked boundary. Direct C++ vector indexing does not perform this check. |
| `index`: return the bounds error | `Stack::offsetToDepth`, `Stack.h:137`, has a bounds assertion | Similar purpose, but different messages and failure interface. |
| `slotAt`: call `index`, then read the slot | `m_data[offset]` or `m_target[offset]` | Same value for a valid offset; Lean defines an error for an invalid offset. No state change. |
| `positionOf`: check target bounds | `Mapping::positionOf`, `Shuffler.cpp:84`, indexes directly | An added check. Lean returns `none` for an invalid target offset. C++ provides no defined out-of-bounds result. |
| `positionOf`: inverse mapping lookup and `Fin.val` | Return `m_positionOf[destination]` | Same optional source offset on valid inputs. |
| `depthOf`: `length - 1 - offset` | `Stack::offsetToDepth`, `Stack.h:135` | Same depth for a valid offset. Lean uses saturating natural-number subtraction. C++ checks the offset before unsigned subtraction. |
| `isSwapReachable`: depth at most 16 | `Emission::isSwapReachable`, `Shuffler.cpp:747` | Same for valid offsets with reach 16. Both consider the top reachable, although swapping the top with itself is not a valid SWAP instruction. |
| `Decidable` instances | C++ Boolean conditions | They make the Lean predicates executable. They do not change state. `is_available` is a Lean specification predicate, not a separate C++ operation. |

The invalid-offset difference is observable: on a two-slot stack,
`depthOf state 2 = 0` and `isSwapReachable state 2` is true. The corresponding
C++ depth conversion throws an assertion. Current proofs use valid offsets;
the query helper types do not enforce this restriction themselves.

The shared `State.is_final` predicate uses an inverse lookup, while C++
`isFinal` checks `destinationOf(pos) == pos`. These are equivalent on valid
source offsets because the mapping is a partial bijection. The shared
`Stack.shallowest_copy_position` reverses source positions and stops at the
first equal value, as C++ does. The shared DUP and SWAP reach predicates take
`Fin` indices, so their callers already establish the bounds that C++ checks
inside its depth conversion.

## `push`

C++ entry: `Emission::push`, `Shuffler.cpp:780`.
Stack operation: `Stack::push`, `Stack.h:76`.

| Lean statement | C++ statement | Finding |
| --- | --- | --- |
| Check that `dest` is unbound | `Mapping::bind` checks this at `Shuffler.cpp:94` | Lean checks first. C++ reaches this check after appending data, recording the operation, and extending the mapping. |
| Check free generation or spill membership | The `produce` caller chooses push for those cases | An extra helper-level check. `Stack::push` does not check spill membership; a direct push of an unspilled non-literal value would record `Load` in C++. Lean rejects it. |
| Prove the new length | No runtime counterpart | Required for the dependent mapping type. |
| Append `slot` to `stack` | `m_data->emplace_back(_slot)`, `Stack.h:79` | Same appended value. |
| `.Var` records `Load`; `.Lit` and `.Wildcard` record `Push` | Conditional trace emission, `Stack.h:83` | Same operation and operand for the supported slot kinds. |
| Extend the mapping and bind its top to `dest` | `m_mapping.push`, `Shuffler.cpp:783` | Same forward and inverse bindings. Other assignments are preserved. |
| Preserve the remaining state fields | No counter or planned-mapping update | Same. `push` does not decrement `pending_generations`. |

Successful effects agree. Assertion timing and partial mutation on an invalid
destination differ. A C++ assertion throws; it does not return an
`Emission::Result` containing the partially changed state.

## `dup`

C++ entry: `Emission::dup`, `Shuffler.cpp:786`.
Stack operation: `Stack::dup`, `Stack.h:88`.

| Lean statement | C++ statement | Finding |
| --- | --- | --- |
| Accept a natural-number offset and check it against the current stack | `offsetToDepth(_copy)` checks bounds | Lean constructs a `Fin` index after this check. An invalid offset returns an assertion error. |
| Check that `dest` is unbound | Mapping check after `m_stack.dup` | Same requirement, different check order. |
| Check DUP reach | `dupReachable(depth)`, `Stack.h:91` | Same valid range: source depths 0 through 15 at default reach. |
| Compute `depth` | `auto const depth = offsetToDepth(_offset)` | Same value. |
| Apply the named stack-equality lemma and establish the new length | No runtime counterpart | These align the trace and mapping types. |
| Append `state.stack[copy]` | Read the slot, then `m_data->push_back(slot)` | Same value and height. |
| Record `Trace.Dup (depth + 1)` | `ShuffleOp::dup(Depth{depth.value + 1})` | Same instruction operand: source depth 15 emits DUP16. |
| Push the destination binding | `m_mapping.push(_destination)` | Same mapping effect; no counter change. |

C++ also rejects duplication of a function return label. That slot kind has
no Lean representation. For a bound destination and an unreachable copy,
Lean reports the bound destination first; C++ fails the reach check first.

## `swapDestinations`

C++ counterpart: `Mapping::swapDestinations`, `Shuffler.cpp:100`.

1. Lean checks both source indices through `index`. C++ uses direct indexing.
2. Lean composes the mapping with a transposition of the two source indices.
   C++ swaps their forward entries and repairs each present inverse entry.
3. Both leave data, trace, pending count, and planned mapping unchanged.

The resulting mappings agree for valid indices, including equal indices and
unbound positions. The representation as a partial bijection keeps Lean's
forward and inverse lookups consistent by construction.

## `swapWith`

C++ entry: `Emission::swapWith`, `Shuffler.cpp:767`.
Stack operation: `Stack::swap`, `Stack.h:60`.

| Lean statement | C++ statement | Finding |
| --- | --- | --- |
| Check the source index | Bounds check inside `Stack::offsetToDepth` | Lean checks before testing finality; C++ tests finality first. |
| Check below-top, reach, and not-final in one condition | Assert not-final, then assert a valid SWAP target | Same accepted domain at default reach. The check order and error strings differ. |
| Compute depth and apply the named conversion lemmas | Stack offset/depth conversion | Same depth; remaining work is proof construction. |
| Swap `offset` with the top in `stack` | `std::swap` in `Stack::swap` | Same values are exchanged. |
| Exchange their mapping destinations | `m_mapping.swapDestinations` | Same assignments follow the values. |
| Record `Trace.Swap depth` | `ShuffleOp::swap(offsetToDepth(_offset))` | Same SWAP operand. C++ records it before changing the mapping. Lean constructs one resulting state. |
| Preserve pending count and planned mapping | No corresponding writes | Same. |

There is no equal-value shortcut inside either `swapWith` helper. The caller
must choose `swapDestinations` when it wants to avoid a physical swap.

## `produce`

C++ counterpart: `Emission::produce`, `Shuffler.cpp:388`.

| Lean statement | C++ statement | Finding |
| --- | --- | --- |
| Reject a bound destination at entry | No entry check | Extra check. C++ checks the binding when a successful push or dup updates the mapping. An unreachable-copy branch can return `Blocked` before that check. |
| Read `target[dest]` | Read `m_target[_targetOffset.value]` | Same slot on valid inputs. |
| Find the shallowest copy | `shallowestCopyPosition(slot)` | Both search from top to bottom and stop at the first equal slot. Both do this before the junk test. |
| Junk: call `push` | First C++ branch | Same. Existing junk is not duplicated. |
| Copy exists and is reachable: call `dup` | Second C++ branch | `else if let some pos := copy.filter ...` tests reach only when a copy exists. This takes precedence over loading a spill or pushing a literal. |
| Freely generated or spilled: call `push` | Third C++ branch | Same fallback when no reachable copy exists. |
| Copy exists: return `blocked (depth - 15)` | `blockDupUnreachable` | Same excess at default reach. Lean omits the copy offset from the error. |
| No copy and no generation source: assertion error | Final C++ assertion | Same reason string; different error interface. |
| Call state actions in the `if / else if` chain, then read the state with `get` | Update the emission state in the C++ branches | Successful branches continue to the shared check and decrement. Failed branches skip all later work. |
| Check that `positionOf(state, dest)` is the new top | Assert that `positionOf(dest)` is the new top, `Shuffler.cpp:402` | Same condition and position before the decrement. Lean supplies a message; C++ uses its default assertion description. The equivalence proof establishes that the check succeeds. |
| Subtract one from pending count | `--m_pendingGenerations` | Same under the pending-count invariant. With an inconsistent zero counter, Lean stays at zero and C++ unsigned arithmetic wraps. |
| Return `Unit` in the state action | Return `std::nullopt` with mutated state | Same successful effects in the common domain. `Action.exec` returns the final Lean state. |

## `generate`

C++ counterpart: `Emission::generate`, `Shuffler.cpp:410`.

1. `index target.length targetOffset` is an extra checked boundary for the C++
   raw target index, applied before `produce`.
2. Calling `produce ...` propagates failure immediately, as the
   C++ `if (blocked = produce(...)) return blocked` does.
3. The outer test is the same: destination strictly below the new top and
   not final. All checks use the state after production.
4. `slotAt` checks bounds for the destination and top reads. The outer guard
   ensures both offsets are valid. The reach check uses `isSwapReachable` with
   the same offset as the main loop; no `Fin` construction appears in the body.
5. Equal destination and top values cause a mapping-only exchange. This
   occurs before the reach check, so equal values can be retagged out of SWAP
   reach. Lean uses an explicit `else if` for the following SWAP branch,
   matching C++.
6. Otherwise, a reachable destination gets one `swapWith` operation.
7. Otherwise, return the produced state unchanged. In particular, an
   unreachable placement is not an error here: both versions leave the new
   slot on top for `buildBottomUp` to handle later.

The successful effects and branch priority agree in the common domain.
Changing the outer guard to a failing `requires` would be incorrect: its
false branch is a successful return, not an assertion failure.

## Final permutation, now inside `buildBottomUp`

C++ branch: `Shuffler.cpp:487`. C++ routine: `Emission::permute`, line 629.
Lean branch: `buildBottomUp` in `Checked.lean`. Lean routine: `Shuffler/Permute/Defs.lean:34`.

1. Both enter when the pending count is zero, after the final-slot skip.
2. Lean checks equal lengths and complete source bindings. C++ asserts equal
   lengths, then calls `.value()` on each source destination while building
   the permutation. Valid inputs produce the same source-to-target map.
3. The called routines differ. C++ first reassigns destinations among equal
   values, keeping slots already at a desired offset. Lean omits this phase.
4. C++ then checks equality before SWAP reach in `exchangeWithTop`; equal
   values only exchange mapping destinations. Lean checks reach and emits a
   physical SWAP without this equality branch. Both omissions are already
   marked as TODOs in `Shuffler/Permute/Defs.lean`.
5. Once those equal-value differences are excluded, both place a misplaced
   top first, otherwise choose the shallowest misplaced slot. Lean scans
   bottom-to-top and retains the last match; C++ scans top-to-bottom and
   breaks on the first match. The selected index agrees; traversal differs.
6. Lean concatenates the returned trace after the existing trace. C++ appends
   to its existing trace in place. The operation order agrees if the called
   routines emit the same operations.
7. Lean returns a stack and trace. C++ keeps the updated mapping and preserves
   data, mapping, and trace on a `Blocked` result. The Lean result type cannot
   express all those effects.

### Accepted divergence: equal-value permutation

These use a complete mapping, zero pending count, cursor zero, and identical
source and target stacks. Both satisfy `BuildBottomUpInvariant 0`.

| Input mapping | Checked Lean result | C++ result derived from its source |
| --- | --- | --- |
| Two copies of literal 7; exchange destinations 0 and 1 | Same stack, trace `[SWAP1]` | Same stack, empty trace. The equal-value normalization makes the permutation identity. |
| Eighteen copies of literal 7; exchange destinations 0 and 17 | `blocked 1` | Success, empty trace. The normalization again makes the permutation identity, so no reach test is needed. |

Lean witnesses were compiled using the actual `Checked.buildBottomUp`, with
separate proofs of the two input invariants. No C++ executable was run for this
review; the C++ columns follow directly from its equal-value normalization.
These witnesses establish a helper-input difference. They do not claim that
the current C++ planner constructs these particular mappings.

## Changes applied after review

1. **Inline the final permutation branch.** Done in this review. This follows
   the C++ `buildBottomUp` structure and removes the separate `finish` API.
2. **Match the C++ branch chain in `produce`.** The code calls state actions
   in an explicit `if / else if` chain, with the top-binding `ensure`
   immediately before the decrement. `copy.filter` combines copy presence
   and DUP reach in the second branch. Successful branches continue to the
   shared code without an early return.
3. **Make `generate`'s mutual exclusion explicit.** The SWAP branch now uses
   `else if` after the equality branch. The outer guarded block remains: it both
   matches C++ and supplies the bounds proof for the destination index.
4. **Move conversion proofs into named lemmas.** Private lemmas now hold the
   offset/depth equalities, positive SWAP depth, and top-index bounds used by
   `dup` and `swapWith`. The operation implementations remain local.

## Remaining interface scope

If C++ retry behavior is in scope, retain blocked offset and working state in
the result. If only admitted helper inputs are in scope, state that explicitly.
Exact behavior for all current Lean inputs is not C++ behavior: raw query
bounds, check order, assertion transport, and counter underflow differ.

## Validation limits

The existing 6,527 comparisons and exact equivalence theorems compare Lean
implementations. They do not run C++ or detect a shared permutation error.
The inlining change retains those tests and proofs, including negative tests
for an incomplete mapping and a size mismatch through the actual loop.

The old `build_bottom_up_correct` theorem still has its original `sorry`.
The experiment's equivalence and termination proofs do not use that theorem.
