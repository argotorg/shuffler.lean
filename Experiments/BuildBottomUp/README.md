# Build-bottom-up experiments

Use `Checked.lean` as the starting point for the next version. It keeps the C++
branch order, searches, early returns, and `continue` statements. Its loop body
has no tactic proofs, proof-carrying search results, or invariant updates.
The urgent-generation guard supplies a proof to `Option.get`. The final
permutation branch gets its length and mapping proofs from `requires`.
The supporting operations still use the existing `State`, `Mapping`, and `Trace`.

This directory contains the candidate implementation for production use. Its
checks and proofs use ordinary Lean definitions and theorems. It does not use
the experimental verification tactics or contract syntax. The existing
implementation in `Shuffler/BuildBottomUp` is unchanged.

The checked version now has a proof of equivalence to the old definition, plus
a separate proof that its outer loop has a finite execution. Both use the old
preconditions. See [Equivalence.lean](Equivalence.lean).

## What was tested

| Approach | File | Result |
| --- | --- | --- |
| Move proofs below the definition and group the four invariants | [Deferred.lean](Deferred.lean) | Compiles without `sorry`. Keeps the dependent `else` branches and recursive calls. |
| Checked helpers with separate assertion errors | [Checked.lean](Checked.lean) and [CheckedSupport.lean](CheckedSupport.lean) | The full algorithm compiles as a `while` loop with early returns. The final permutation checks and call are in the loop body. |
| Prove helper contracts and loop properties after the definition | [CheckedProofs.lean](CheckedProofs.lean) | Proves exact helper equivalence and that a loop over checked `generate` takes at most one iteration, preserves the invariant, and can fail only with `Blocked`. |

An attempted `rfl` proof of equality between the deferred version and the old
function failed. Grouping the invariant arguments changes the recursive term.
Both versions compile, but full equivalence is not proved by that experiment.

## Why checked helpers restore early returns

The old definition needs facts from branches that have already returned. It
also needs facts about the state after mutation and after a search. Its dependent
operations require those facts when Lean elaborates the program. An explicit
`else` keeps the required branch fact in scope.

Moving each operation into a checked helper keeps those proof arguments out of
the loop body:

```lean
state ← generate state urgent
continue
```

The helper checks its bounds, unbound destination, and availability. The local
`push`, `dup`, `produce`, `swapWith`, and `generate` implementations construct
states and traces directly. They share the core types with the old code but do
not call its operational `State` helpers. On valid
inputs, `generate_eq` proves that it returns exactly the result of
`State.generate`, with the old error embedded in the new error type. This
includes the complete state and trace. `swapWith_eq` proves the corresponding
statement for swaps.

In Lean these helpers are total functions into `Except`. They are partial
operations from the caller's point of view. An assertion error is distinct from
a stack reach error:

```lean
| blocked (excess : Nat)
| assertion (reason : String)
```

Assertion errors carry a message that describes the failed precondition.

The error case in `generate_spec` and `generateUntilBound_spec` is
`exists excess, err = .blocked excess`. It rules out every assertion error.
No helper error is converted to `Blocked`, discarded, or replaced by a default
value. The helper checks add computation; this experiment does not claim that
the compiler removes them.

`buildBottomUp_noAssertion` proves assertion exclusion for the full loop.
`buildBottomUpVerified` uses `restoreResult` to give the function its old
`Except ShuffleErr` result type. The assertion branch is eliminated with that
proof. `buildBottomUpVerified_eq` proves exact equality to the old function.
This wrapper takes the four old preconditions as one `BuildBottomUpInvariant`.

The C++ assertions about the produced top, bound source, selected value, final
placement, and final stack size use the local `ensure` function:

```lean
ensure (state.stack.length = target.length) "stack and target sizes differ"
```

These checks run at runtime. A false condition returns `.assertion reason`.
Tests cover invalid inputs, including a size mismatch when the cursor skips
the loop. The equivalence and termination proofs use the old preconditions
and prove that these checks succeed on admitted inputs.

`produce` joins its successful branches at `let next ← (do ...)`, checks that
the destination is bound to the new top, then decrements the pending count.
The parentheses keep the branch returns local to that action. A bare
`let next ← do ...` lets those returns leave the enclosing function and skip
the shared check and decrement. Tests cover the counter and binding after
each production path. `generate` uses an explicit `else if` to keep the
mapping-only exchange and physical swap mutually exclusive.

The offset/depth conversion proofs used by `dup` and `swapWith` are private
named lemmas in `CheckedSupport.lean`.

Bounds and operation preconditions are checked inside the support functions.
The local `requires` function returns the checked proof in Lean's built-in
`PLift` type. Helpers can use that proof without nested success branches:

```lean
let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
```

The proof is used to construct trace operations and mappings. A failed check
returns `.assertion reason`. This is an ordinary function, with no experimental
contract syntax. `ensure` calls `requires` and discards the proof when the caller
only needs the runtime check.

Conditions use propositions: `∧`, `∨`, `=`, `≠`, and `¬`.
`isSwapReachable` is a proposition with a `Decidable` instance. Standard
`Option.isSome` and `Option.isNone` queries still return `Bool`. The test runner
uses `decide` at the boundary where it needs a Boolean result.

## Helper and loop proofs

`generateUntilBound` is a small loop that calls the same checked `generate`
operation as the full translation. Ordinary Lean theorems establish:

- Each successful generation preserves `BuildBottomUpInvariant`, decreases
  `pending_generations`, and binds the destination.
- The loop either returns the already-bound state or calls `generate` once.
- Success preserves the invariant and leaves the destination bound.
- The only possible failure under the preconditions is `Blocked`.

The proofs use exact helper equivalence and the existing
`State.generate_preserves` and `State.generate_position` theorems. The loop
equation is proved by unfolding the actual loop. Axiom checks cover both the
checked algorithm and the loop proof.

## Comparison with C++

See [CppHelperAudit.md](CppHelperAudit.md) for the statement-by-statement helper
review. The final permutation's handling of equal slots is an accepted
divergence for now; it can emit extra swaps or report a blocked operation that
C++ avoids. The existing comparison tests compare Lean implementations, not
Lean against C++.

Compare `Checked.buildBottomUp` with `Emission::buildBottomUp` in
`solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp`, starting at line 478.

| C++ | Checked Lean |
| --- | --- |
| `for` loop increment | Increment at each advancing `continue` and at the loop tail |
| `--targetOffset; continue` | `continue`, with the cursor unchanged |
| `m_data`, `m_mapping`, `m_pendingGenerations` | Fields of local `state` |
| `generate(...)`, failure check | `state ← generate state ...` |
| `m_mapping.swapDestinations(...)` | `state ← swapDestinations state ...` |
| Reach check followed by `swapWith(...)` | The same check followed by checked `swapWith` |
| `return permute(...)` | Check the complete mapping, call `permute`, and return the stack and combined trace |
| `yulAssert(...)` | `ensure condition reason` or a checked helper precondition |

The urgent scan keeps scanning after it finds the first urgent destination.
A later unreachable copy must still block the operation. The equal-copy scan
stops at its first eligible copy. Both details have tests.

The urgent-generation `if` has the same three checks as C++: an urgent value
exists, it differs from the target offset, and generation preserves swap reach.
The named condition `h` supplies its first fact to `urgentToDup.get h.1`.
Given the presence check, `urgentToDup ≠ some targetOffset` compares the stored
offset with `targetOffset`.

The local mutation in Lean `do` notation is translated into value passing.
There is no shared mutable state. A `StateT` layer could remove some explicit
`state` arguments, but it is not needed for this result.

## Checks

The experiments are registered as a Lake library, so the editor can resolve
their imports. Run `lake build Experiments` to build all experiment modules.
The default `lake build` still builds `Shuffler`.

From the repository root:

```sh
Experiments/BuildBottomUp/check.sh
```

The script runs `lake build Experiments`, then checks the derived branch
fixtures. Together, the build and fixture checks cover:

- The existing branch fixtures against all three Lean implementations and the
  verified wrapper.
- Equality of result stacks, all trace operations and operands, and error excess.
- Every binary-literal source of length 0–3 and target of length up to 4,
  every injection from source positions to target positions, and every cursor
  from zero through the target length, subject to the old preconditions:
  6,527 admitted cases. The test also checks this count.
- An urgent copy followed by a blocked copy.
- Bounds, unavailable values, already-bound destinations, invalid swaps,
  and an incomplete final permutation.

The existing fixtures also cover urgent and new-top retries, equal-copy
selection, skipping final copies, blocked swaps, and the SWAP16 boundary.
Compiled modules are in Lake's build directory. Derived test files are
temporary files under `.lake`.

## Equivalence and termination proofs

For every input admitted by the old definition, `buildBottomUp_eq` proves:

```lean
buildBottomUp cursor state =
  liftResult (build_bottom_up cursor state hi hs hp ha)
```

`liftResult` changes only the error constructor from `ShuffleErr.Blocked` to
`Error.blocked`. The theorem compares the full dependent result, including the
exact `Trace`, rather than a list of observations. Thus the stack, operations,
operands, and blocked excess all agree. `buildBottomUpVerified_eq` removes even
the error-type difference.

The proof files have separate roles:

- [ScanEquivalence.lean](ScanEquivalence.lean) proves the two searches use the
  same order, selected position, early break, and error behavior. The urgent
  scan still checks later copies after it finds an urgent one.
- [FiniteExecution.lean](FiniteExecution.lean) extracts the actual loop body
  from `buildBottomUp`. Lean checks the extraction by equality. There is no
  separate copy of the algorithm. `LoopRuns` describes a finite sequence of
  calls to that body, ending in `done` or an error.
- [Equivalence.lean](Equivalence.lean) compares each branch under the old
  definition's well-founded induction. Every continuation uses the same cursor
  and complete `State`, including its mapping, counters, and trace.

The main induction is `buildWith_eq`. It accepts any loop interpreter that
satisfies the one-step equation. Applied to Lean's loop, it proves exact result
equality. Applied to the proof-only `loopOr` interpreter, it also proves finite
execution: this interpreter returns an assertion error if no finite execution
exists. Equality to the old result excludes that error. This argument uses the
old termination measure through `build_bottom_up.induct`; it does not infer
termination from equality of Lean values alone.

`buildBottomUp_terminates` states that a finite `LoopRuns` derivation exists.
`buildBottomUp_total` combines that derivation with exact equality of its output
to the old result. `buildBottomUp_noAssertion` excludes every added assertion
error. The axiom checks cover equality, termination, the combined theorem, and
the verified wrapper. They report only `propext`, `Classical.choice`, and
`Quot.sound`; none uses `sorryAx` or `native_decide`.

The old return type exposes a stack and trace on success, or a blocked excess
on error. It does not expose a final mapping or the working state on error.
The theorems compare everything that type returns. They do not add an output
state to the old interface.

The experiments preserve the existing model's limits: fixed stack reach, fewer
slot kinds, literal equality assumptions, and errors without the blocked offset
or working state. They do not prove equivalence to C++ across those differences.
The old `build_bottom_up_correct` theorem still contains its original `sorry`;
none of these experiments uses that theorem as evidence.
