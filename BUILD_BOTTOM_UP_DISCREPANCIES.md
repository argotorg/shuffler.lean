This file records the differences found between Lean `build_bottom_up` and C++
`Emission::buildBottomUp`, including the operations that they call. The review
covers behavior, input and output models, specifications, proofs, and build
coverage. A missing proof does not, by itself, establish a behavior error.

The implementations are not equivalent. In the examples below, stack positions
start at zero at the bottom. Lists run from bottom to top. Numbers denote literal
values unless stated otherwise. Permutations map source positions to destination
positions. C++ reach is 16 unless stated otherwise.

1. **Lean returns before it processes the last target offset.**

   Lean returns when `target_offset.val + 1 ≥ target.length`. Since the cursor has
   type `Fin target.length`, this condition holds at the last valid offset. C++
   processes that offset and exits only after the loop increment.

   For an empty source, target `[7]`, empty mapping, pending count `1`, and cursor
   `0`, every Lean precondition holds. The written Lean branch returns `[]` with
   no operations. C++ generates `7` and returns `[7]`.

   The same error occurs after earlier positions are complete. For current stack
   `[7]`, target `[7, 8]`, mapping `0 ↦ 0`, and pending count `1`, Lean skips offset
   zero and returns before it generates offset one. The prefix invariant does
   not imply that the last slot exists or is final.

   C++ checks that the stack has target length after the loop. Lean can return
   with one generation still pending. Changing the condition alone to
   `target_offset.val ≥ target.length` is insufficient: `Fin target.length`
   cannot represent that endpoint.

   Sources: [Lean definition](Shuffler/BuildBottomUp/Defs.lean), lines 24 and
   32–42; [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
   lines 480 and 615–616.

2. **Lean cannot accept an empty target.**

   The cursor parameter requires an inhabitant of `Fin 0` for an empty target.
   No such cursor exists. C++ can enter `buildBottomUp` with an empty target,
   skip the loop, check that the working stack is empty, and return success.

   Sources: [Lean definition](Shuffler/BuildBottomUp/Defs.lean), line 24;
   [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp), lines
   480 and 615–616.

3. **Lean `permute` omits the initial reassignment of equal values.**

   C++ groups equal values before it processes permutation cycles. Values
   already at a destination needed by their group stay there. The remaining
   positions take the remaining destinations in ascending order. Lean processes
   the supplied permutation of positions without this step.

   For stack `[7, 7, 9]` and a permutation that exchanges positions `0` and `1`,
   C++ changes the permutation to the identity and emits no operation. Lean emits
   `SWAP1, SWAP2, SWAP1`. The final values agree, but the traces differ.

   This can also change failure into success. For 18 copies of `7` and a
   permutation that exchanges positions `0` and `17`, C++ changes the permutation
   to the identity and succeeds. Lean attempts a swap at depth 17 and returns
   `Blocked 1`.

   Complete, value-consistent mappings can supply these permutations under the
   Lean input contract. These examples do not establish that the full C++
   planner constructs those exact entry states.

   Sources: [Lean call](Shuffler/BuildBottomUp/Defs.lean), lines 45–51;
   [Lean permutation](Shuffler/Permute/Defs.lean), lines 30–105;
   [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp), lines
   629–675.

4. **Lean `permute` omits assignment exchanges between equal values during execution.**

   C++ `exchangeWithTop` first compares the selected value with the top value.
   If they are equal, it exchanges their mapping destinations and emits no stack
   operation. It does this before the reach check. Lean checks reach and emits
   a physical swap even when the two values are equal.

   This difference remains even if the initial normalization from item 3 is
   added. For stack `[7, 7, 9, 9]` and permutation `[2, 3, 0, 1]`, C++ leaves the
   initial permutation unchanged. It later replaces the last physical swap with
   an assignment exchange. C++ emits three swaps; Lean emits four. Both produce
   `[9, 9, 7, 7]`.

   Sources: [Lean permutation](Shuffler/Permute/Defs.lean), lines 43–72 and
   85–102; [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
   lines 677–687.

5. **Lean blocked errors omit the blocked source offset.**

   C++ returns both the working-stack offset and the excess depth. Lean's
   `ShuffleErr.Blocked` contains only a natural number for the excess depth.
   Equal excess depths at different offsets do not supply the same information.

   C++ recovery uses the blocked offset to find retained slots above it and uses
   the excess to determine how many slots to drop. Lean cannot represent this
   recovery input.

   Sources: [Lean error type](Shuffler/Defs.lean), lines 17–18;
   [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp), lines
   276–281, 792–808, and 960–967.

6. **Lean discards the working state on failure.**

   C++ `Emission::Result` retains the working stack, mapping, and trace when an
   attempt fails. Lean returns only `Except.error`, so those intermediate values
   are absent from its result.

   This matters after earlier generation or swap operations, and after a mapping
   exchange that precedes a failed reach check. C++ recovery reads the current
   mapping along with the blocked offset and excess. The Lean error result
   cannot support that operation.

   Sources: [Lean result type](Shuffler/BuildBottomUp/Defs.lean), line 30;
   [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp), lines
   283–291, 323–331, 871, and 960–967.

7. **Two Lean failure branches have no defined excess-depth value.**

   The swap-up failure and the final swap-down failure use `.Blocked sorry`.
   These occurrences of `sorry` supply a natural-number result, not a proof.
   C++ computes `depthOf(position) - m_maxSwapDepth` in both cases.

   Even a comparison that ignores the missing offset cannot establish equal
   error values for these branches.

   Sources: [Lean definition](Shuffler/BuildBottomUp/Defs.lean), lines 155 and
   170; [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
   lines 591, 611, and 800–803.

8. **Lean fixes the reach limits; C++ accepts a configured reach.**

   Lean fixes maximum SWAP depth at 16 and maximum DUP depth at 15. C++ sets
   these limits from the requested reach: SWAP depth is the reach, and DUP depth
   is one less. Thus, the current Lean constants cover only C++ reach 16.

   The standard depth conventions agree. DUP16 reads zero-based depth 15;
   SWAP16 exchanges the top with zero-based depth 16. The discrepancy is the
   missing parameter, not an instruction-number conversion error.

   Sources: [Lean constants](Shuffler/Defs.lean), lines 13–15;
   [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp), lines
   830–839 and 1073–1082.

9. **Lean omits both C++ return-label slot kinds.**

   Lean represents variables, literals, and wildcards. C++ also represents
   `FunctionCallReturnLabel` and `FunctionReturnLabel`.

   A function-call return label can be freely generated. A function return label
   cannot be pushed or duplicated. Treating both kinds as ordinary Lean
   variables would not preserve these rules.

   Sources: [Lean value type](Shuffler/Defs.lean), lines 20–23;
   [C++ slot type](solidity/libyul/backends/evm/ssa/StackSlot.h), lines 77–82 and
   138–142; [C++ stack operations](solidity/libyul/backends/evm/ssa/Stack.h),
   lines 76–96.

10. **The correspondence between C++ slot equality and Lean value equality is unstated.**

    Lean compares literal words. C++ compares literal instruction identities as
    part of `StackSlot` equality. C++ deduplicates literals by value within an
    instruction store, which supports the intended correspondence for slots from
    that store. The model does not state this restriction or the correspondence
    between C++ instruction IDs and Lean variable IDs.

    This is a missing model relation. It does not establish an equality mismatch
    for valid slots from one store. The relation matters to copy searches,
    equal-value assignment exchanges, and permutation normalization.

    Sources: [Lean values](Shuffler/Defs.lean), lines 5–9 and 20–25;
    [C++ slot equality](solidity/libyul/backends/evm/ssa/StackSlot.h), line 119;
    [C++ literal allocation](solidity/libyul/backends/evm/ssa/InstructionStore.h),
    lines 193–209.

11. **The Lean assumptions do not connect mapping destinations to stack values.**

    `LoopInvariant` requires earlier positions to be final according to the
    mapping. Neither it nor `State` requires a mapped source to contain a value
    permitted at its destination.

    For source and current stack `[10, 20]`, target `[30, 40]`, identity mapping,
    pending count `0`, and cursor `0`, all current input assumptions hold. Both
    positions are final according to the mapping, but both values are wrong.
    The algorithm has no reason to replace them.

    C++'s mapping builder would not create that mapping for those literal
    targets. A relation needed for the Lean theorem is: for every mapped pair
    `s ↦ d`, either `target[d]` is junk or `stack[s] = target[d]`.

    This is a specification gap. It is not an additional loop-body difference
    on valid corresponding states.

    Sources: [Lean state and invariant](Shuffler/BuildBottomUp/State.lean),
    lines 12–38; [Lean theorem](Shuffler/BuildBottomUp/Defs.lean), lines 183–194;
    [C++ mapping builder](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
    lines 156–199 and 238–245.

12. **The Lean success theorem requires exact equality instead of wildcard compatibility.**

    C++ treats target junk slots as wildcards. For current stack `[10, 20]`,
    target `[Wildcard, 20]`, and identity mapping, C++ needs no operation. The
    result `[10, 20]` is compatible with the target but is not equal to it.

    Lean's `res = target` requirement rejects that valid result. A theorem for
    the C++ contract needs equal lengths and equality at each non-junk target
    position. Exact equality can be a separate theorem for targets without
    wildcards.

    Sources: [Lean theorem](Shuffler/BuildBottomUp/Defs.lean), lines 191–193;
    [C++ layout check](solidity/libyul/backends/evm/ssa/StackUtils.cpp), lines
    123–142.

13. **The Lean correctness theorem does not specify implementation equivalence.**

    The theorem states a property of successful output stacks and accepts every
    error through `.error _ => True`. It does not require the same success or
    failure decision as C++, the same error information, or the same emitted
    operations.

    The dependent `Trace` type constrains which operations can produce the
    returned stack. It does not establish equality with a C++ trace. Even a
    completed proof of the current theorem would not prove those additional
    properties. The theorem itself also remains `sorry`.

    Sources: [Lean theorem](Shuffler/BuildBottomUp/Defs.lean), lines 183–194;
    [Lean trace type](Shuffler/Defs.lean), lines 54–83.

14. **The later Lean branches omit proofs for C++ assertions and state preservation.**

    Missing proofs include the bound source being at or above the cursor, index
    bounds, equality of the selected copy, SWAP preconditions, the unmapped
    destination and availability arguments for current-target generation, and
    the invariants passed to later recursive calls.

    C++ checks several corresponding facts with assertions. Lean substitutes
    assumed proofs at these sites. The branch conditions and operation order
    largely match, but the current code does not prove that these assumptions
    follow from its inputs and preceding operations.

    Counter consistency and availability are already function inputs. The two
    early generation branches preserve them through `generate_preserves`; the
    later calls still use `sorry`. Thus, these facts are not absent everywhere.

    Sources: [Lean definition](Shuffler/BuildBottomUp/Defs.lean), lines 119–173;
    [Lean preservation theorem](Shuffler/BuildBottomUp/Theorems.lean), lines
    242–262; [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
    lines 555–612.

15. **The proved `produce` results do not yet state its full value, trace, and error behavior.**

    `produce_top` proves that the requested destination is mapped to the new top.
    It does not state that the value at that position equals the requested target
    value. The existing results cover stack length, mapping effects, counters,
    and preservation facts, but do not give the full correspondence with the
    C++ operation and error result.

    The inspected branch priority agrees for the supported slot kinds: push
    junk, otherwise duplicate a reachable copy, otherwise push or reload a
    generatable value, otherwise report an unreachable copy. This item records
    a proof gap rather than a demonstrated production-value error.

    Sources: [Lean production operation](Shuffler/BuildBottomUp/State.lean),
    lines 129–160; [Lean production theorems](Shuffler/BuildBottomUp/Theorems.lean),
    lines 4–77; [C++ production operation](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
    lines 388–404.

16. **The termination proof fails to build.**

    The measure `target.length - target_offset.val + pending_generations` is
    suitable for the intended progress: advance the cursor or decrease the
    pending count. However, the current proof does not discharge the obligations
    from all recursive branches.

    `lake build Shuffler.BuildBottomUp.Defs` reports an `omega` failure at line
    180 and further unsolved termination goals. The file therefore does not yet
    provide a successfully compiled definition. Behavior examples for the full
    function in this document follow from the written branches, not execution
    of a compiled `build_bottom_up`.

    Source: [Lean termination proof](Shuffler/BuildBottomUp/Defs.lean), lines
    175–181.

17. **The default build does not check the reviewed module.**

    `lake build` passes because the default root module imports the permutation
    theorems and mapping module, but does not import `BuildBottomUp.Defs`. A
    successful default build therefore does not establish that this function
    compiles.

    Tests that import `BuildBottomUp.Defs`, including `Tests/Generate.lean` and
    `Tests/BuildBottomUpBranches.lean`, cannot run against the failed module.

    Sources: [library root](Shuffler.lean); [build configuration](lakefile.toml);
    [generation tests](Tests/Generate.lean); [branch tests](Tests/BuildBottomUpBranches.lean).

18. **Lean excludes unavailable inputs that C++ rejects with an assertion.**

    Lean requires availability on the current stack for every target value. If
    production has neither a copy nor a way to generate a value, that assumption
    eliminates the branch through `False.elim`. C++ reaches an assertion instead.

    This is an input-contract difference, not a mismatch on inputs satisfying
    availability. A comparison with the full C++ pipeline must establish that
    its earlier phases preserve the required current-stack availability. The
    planner's initial availability assertion concerns the original source.

    Sources: [Lean availability and production](Shuffler/BuildBottomUp/State.lean),
    lines 73–75 and 129–157; [Lean function inputs](Shuffler/BuildBottomUp/Defs.lean),
    line 29; [C++ shuffler](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
    lines 400–401 and 848–857.

19. **Standalone production at a zero counter has different arithmetic.**

    Lean natural-number subtraction saturates at zero. C++ decrements an
    unsigned counter, which wraps at zero. The standalone Lean `produce` inputs
    do not require counter consistency, so this distinction exists outside the
    `build_bottom_up` contract.

    For an unmapped destination under `hpending`, the count is positive. Thus,
    this is not an additional underflow error in valid bottom-up states. The
    input relation and its preservation must retain that restriction.

    Sources: [Lean counter update](Shuffler/BuildBottomUp/State.lean), line 160;
    [Lean consistency assumption](Shuffler/BuildBottomUp/Defs.lean), line 28;
    [C++ counter update](solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
    line 403.

The review also found interface differences that need an explicit comparison
relation. C++ starts its private loop at zero after surplus removal and an
initial permutation. Lean accepts an arbitrary intermediate cursor and state.
On success, Lean returns a stack and trace; C++ retains its working mapping in
`Emission::Result` as well. These interfaces can be compared through a stated
relation and projection. Their different shapes alone do not prove a stack
behavior error.

Several details that can appear different have matching behavior under the
stated restrictions. Both implementations scan urgent destinations in ascending
order, select the first urgent destination, continue scanning for later blocked
copies, search for replacement copies strictly above the original source, and
revisit the same cursor after early generation. Their standard DUP and SWAP
depth conversions agree. Both prefer a reachable DUP over a literal push or
spill reload. Lean's `State.push` records a load for spilled variables, as C++
does. These are not additional discrepancies.

The explicit length guard before C++ `isFinal` must also be retained: it protects
the source-side vector lookup. Although Lean can prove that finality implies an
existing stack position, that logical implication does not make an unguarded
C++ lookup safe.

Validation from the review:

| Check | Result |
| --- | --- |
| `lake build` | Passed; did not build `BuildBottomUp.Defs` |
| `lake build Shuffler.BuildBottomUp.Defs` | Failed in the termination proof |
| `lake env lean Tests/BuildBottomUp.lean` | Passed; covers supporting operations |
| `lake env lean Tests/Permute.lean` | Passed |
| `lake env lean Tests/Generate.lean` | Failed to import the unbuilt `Defs` module |
| `lake env lean Tests/BuildBottomUpBranches.lean` | Failed to import the unbuilt `Defs` module |
| Temporary checks using production state and permutation definitions | Passed |
| C++ compilation attempt | Stopped at missing `fmt/format.h` |

The temporary checks established the stated input preconditions for the
missing-slot, wrong-value, and wildcard examples without `sorry`. They also
evaluated the production Lean permutation code for the equal-value examples.
They did not replace or execute a rewritten `build_bottom_up`. The temporary
checks are not part of this repository file. C++ outcomes in this document
follow from source inspection; no C++ differential test run was completed.
