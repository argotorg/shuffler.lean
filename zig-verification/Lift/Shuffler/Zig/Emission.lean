module

public import Lift.Shuffler.Zig.Basic
public import Lift.Shuffler.Ext.FlatSpill
public import Lift.Shuffler.Ext.FlatPop
public import Lift.Shuffler.Ext.FlatSurplus
public import Lift.Shuffler.Ext.FlatLowest

@[expose] public section

/-!
The emission state and the stack operations of the Zig flat model
(`docs/research/zig-flat-model-design-20261118.md`, sections 3.1 and 5, tasks K3d to K3g).

Z is `Lift/LLVM/data/shuffler/src/shuffler.zig`. The external flat model (`FlatShuffler.Flat`, in
`Lift/Shuffler/Ext/`) is the reference. The functions here have its statements in its order, with
four changes that the Zig has and the external model does not:

- D2: the reach is a field of the state (`maxSwapDepth`, `maxDupDepth`, Z:484-486), not the
  constants 16 and 15.
- D3: `Stack` asserts its capacity: the stack has at most `maxStackSize` slots (Z:261, 268) and the
  trace at most `maxTraceSize` operations (Z:282). The machine code has these checks (the
  `shuffler.s` lines are in the doc comments). A failed check is `Exit.assertionExit`. The state of
  the exit is the state of the code at that point: a write before the check stays.
- D42: the slot type is the `StackSlot` of the external model, which has no padding. The padding of
  a slot is carried beside it: `St.pad` for the data, `St.targetPad` for the target, and `OpP.pad`
  for an operation of the trace. A function that moves a whole word (`stackSwap`, `stackPush`,
  `stackDup`) moves its padding. No decision reads a padding.
- The unit result is `Exit` in place of `ExecutionControl`. `Exit.outOfFuel` is given by `permute`
  (K3e) and `removeSurplus` (K3f): their loops (Z:709, 742) have no bound in the Zig, and the model
  gives them fuel (design section 3.4). The loop of `buildBottomUp` (K3g) is well-founded, with the
  measure of the external model (FM:624).

The functions that read no field of the state that changes keep the external text: `Flat.get`,
`Flat.put`, `Flat.NONE`, `Flat.initial`, `Flat.misplacedBelow`, `Op.swapW`, `Op.dupW`, `Op.push`,
`Op.pop`, `isJunk`, `canBeFreelyGenerated`, `spillIsSpilled`, and (K3f) `Locals`, `Scan` and `fill`
are used unchanged. All other
functions are copies over the new `St`.
-/

namespace Lift.Shuffler.Zig

open FlatShuffler (Word StackSlot Op maxStackSize FunctionReturnLabel isJunk canBeFreelyGenerated)
open FlatShuffler.Flat (Status NONE get put initial misplacedBelow Locals Scan fill)

/-- `Emission` (Z:478-499) with the members that the units of this module read or write. The
arrays have `maxStackSize` elements; `target` and `targetPad` are the target words below
`targetSize`. The members `planned_mapping` and `scratch` are not part of the state (the scratch
arrays are arguments of the units that use them). -/
structure St where
  /-- `target`, Z:479, without the padding of a word (`targetPad`). -/
  target : Vector StackSlot maxStackSize
  /-- The padding of each target word. -/
  targetPad : Vector (BitVec 16) maxStackSize
  /-- `target_size`, Z:480. -/
  targetSize : Word
  /-- `spills`, Z:482. -/
  spills : BitVec 32 → BitVec 8
  /-- `max_swap_depth`, Z:484: the reach. `Emission.init` (Z:513) sets it to the reach input. -/
  maxSwapDepth : Word
  /-- `max_dup_depth`, Z:486: `Emission.init` (Z:514) sets it to `maxSwapDepth - 1` (wraps for 0). -/
  maxDupDepth : Word
  /-- `stack.data`, Z:229, without the padding of a word (`pad`). -/
  data : Vector StackSlot maxStackSize
  /-- The padding of each word of `data`. -/
  pad : Vector (BitVec 16) maxStackSize
  /-- `stack.size`, Z:230. -/
  size : Word
  /-- `stack.trace[0 .. stack.trace_size)`, Z:231-232, each with the padding of its slot. -/
  trace : List OpP
  /-- `mapping.destination_of`, Z:180. -/
  dest : Vector Word maxStackSize
  /-- `mapping.position_of`, Z:181. -/
  pos : Vector Word maxStackSize
  /-- `pending_generations`, Z:490. -/
  pend : Word
  /-- `blocked.offset`, Z:452-456. -/
  blockedOffset : Word
  /-- `blocked.excess`. -/
  blockedExcess : Word

/-- A normal return of a unit that has no value, and the state at that point. -/
abbrev Outcome (α : Type) := Exit α × St

/-- A unit that returns `Status.done`. Pattern of the external `ExecutionControl.done`. -/
@[match_pattern] abbrev Exit.done : Exit Status := .returned .done

/-- A unit that returns `Status.blocked` (`error.Blocked`). -/
@[match_pattern] abbrev Exit.blocked : Exit Status := .returned .blocked

/-! ## `Stack` -/

/-- `Stack.record` (Z:281-288) with the trace capacity: `assert(trace_size < max_trace_size)`
(Z:282; `shuffler.s` 1211, 1443, 1481, 1992) fails at `maxTraceSize` operations, and then the trace
and the rest of the state stay as they are. The padding `pad` is the padding of the slot of the
operation: of the word that a push pushes, and 0 for a swap, a dup and a pop (their slot is
`.junk`, whose padding is 0, Z:94). New: the check (the external model has none) and `pad`. -/
def record (st : St) (op : Op) (pad : BitVec 16) : Outcome Status :=
  if st.trace.length < maxTraceSize then (.done, { st with trace := st.trace ++ [⟨op, pad⟩] })
  else (.assertionExit, st)

/-- `Stack.swap` (Z:252-257): the slot at `offset` and the top change places, with their padding
(Z:253-255), then `record` (Z:256) with the depth `size - 1 - offset` truncated to a byte. The
swap is done before the check of `record`: at a full trace the exit state has the slots swapped.
Same as `Flat.stackSwap` (FM:90) with the padding moved and the check of `record`. -/
def stackSwap (st : St) (offset : Word) : Outcome Status :=
  let slot := get st.data offset
  let slotPad := get st.pad offset
  let data := put st.data offset (get st.data (st.size - 1))
  let data := put data (st.size - 1) slot
  let pad := put st.pad offset (get st.pad (st.size - 1))
  let pad := put pad (st.size - 1) slotPad
  record { st with data, pad } (Op.swapW (st.size - 1 - offset)) 0

/-- `Stack.push` (Z:260-265): `assert(size < max_stack_size)` (Z:261; `shuffler.s` 1475), then the
word (`slot` with its padding `slotPad`) is written and the size grows (Z:262-263), then `record`
(Z:264) with a `Load` for a variable and a `Push` for another slot. Same as `Flat.stackPush` (FM:97)
with the padding moved and the two checks. At a full trace the exit state has the slot pushed. -/
def stackPush (st : St) (slot : StackSlot) (slotPad : BitVec 16) : Outcome Status :=
  if ¬st.size.toNat < maxStackSize then (.assertionExit, st)
  else
    record { st with data := put st.data st.size slot, pad := put st.pad st.size slotPad,
                     size := st.size + 1 } (Op.push slot) slotPad

/-- `Stack.dup` (Z:267-272): `assert(size < max_stack_size)` (Z:268; `shuffler.s` 1440), then
`record` (Z:269) with the depth `size - 1 - offset + 1` truncated to a byte, then the word at
`offset` with its padding is copied to the top and the size grows (Z:270-271). The record comes
first: at a full trace the exit state is the state before. Same as `Flat.stackDup` (FM:102) with
the padding moved and the two checks. -/
def stackDup (st : St) (offset : Word) : Outcome Status :=
  if ¬st.size.toNat < maxStackSize then (.assertionExit, st)
  else
    let r := record st (Op.dupW (st.size - 1 - offset + 1)) 0
    if r.1 ≠ .done then r
    else
      let st := r.2
      (.done, { st with data := put st.data st.size (get st.data offset),
                        pad := put st.pad st.size (get st.pad offset), size := st.size + 1 })

/-- `Stack.pop` (Z:274-278): `assert(size != 0)` (Z:275; `shuffler.s` 1989), then the size shrinks
(Z:276), then `record` (Z:277). At a full trace the exit state has the smaller size. Same as
`Flat.stackPop` (FPo:27) with the check of `record`. -/
def stackPop (st : St) : Outcome Status :=
  if st.size = 0 then (.assertionExit, st)
  else record { st with size := st.size - 1 } Op.pop 0

/-! ## `Mapping` -/

/-- `Mapping.pop` (Z:222-224): the position of the destination of `top`, if any, becomes none.
`dest[top]` stays. Same as `Flat.mappingPop` (FPo:32), over the new `St`. -/
def mappingPop (st : St) (top : Word) : St :=
  let destination := get st.dest top
  if destination ≠ NONE then { st with pos := put st.pos destination NONE } else st

/-- `Mapping.bind` (Z:206-209). Same as `Flat.bind` (FM:109), over the new `St`. -/
def bind (st : St) (pos destination : Word) : St :=
  { st with dest := put st.dest pos destination, pos := put st.pos destination pos }

/-- `Mapping.swapDestinations` (Z:212-218). Same as `Flat.swapDestinations` (FM:113), over the
new `St`. -/
def swapDestinations (st : St) (a b : Word) : St :=
  let destinationOfA := get st.dest a
  let dest := put st.dest a (get st.dest b)
  let dest := put dest b destinationOfA
  let pos := if get dest a ≠ NONE then put st.pos (get dest a) a else st.pos
  let pos := if get dest b ≠ NONE then put pos (get dest b) b else pos
  { st with dest, pos }

/-! ## Queries -/

/-- `Emission.isSpilled` (Z:572-574) with `SpillSet.isSpilled` (Z:165-167): the external
`spillIsSpilled` on the spill bytes of the state. -/
def isSpilled (st : St) (slot : StackSlot) : Bool :=
  FlatShuffler.Flat.spillIsSpilled st.spills slot

/-- `Emission.isFinal` (Z:536-538): the slot at `pos` is bound for `pos`. Same as `Flat.isFinal`
(FM:128). -/
def isFinal (st : St) (pos : Word) : Bool := get st.dest pos == pos

/-- `Emission.depthOf` (Z:541-543) with `Stack.offsetToDepth` (Z:248-250): wraps for an offset
above the stack. Same as `Flat.depthOf` (FM:131). -/
def depthOf (st : St) (pos : Word) : Word := st.size - 1 - pos

/-- `Emission.isSwapReachable` (Z:546-548). Changed: the bound is the field `maxSwapDepth`, the
Zig `max_swap_depth` (Z:484), where `Flat.isSwapReachable` (FM:134) has the constant 16. -/
def isSwapReachable (st : St) (pos : Word) : Bool := depthOf st pos ≤ st.maxSwapDepth

/-- `Emission.isDupReachable` (Z:551-553). Changed: the bound is the field `maxDupDepth`
(Z:486), where `Flat.isDupReachable` (FM:135) has the constant 15. -/
def isDupReachable (st : St) (pos : Word) : Bool := depthOf st pos ≤ st.maxDupDepth

/-- The loop of `Emission.shallowestCopyPosition` (Z:577-582) from `pos` down. Same as
`Flat.copyBelow` (FM:138), over the new `St` (the padding is not read: `eql`, Z:96-99, drops it). -/
def copyBelow (st : St) (slot : StackSlot) (pos : Word) : Word :=
  if h : pos = 0 then NONE
  else if get st.data (pos - 1) = slot then pos - 1
  else copyBelow st slot (pos - 1)
termination_by pos.toNat
decreasing_by bv_omega

/-- `Emission.shallowestCopyPosition` (Z:576-583). Same as `Flat.shallowestCopyPosition`
(FM:146), over the new `St`. -/
def shallowestCopyPosition (st : St) (slot : StackSlot) : Word :=
  copyBelow st slot st.size

/-! ## `block` -/

/-- `Emission.block` (Z:556-560): `assert(excess > 0)`, then the record of the blocked slot and
`error.Blocked`. Same as `Flat.block` (FM:177), over the new `St`. -/
def block (st : St) (position excess : Word) : Outcome Status :=
  if excess = 0 then (.assertionExit, st)
  else (.blocked, { st with blockedOffset := position, blockedExcess := excess })

/-- `Emission.blockSwapUnreachable` (Z:563-565). Changed: the field `maxSwapDepth` in place of the
constant (`Flat.blockSwapUnreachable`, FM:182). -/
def blockSwapUnreachable (st : St) (position : Word) : Outcome Status :=
  block st position (depthOf st position - st.maxSwapDepth)

/-- `Emission.blockDupUnreachable` (Z:568-570). Changed: the field `maxDupDepth` in place of the
constant (`Flat.blockDupUnreachable`, FM:184). -/
def blockDupUnreachable (st : St) (position : Word) : Outcome Status :=
  block st position (depthOf st position - st.maxDupDepth)

/-! ## Actions -/

/-- `Emission.swapWith` (Z:593-600): `pos < size` (Z:594), not final (Z:595), and
`1 ≤ depth ≤ max_swap_depth` (Z:597); then `Stack.swap` (Z:598, with the checks of `record`) and
`Mapping.swapDestinations` of `pos` and the top (Z:599). Changed from `Flat.swapWith` (FM:152): the
bound of the depth is the field `maxSwapDepth` (Z:484), not 16, and `stackSwap` can exit
(Z:282). -/
def swapWith (st : St) (pos : Word) : Outcome Status :=
  if ¬pos < st.size then (.assertionExit, st)
  else if isFinal st pos then (.assertionExit, st)
  else
    let depth := depthOf st pos
    if ¬(1 ≤ depth ∧ depth ≤ st.maxSwapDepth) then (.assertionExit, st)
    else
      let r := stackSwap st pos
      if r.1 ≠ .done then r
      else (.done, swapDestinations r.2 pos (r.2.size - 1))

/-- `Emission.pop` (Z:603-607): the top offset is read first (Z:604), then `Stack.pop` (Z:605,
with its checks), then `Mapping.pop` (Z:606). Changed from `Flat.pop` (FPo:37): `stackPop` can
exit at a full trace (Z:282). -/
def pop (st : St) : Outcome Status :=
  let top := st.size - 1
  let r := stackPop st
  if r.1 ≠ .done then r
  else (.done, mappingPop r.2 top)

/-- `Emission.push` (Z:609-614): `Stack.push` of the word `slot` with its padding `slotPad`
(Z:610, with its checks), `assert(positionOf(destination) == none)` (Z:612), then the top is bound
for `destination` (Z:613). The caller gives the padding of the word (the call sites in `produce`
push a target word, Z:630, 634). Changed from `Flat.push` (FM:163): the two checks of `stackPush`
(Z:261, 282), which can exit before the check of the destination, and the padding. -/
def push (st : St) (slot : StackSlot) (slotPad : BitVec 16) (destination : Word) : Outcome Status :=
  let r := stackPush st slot slotPad
  if r.1 ≠ .done then r
  else
    let st := r.2
    if get st.pos destination ≠ NONE then (.assertionExit, st)
    else (.done, bind st (st.size - 1) destination)

/-- `Emission.dup` (Z:616-623): `assert(!at(copy).isFunctionReturnLabel())` (Z:618), `Stack.dup`
(Z:619, with its checks), `assert(positionOf(destination) == none)` (Z:621), then the top is bound
for `destination` (Z:622). Changed from `Flat.dup` (FM:169): the two checks of `stackDup` (Z:268,
282) and the padding, which `stackDup` copies. `dup` reads no reach: `produce` checks
`isDupReachable` before it calls `dup` (Z:631). -/
def dup (st : St) (copy destination : Word) : Outcome Status :=
  if (get st.data copy).kind = FunctionReturnLabel then (.assertionExit, st)
  else
    let r := stackDup st copy
    if r.1 ≠ .done then r
    else
      let st := r.2
      if get st.pos destination ≠ NONE then (.assertionExit, st)
      else (.done, bind st (st.size - 1) destination)

/-! ## `produce` and `generate` -/

/-- `Emission.produce` (Z:626-643): the slot for `target_offset` (Z:627), its shallowest copy
(Z:628), then the first case that holds: a junk slot is pushed (Z:629-630); a copy in dup reach is
dup'ed (Z:631-632); a slot that can be generated or is spilled is pushed (Z:633-634); a copy out of
reach is Blocked (Z:635-636); else an assertion (Z:637-639). The pushes carry the padding of the
target word (Z:630, 634). Then `assert(positionOf(target_offset) == top)` (Z:641) and
`pending_generations -%= 1` (Z:642). Changed from `Flat.produce` (FM:188): the reach is the field
`maxDupDepth` (Z:631) through `isDupReachable`, `push` takes the padding `targetPad` of the target
word (design D42), and `push`, `dup` can exit at a capacity check (Z:261, 268, 282). -/
def produce (st : St) (targetOffset : Word) : Outcome Status :=
  let slot := get st.target targetOffset
  let slotPad := get st.targetPad targetOffset
  let copy := shallowestCopyPosition st slot
  let r :=
    if isJunk slot then push st slot slotPad targetOffset
    else if copy ≠ NONE ∧ isDupReachable st copy then dup st copy targetOffset
    else if canBeFreelyGenerated slot || isSpilled st slot then push st slot slotPad targetOffset
    else if copy ≠ NONE then blockDupUnreachable st copy
    else (.assertionExit, st)
  if r.1 ≠ .done then r
  else
    let st := r.2
    if get st.pos targetOffset ≠ st.size - 1 then (.assertionExit, st)
    else (.done, { st with pend := st.pend - 1 })

/-- `Emission.generate` (Z:648-664): `assert(target_offset < target_size)` (Z:649), `produce`
(Z:650), then, if the offset is strictly below the top and not final (Z:653): an equal slot at the
offset takes over the destination (Z:654-656); else a `swapWith` in swap reach (Z:657-659); else
the slot stays on top (Z:661). Changed from `Flat.generate` (FM:204): the reach is the field
`maxSwapDepth` through `isSwapReachable`, and the callees are the copies of this module. -/
def generate (st : St) (targetOffset : Word) : Outcome Status :=
  if ¬targetOffset < st.targetSize then (.assertionExit, st)
  else
    let r := produce st targetOffset
    if r.1 ≠ .done then r
    else
      let st := r.2
      if targetOffset + 1 < st.size ∧ ¬isFinal st targetOffset then
        if get st.data targetOffset = get st.data (st.size - 1) then
          (.done, swapDestinations st targetOffset (st.size - 1))
        else if isSwapReachable st targetOffset then swapWith st targetOffset
        else (.done, st)
      else (.done, st)

/-! ## `permute`

The scratch array `desired_by` (Z:674) starts from `initial`, as in `Flat.permute` (FM:362): the
Zig writes each element below the size before it reads it. The array `permutation` is an argument
and is not returned: the Zig changes it in place (Z:667) and no caller reads it after the call. -/

/-- The loop of `permute` that sets `desired_by` to none (Z:675), from `offset` on. Same as
`Flat.clearDesired` (FM:244), over the new `St`. -/
def clearDesired (st : St) (offset : Word) (desiredBy : Vector Word maxStackSize) :
    Vector Word maxStackSize :=
  if h : offset < st.size then clearDesired st (offset + 1) (put desiredBy offset NONE)
  else desiredBy
termination_by (st.size - offset).toNat
decreasing_by bv_omega

/-- The loop that marks the desired offsets of the group of `leader` (Z:680-682), from `pos` up to
`leader`. The compare `eql` drops the padding (Z:96-99). Same as `Flat.markDesired` (FM:252), over
the new `St`. -/
def markDesired (st : St) (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (permutation : Vector Word maxStackSize) (pos : Word) (desiredBy : Vector Word maxStackSize) :
    Vector Word maxStackSize :=
  if h : pos ≤ leader then
    let desiredBy :=
      if get st.data pos = slot then put desiredBy (get permutation pos) leader else desiredBy
    markDesired st leader hl slot permutation (pos + 1) desiredBy
  else desiredBy
termination_by (leader + 1 - pos).toNat
decreasing_by bv_omega

/-- The `while` of `permute` (Z:692-696): from `vacant` on, the first offset that the group of
`leader` desires and that does not hold `slot`, or the size. Same as `Flat.nextVacant` (FM:265),
over the new `St`. -/
def nextVacant (st : St) (leader : Word) (slot : StackSlot) (desiredBy : Vector Word maxStackSize)
    (vacant : Word) : Word :=
  if h : vacant < st.size ∧ ¬(get desiredBy vacant = leader ∧ ¬get st.data vacant = slot) then
    nextVacant st leader slot desiredBy (vacant + 1)
  else vacant
termination_by (st.size - vacant).toNat
decreasing_by bv_omega

/-- The loop that gives each slot of the group of `leader` an offset in `permutation`
(Z:686-701), from `pos` up to `leader`; none if no vacant offset is left (`assert`, Z:698). Same as
`Flat.placeGroup` (FM:275), over the new `St`. -/
def placeGroup (st : St) (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (desiredBy : Vector Word maxStackSize) (pos vacant : Word)
    (permutation : Vector Word maxStackSize) : Option (Vector Word maxStackSize) :=
  if h : pos ≤ leader then
    if ¬get st.data pos = slot then
      placeGroup st leader hl slot desiredBy (pos + 1) vacant permutation
    else if get desiredBy pos = leader then
      placeGroup st leader hl slot desiredBy (pos + 1) vacant (put permutation pos pos)
    else
      let vacant := nextVacant st leader slot desiredBy vacant
      if ¬vacant < st.size then none
      else placeGroup st leader hl slot desiredBy (pos + 1) (vacant + 1) (put permutation pos vacant)
  else some permutation
termination_by (leader + 1 - pos).toNat
decreasing_by all_goals bv_omega

/-- The `leader` loop (Z:676-702), from `leader` on; none if a group has no vacant offset left.
Same as `Flat.regroup` (FM:292), over the new `St`. -/
def regroup (st : St) (leader : Word) (permutation desiredBy : Vector Word maxStackSize) :
    Option (Vector Word maxStackSize) :=
  if h : leader < st.size then
    let slot := get st.data leader
    if shallowestCopyPosition st slot ≠ leader then regroup st (leader + 1) permutation desiredBy
    else
      let desiredBy := markDesired st leader h slot permutation 0 desiredBy
      match placeGroup st leader h slot desiredBy 0 0 permutation with
      | none => none
      | some permutation => regroup st (leader + 1) permutation desiredBy
  else some permutation
termination_by (st.size - leader).toNat
decreasing_by all_goals exact FlatShuffler.Flat.sub_succ_lt h

/-- How an iteration of the loop of `permute` ends: the next state and `permutation`, or `return`.
Same as `Flat.PNext` (FM:317) over the outcome of this module. -/
inductive PNext where
  | cont (st : St) (permutation : Vector Word maxStackSize)
  | ret (r : Outcome Status)

/-- The end of an iteration of the loop of `permute` (Z:726-736): the slot at `pos` and the top.
An equal slot takes over the destination (Z:726-727); else out of swap reach is Blocked
(Z:728-729); else `Stack.swap` (Z:731, with its checks, so it can exit) and `swapDestinations`
(Z:732); then the entries `pos` and `top` of `permutation` change places (Z:734-736). Changed from
`Flat.exchange` (FM:322): the reach is the field `maxSwapDepth`, and `stackSwap` can exit (Z:282). -/
def exchange (st : St) (top : Word) (permutation : Vector Word maxStackSize) (pos : Word) : PNext :=
  let r : Except (Outcome Status) St :=
    if get st.data pos = get st.data (st.size - 1) then .ok (swapDestinations st pos top)
    else if !isSwapReachable st pos then .error (blockSwapUnreachable st pos)
    else
      let s := stackSwap st pos
      if s.1 ≠ .done then .error s else .ok (swapDestinations s.2 pos top)
  match r with
  | .error r => .ret r
  | .ok st =>
    let desired := get permutation pos
    let permutation := put permutation pos (get permutation top)
    .cont st (put permutation top desired)

/-- An iteration of the loop of `permute` (Z:710-736). The scan for the shallowest misplaced slot
(Z:711-722) is `Flat.misplacedBelow` (FM:308), unchanged. Same as `Flat.permuteStep` (FM:335), over
the new `St`. -/
def permuteStep (st : St) (top : Word) (permutation : Vector Word maxStackSize) : PNext :=
  let pos := get permutation top
  if pos = top then
    let pos := misplacedBelow permutation top top
    if pos = top then .ret (.done, st)
    else exchange st top permutation pos
  else exchange st top permutation pos

/-- The loop of `permute` (Z:709-737) for at most `fuel` iterations. At fuel 0 the result is
`.outOfFuel` with the state at that point. The Zig loop has no bound; it ends after at most
`2 * size - 1` iterations if `permutation` is a permutation (Z:704-707). Changed from
`Flat.permuteLoop` (FM:347): fuel 0 gives `.outOfFuel`, not `.assertionExit` (design 3.4, D42: a
loop that does not end is not a return). -/
def permuteLoop (fuel : Nat) (st : St) (top : Word) (permutation : Vector Word maxStackSize) :
    Outcome Status :=
  match fuel with
  | 0 => (.outOfFuel, st)
  | fuel + 1 =>
    match permuteStep st top permutation with
    | .ret r => r
    | .cont st permutation => permuteLoop fuel st top permutation

/-- `Emission.permute` (Z:667-738): the slot at each offset `pos` goes to `permutation[pos]`. An
empty stack returns at once (Z:668). The regroup (Z:674-702) and the loop (Z:709-737) follow; the
fuel is `2 * size` (the source: `Flat.permute`, FM:355-362, and design 3.4). Changed from
`Flat.permute` (FM:359): the callees are the copies of this module, and the fuel exhaustion is
`.outOfFuel`. -/
def permute (st : St) (permutation : Vector Word maxStackSize) : Outcome Status :=
  if st.size = 0 then (.done, st)
  else
    let desiredBy := clearDesired st 0 initial
    match regroup st 0 permutation desiredBy with
    | none => (.assertionExit, st)
    | some permutation =>
      let top := st.size - 1
      permuteLoop (2 * st.size.toNat) st top permutation

/-! ## `removeSurplus` -/

/-- `Emission.isSurplus` (Z:531-533): the slot at `pos` has no destination. Same as
`Flat.isSurplus` (FS:22), over the new `St`. -/
def isSurplus (st : St) (pos : Word) : Bool := get st.dest pos == NONE

/-- The scan of `removeSurplus` from `pos` down (Z:747-754): the first surplus slot found is the
shallowest, the last reachable one the deepest. Changed from `Flat.surplusScan` (FS:25): the
reach is the field `maxSwapDepth` through `isSwapReachable` (Z:752). -/
def surplusScan (st : St) (pos shallowest deepest : Word) : Word × Word :=
  if h : pos = 0 then (shallowest, deepest)
  else if isSurplus st (pos - 1) then
    surplusScan st (pos - 1) (if shallowest = NONE then pos - 1 else shallowest)
      (if isSwapReachable st (pos - 1) then pos - 1 else deepest)
  else surplusScan st (pos - 1) shallowest deepest
termination_by pos.toNat
decreasing_by all_goals bv_omega

/-- The loop of `removeSurplus` that looks for an equal surplus slot, from `pos` down (Z:764-772):
the first surplus slot, from the top down, that is `eql` to the top (the padding is dropped, Z:96-99).
Same as `Flat.equalBelow` (FS:35), over the new `St`. -/
def equalBelow (st : St) (pos : Word) : Word :=
  if h : pos = 0 then NONE
  else if isSurplus st (pos - 1) ∧ get st.data (pos - 1) = get st.data (st.size - 1) then pos - 1
  else equalBelow st (pos - 1)
termination_by pos.toNat
decreasing_by bv_omega

/-- One pass of the loop of `removeSurplus` (Z:743-779): `.ok` with the state after the pop, or
`.error` with the result of `removeSurplus`. No surplus ends the loop with `.done` (Z:755); a surplus
and none in swap reach is Blocked (Z:757-758); a surplus that is the top needs no move (Z:761); an
equal surplus slot takes over the destination of the top (Z:773-774), else the deepest reachable
surplus swaps with the top (Z:776); then `pop` (Z:779). Changed from `Flat.surplusPass` (FS:43): the
callees are the copies of this module (`swapWith` and `pop` can exit at a capacity check, Z:282). -/
def surplusPass (st : St) : Except (Outcome Status) St :=
  let sc := surplusScan st st.size NONE NONE
  if sc.1 = NONE then .error (.done, st)
  else if sc.2 = NONE then .error (blockSwapUnreachable st sc.1)
  else
    let top := st.size - 1
    let r : Outcome Status :=
      if sc.1 = top then (.done, st)
      else if equalBelow st top ≠ NONE then (.done, swapDestinations st (equalBelow st top) top)
      else swapWith st sc.2
    if r.1 ≠ .done then .error r
    else
      let r := pop r.2
      if r.1 ≠ .done then .error r else .ok r.2

/-- The loop of `removeSurplus` (Z:742) for at most `fuel` passes. Each pass that does not return
pops one slot, so the fuel `size` is enough: at fuel 0 the stack is empty and the loop ends with
`.done`. A stack at fuel 0 gives `.outOfFuel` (no call of `removeSurplus` reaches it). Changed from
`Flat.surplusLoop` (FS:59): fuel 0 with a slot gives `.outOfFuel`, not `.done` (design 3.4, D42). -/
def surplusLoop (st : St) : Nat → Outcome Status
  | 0 => if st.size = 0 then (.done, st) else (.outOfFuel, st)
  | fuel + 1 =>
    if st.size = 0 then (.done, st)
    else match surplusPass st with
      | .error r => r
      | .ok st => surplusLoop st fuel

/-- `Emission.removeSurplus` (Z:741-781), with the fuel `size`. -/
def removeSurplus (st : St) : Outcome Status := surplusLoop st st.size.toNat

/-! ## `permuteAtLowestHeight`

The scratch arrays `permutation`, `holes` and `parked` (Z:788-791) are the argument `Locals`, as in
`Flat.permuteAtLowestHeight` (FL:71): the content of the workspace before the function writes it
(D42, point 4). The planned mapping is not part of the state: `planned` is its `position_of` array
(Z:495). -/

/-- The body of the first loop of `permuteAtLowestHeight` for the slot at `pos` and its destination
`destination` (Z:800-812), after the assertions. Same as `Flat.scanStep` (FL:39), over the new `St`. -/
def scanStep (planned : Vector Word maxStackSize) (st : St) (pos destination : Word) (sc : Scan) : Scan :=
  let isHole : Bool := get planned pos == NONE
  let isParked : Bool := decide (st.size ≤ destination)
  let sc := if !isParked then { sc with permutation := put sc.permutation pos destination } else sc
  let sc := if isParked && isHole then { sc with permutation := put sc.permutation pos pos } else sc
  let sc := if isParked && !isHole then
      { sc with parked := put sc.parked sc.parkedCount pos, parkedCount := sc.parkedCount + 1 }
    else sc
  if !isParked && isHole then
    { sc with holes := put sc.holes sc.holeCount pos, holeCount := sc.holeCount + 1 }
  else sc

/-- The first loop of `permuteAtLowestHeight` from `pos` on (Z:795-813); none if an assertion fails:
a slot with no destination (Z:797), a slot at or above the target size (Z:798). Same as `Flat.scan`
(FL:52), over the new `St`. -/
def scan (planned : Vector Word maxStackSize) (st : St) (pos : Word) (sc : Scan) : Option Scan :=
  if h : pos < st.size then
    let destination := get st.dest pos
    if destination = NONE then none
    else if ¬pos < st.targetSize then none
    else scan planned st (pos + 1) (scanStep planned st pos destination sc)
  else some sc
termination_by (st.size - pos).toNat
decreasing_by bv_omega

/-- `Emission.permuteAtLowestHeight` (Z:787-820): the first loop, `assert(parked_count ==
hole_count)` (Z:815), the second loop (`fill`, Z:817: `permutation[parked[i]] = holes[i]`), then
`permute` (Z:819). Changed from `Flat.permuteAtLowestHeight` (FL:71): the callees are the copies of
this module. -/
def permuteAtLowestHeight (planned : Vector Word maxStackSize) (l : Locals) (st : St) : Outcome Status :=
  match scan planned st 0 (Scan.init l) with
  | none => (.assertionExit, st)
  | some sc =>
    if sc.parkedCount ≠ sc.holeCount then (.assertionExit, st)
    else permute st (fill sc 0 sc.permutation)

/-! ## `isAvailable` and the checks of `run` -/

/-- `Emission.isAvailable` (Z:587-590): the target slot is free, spilled, or has a copy on the stack.
Same as `Flat.isAvailable` (FP:336), over the new `St`. -/
def isAvailable (st : St) (offset : Word) : Bool :=
  let slot := get st.target offset
  canBeFreelyGenerated slot || isSpilled st slot || shallowestCopyPosition st slot ≠ NONE

/-- The loop of `run` that counts the unmapped target offsets from `o` on (Z:962-965). Same as
`Flat.unmappedFrom` (FP:344), over the new `St`. -/
def unmappedFrom (st : St) (o count : Word) : Word :=
  if h : o < st.targetSize then
    unmappedFrom st (o + 1) (if get st.pos o = NONE then count + 1 else count)
  else count
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

/-- The loop of `run` that checks `isAvailable` from `o` on (Z:968-971). Same as
`Flat.availableFrom` (FP:352), over the new `St`. -/
def availableFrom (st : St) (o : Word) : Bool :=
  if h : o < st.targetSize then isAvailable st o && availableFrom st (o + 1) else true
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

/-- The loop of `run` that checks the function return labels from `o` on (Z:972-975). Same as
`Flat.labelsFrom` (FP:359), over the new `St`. -/
def labelsFrom (st : St) (o : Word) : Bool :=
  if h : o < st.targetSize then
    ((get st.target o).kind ≠ FunctionReturnLabel || get st.pos o ≠ NONE) && labelsFrom st (o + 1)
  else true
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

/-- The four checks of `Emission.run` between `permuteAtLowestHeight` and `buildBottomUp`
(Z:960-975), each an `assert`: the stack height and the pending generations sum to the target size,
the pending count is the count of unmapped target offsets, each target slot is available, and each
function return label of the target has a bound source. The state is not changed. -/
def runChecks (st : St) : Outcome Status :=
  if st.size + st.pend ≠ st.targetSize then (.assertionExit, st)
  else if unmappedFrom st 0 0 ≠ st.pend then (.assertionExit, st)
  else if !availableFrom st 0 then (.assertionExit, st)
  else if !labelsFrom st 0 then (.assertionExit, st)
  else (.done, st)

/-- `Emission.run` (Z:956-978) up to the call of `buildBottomUp` (Z:977; K3g): `removeSurplus`,
`permuteAtLowestHeight` and the checks. A result that is not `.done` is the result of `run`. Changed
from `Flat.emissionRun` (FP:364): the part before `buildBottomUp` only (`buildBottomUp` has the copy
of K3g); `planned` and the scratch `Locals` are arguments as there. -/
def emissionPrologue (planned : Vector Word maxStackSize) (l : Locals) (st : St) : Outcome Status :=
  let r := removeSurplus st
  if r.1 ≠ .done then r else
  let r := permuteAtLowestHeight planned l r.2
  if r.1 ≠ .done then r else
  runChecks r.2

/-! ## `buildBottomUp`

The scratch array `permutation` of the final permutation (Z:838) starts from `initial`, as in
`Flat.permuteMapping` (FM:372). The content of the workspace there does not change a result: the
Zig writes each element below the size (Z:839-841) before the call of `permute` (Z:843), and
`permute` reads `permutation` only below the size: at `pos ≤ leader < size` (Z:681), at the top
(Z:710), at `candidate < top` (Z:716), and at a value that the regroup wrote below the size
(Z:689, 699, with `vacant < size` from Z:698) or a swap of two such values (Z:734-736). An exit at
Z:840 returns before any read. -/

/-- The loop of the final permutation that reads the destinations into `permutation` (Z:839-841),
from `pos` on; none if a slot has no destination (Z:840). Same as `Flat.readDestinations` (FM:233),
over the new `St`. -/
def readDestinations (st : St) (pos : Word) (permutation : Vector Word maxStackSize) :
    Option (Vector Word maxStackSize) :=
  if h : pos < st.size then
    let destination := get st.dest pos
    if destination = NONE then none
    else readDestinations st (pos + 1) (put permutation pos destination)
  else some permutation
termination_by (st.size - pos).toNat
decreasing_by bv_omega

/-- The final permutation of `buildBottomUp` (Z:838-843): the destinations into `permutation`, then
`permute`. Same as `Flat.permuteMapping` (FM:372), with the `permute` of this module. -/
def permuteMapping (st : St) : Outcome Status :=
  match readDestinations st 0 initial with
  | none => (.assertionExit, st)
  | some permutation => permute st permutation

/-- The `urgent_to_dup` loop of `buildBottomUp` (Z:849-864) from `offset` on, with the value of
`urgent_to_dup` so far, or the result of `blockDupUnreachable` (Z:855). Changed from
`Flat.urgentFrom` (FM:381): the depth of an urgent copy is the field `maxDupDepth` (Z:857), not 15,
and the reach is the field through `isDupReachable` (Z:855). -/
def urgentFrom (st : St) (targetOffset offset urgentToDup : Word) : Except (Outcome Status) Word :=
  if h : offset < st.targetSize then
    if get st.pos offset ≠ NONE then urgentFrom st targetOffset (offset + 1) urgentToDup
    else
      let slot := get st.target offset
      if isJunk slot || canBeFreelyGenerated slot || isSpilled st slot then
        urgentFrom st targetOffset (offset + 1) urgentToDup
      else
        let sourceCopy := shallowestCopyPosition st slot
        if sourceCopy ≠ NONE then
          if !isDupReachable st sourceCopy then .error (blockDupUnreachable st sourceCopy)
          else urgentFrom st targetOffset (offset + 1)
            (if depthOf st sourceCopy = st.maxDupDepth ∧ sourceCopy ≠ targetOffset ∧ urgentToDup = NONE
              then offset else urgentToDup)
        else urgentFrom st targetOffset (offset + 1) urgentToDup
  else .ok urgentToDup
termination_by (st.targetSize - offset).toNat
decreasing_by all_goals bv_omega

/-- The `candidate` loop of `buildBottomUp` (Z:909-915): the shallowest copy of `slot` from
`candidate` down to above `source` that is not final, or `source`. The compare `eql` drops the
padding (Z:96-99). Same as `Flat.candidateFrom` (FM:402), over the new `St`. -/
def candidateFrom (st : St) (slot : StackSlot) (source candidate : Word) : Word :=
  if h : candidate > source then
    if get st.data candidate = slot ∧ !isFinal st candidate then candidate
    else candidateFrom st slot source (candidate - 1)
  else source
termination_by candidate.toNat
decreasing_by bv_omega

/-- How an iteration of the loop of `buildBottomUp` ends: `continue` with the value of
`target_offset` (before the increment of Z:830), or `return`. Same as `Flat.Next` (FM:412) over the
outcome of this module. -/
inductive Next where
  | cont (st : St) (targetOffset : Word)
  | ret (r : Outcome Status)

/-- The end of an iteration (Z:943-948): the top swaps down into `targetOffset`, if it is not the
top. Changed from `Flat.placeTop` (FM:417): the reach is the field `maxSwapDepth` (Z:946), and
`swapWith` can exit (Z:282). -/
def placeTop (st : St) (targetOffset : Word) : Next :=
  if ¬targetOffset < st.size then .ret (.assertionExit, st)
  else if isFinal st targetOffset then .ret (.assertionExit, st)
  else if targetOffset ≠ st.size - 1 then
    if !isSwapReachable st targetOffset then .ret (blockSwapUnreachable st targetOffset)
    else
      let r := swapWith st targetOffset
      if r.1 ≠ .done then .ret r else .cont r.2 targetOffset
  else .cont st targetOffset

/-- The branch for an offset that a slot is bound for (Z:895-931), then `placeTop`. Changed from
`Flat.bound` (FM:428): the reach is the field `maxSwapDepth` (Z:929), and `swapWith` can exit
(Z:282). -/
def bound (st : St) (targetOffset : Word) : Next :=
  let boundForTarget := get st.pos targetOffset
  if ¬(boundForTarget ≠ NONE ∧ boundForTarget ≥ targetOffset) then .ret (.assertionExit, st)
  else
    let sourceForTargetOffset := boundForTarget
    let slot := get st.data sourceForTargetOffset
    let pos :=
      if get st.data targetOffset = slot then targetOffset
      else candidateFrom st slot sourceForTargetOffset (st.size - 1)
    if get st.data pos ≠ get st.data sourceForTargetOffset then .ret (.assertionExit, st)
    else
      let st := swapDestinations st pos sourceForTargetOffset
      if pos = targetOffset then .cont st targetOffset
      else if pos ≠ st.size - 1 then
        if !isSwapReachable st pos then .ret (blockSwapUnreachable st pos)
        else
          let r := swapWith st pos
          if r.1 ≠ .done then .ret r else placeTop r.2 targetOffset
      else placeTop st targetOffset

/-- An iteration of the loop of `buildBottomUp` (Z:831-948), for `targetOffset < target_size`: a
final offset continues (Z:832); with nothing pending the final permutation (Z:835-844); else the
urgent dup (Z:866-876), the generation at the source top (Z:880-892), the bound slot (Z:895-931) or
the generation at the offset (Z:934-939). A generation that revisits the offset continues with
`targetOffset - 1` (Z:873, 890: `-%= 1`). Changed from `Flat.body` (FM:449): the swap reach in the
two tests is the field `maxSwapDepth` (Z:869, 885), not 16, and the callees are the copies of this
module. -/
def body (st : St) (targetOffset : Word) : Next :=
  if targetOffset < st.size ∧ isFinal st targetOffset then .cont st targetOffset
  else if st.pend = 0 then
    if st.size ≠ st.targetSize then .ret (.assertionExit, st)
    else .ret (permuteMapping st)
  else match urgentFrom st targetOffset targetOffset NONE with
  | .error r => .ret r
  | .ok urgentToDup =>
    if urgentToDup ≠ NONE ∧ urgentToDup ≠ targetOffset ∧ st.size - targetOffset < st.maxSwapDepth then
      let r := generate st urgentToDup
      if r.1 ≠ .done then .ret r else .cont r.2 (targetOffset - 1)
    else
      let sourceTop := st.size
      if urgentToDup = NONE ∧ sourceTop > targetOffset ∧ sourceTop < st.targetSize ∧
          get st.pos sourceTop = NONE ∧ sourceTop - targetOffset < st.maxSwapDepth then
        let r := generate st sourceTop
        if r.1 ≠ .done then .ret r else .cont r.2 (targetOffset - 1)
      else if get st.pos targetOffset ≠ NONE then bound st targetOffset
      else
        let r := generate st targetOffset
        if r.1 ≠ .done then .ret r
        else
          let st := r.2
          if ¬targetOffset < st.size then .ret (.assertionExit, st)
          else if isFinal st targetOffset then .cont st targetOffset
          else placeTop st targetOffset

/-! ### Termination

Adapted from FM:478-615. The units do not write `targetSize`, and only `produce` writes `pend`: an
iteration that continues keeps `targetOffset`, or generates a slot (so `pend` was not 0 and
decreases) and continues with `targetOffset - 1`. The changes: `Keep` goes through the capacity
checks of `record`, `stackSwap`, `stackPush` and `stackDup`. -/

/-- The state `st'` has the target size and the pending count of `st`. Same as `Flat.Keep`
(FM:491), over the new `St`. -/
def Keep (st st' : St) : Prop := st'.targetSize = st.targetSize ∧ st'.pend = st.pend

theorem record_keep (st : St) (op : Op) (p : BitVec 16) : Keep st (record st op p).2 := by
  unfold record; split <;> exact ⟨rfl, rfl⟩

theorem stackSwap_keep (st : St) (offset : Word) : Keep st (stackSwap st offset).2 :=
  record_keep _ _ _

theorem stackPush_keep (st : St) (slot : StackSlot) (p : BitVec 16) :
    Keep st (stackPush st slot p).2 := by
  unfold stackPush; split
  · exact ⟨rfl, rfl⟩
  · exact record_keep _ _ _

theorem stackDup_keep (st : St) (offset : Word) : Keep st (stackDup st offset).2 := by
  unfold stackDup; split
  · exact ⟨rfl, rfl⟩
  · have h := record_keep st (Op.dupW (st.size - 1 - offset + 1)) 0
    dsimp only
    split
    · exact h
    · exact h

theorem push_keep (st : St) (slot : StackSlot) (p : BitVec 16) (d : Word) :
    Keep st (push st slot p d).2 := by
  unfold push; dsimp only; repeat' split
  all_goals exact stackPush_keep _ _ _

theorem dup_keep (st : St) (copy d : Word) : Keep st (dup st copy d).2 := by
  unfold dup; dsimp only; repeat' split
  all_goals first | exact ⟨rfl, rfl⟩ | exact stackDup_keep _ _

theorem swapWith_keep (st : St) (pos : Word) : Keep st (swapWith st pos).2 := by
  unfold swapWith; dsimp only; repeat' split
  all_goals first | exact ⟨rfl, rfl⟩ | exact stackSwap_keep _ _

theorem block_keep (st : St) (pos excess : Word) : Keep st (block st pos excess).2 := by
  unfold block; split <;> exact ⟨rfl, rfl⟩

/-- The end of `produce` (Z:641-642), after the status of the action is `r.1`. Same as
`Flat.produce_tail` (FM:508), over the new `St`. -/
theorem produce_tail {st : St} {t : Word} {r : Outcome Status} (hr : Keep st r.2)
    (h : (if r.1 ≠ .done then r
          else if get r.2.pos t ≠ r.2.size - 1 then (.assertionExit, r.2)
          else (.done, { r.2 with pend := r.2.pend - 1 })).1 = .done) :
    (if r.1 ≠ .done then r
      else if get r.2.pos t ≠ r.2.size - 1 then (.assertionExit, r.2)
      else (.done, { r.2 with pend := r.2.pend - 1 })).2.targetSize = st.targetSize ∧
    (if r.1 ≠ .done then r
      else if get r.2.pos t ≠ r.2.size - 1 then (.assertionExit, r.2)
      else (.done, { r.2 with pend := r.2.pend - 1 })).2.pend = st.pend - 1 := by
  by_cases hs : r.1 = .done
  · rw [ite_eq_right (fun h' => h' hs)] at h ⊢
    by_cases hp : get r.2.pos t ≠ r.2.size - 1
    · rw [ite_eq_left hp] at h; cases h
    · rw [ite_eq_right hp]
      exact ⟨hr.1, congrArg (· - 1) hr.2⟩
  · rw [ite_eq_left hs] at h; exact absurd h hs

theorem produce_done {st : St} {t : Word} (h : (produce st t).1 = .done) :
    (produce st t).2.targetSize = st.targetSize ∧ (produce st t).2.pend = st.pend - 1 := by
  unfold produce at h ⊢
  refine produce_tail ?_ h
  repeat' split
  all_goals first
    | exact push_keep _ _ _ _
    | exact dup_keep _ _ _
    | exact block_keep _ _ _
    | exact ⟨rfl, rfl⟩

theorem generate_done {st : St} {t : Word} (h : (generate st t).1 = .done) :
    (generate st t).2.targetSize = st.targetSize ∧ (generate st t).2.pend = st.pend - 1 := by
  unfold generate at h ⊢
  by_cases h0 : ¬t < st.targetSize
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h ⊢
  by_cases h1 : (produce st t).1 = .done
  · have hp := produce_done h1
    rw [ite_eq_right (fun h' => h' h1)]
    dsimp only
    repeat' split
    all_goals first
      | exact hp
      | exact ⟨(swapWith_keep _ _).1.trans hp.1, (swapWith_keep _ _).2.trans hp.2⟩
  · rw [ite_eq_left h1] at h; exact absurd h h1

theorem placeTop_cont {st st' : St} {t t' : Word} (h : placeTop st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧ t' = t := by
  unfold placeTop at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (cases h; exact ⟨(swapWith_keep _ _).1, rfl⟩)

theorem bound_cont {st st' : St} {t t' : Word} (h : bound st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧ t' = t := by
  unfold bound at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨h1, h2⟩ := placeTop_cont h; exact ⟨h1.trans (swapWith_keep _ _).1, h2⟩)
    | (obtain ⟨h1, h2⟩ := placeTop_cont h; exact ⟨h1, h2⟩)

/-- Each iteration that continues keeps `targetOffset`, or generates a slot and decrements
`targetOffset`. Same as `Flat.body_cont` (FM:576), over the new `St`. -/
theorem body_cont {st st' : St} {t t' : Word} (h : body st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧
      (t' = t ∨ (t' = t - 1 ∧ st'.pend.toNat < st.pend.toNat)) := by
  unfold body at h
  split at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  split at h
  · split at h <;> cases h
  rename_i hp
  split at h
  · cases h
  try dsimp only at h
  split at h
  · split at h
    · cases h
    · cases h
      rename_i h1
      obtain ⟨g1, g2⟩ := generate_done (Decidable.not_not.mp h1)
      exact ⟨g1, .inr ⟨rfl, by rw [g2]; bv_omega⟩⟩
  split at h
  · split at h
    · cases h
    · cases h
      rename_i h1
      obtain ⟨g1, g2⟩ := generate_done (Decidable.not_not.mp h1)
      exact ⟨g1, .inr ⟨rfl, by rw [g2]; bv_omega⟩⟩
  split at h
  · exact ⟨(bound_cont h).1, .inl (bound_cont h).2⟩
  split at h
  · cases h
  rename_i h1
  obtain ⟨g1, -⟩ := generate_done (Decidable.not_not.mp h1)
  try dsimp only at h
  split at h
  · cases h
  split at h
  · cases h; exact ⟨g1, .inl rfl⟩
  · obtain ⟨k1, k2⟩ := placeTop_cont h
    exact ⟨k1.trans g1, .inl k2⟩

/-- The loop of `buildBottomUp` (Z:830-950) from `targetOffset`: `continue` increments the offset
with a wrap (Z:830: `+%= 1`); after the loop `assert(size == target_size)` (Z:950). Well-founded on
(`targetSize - targetOffset`, `pend`), lexicographic, as `Flat.loop` (FM:617-632). Same as
`Flat.loop`, with the `body` of this module. -/
def loop (st : St) (targetOffset : Word) : Outcome Status :=
  if targetOffset < st.targetSize then
    match h : body st targetOffset with
    | .ret r => r
    | .cont st' targetOffset' => loop st' (targetOffset' + 1)
  else if st.size ≠ st.targetSize then (.assertionExit, st)
  else (.done, st)
termination_by ((st.targetSize - targetOffset).toNat, st.pend.toNat)
decreasing_by
  obtain ⟨hn, h' | ⟨h', hp⟩⟩ := body_cont h
  · subst h'
    rw [hn]
    exact Prod.Lex.left _ _ (by bv_omega)
  · subst h'
    rw [hn, BitVec.sub_add_cancel]
    exact Prod.Lex.right _ hp

/-- `Emission.buildBottomUp` (Z:827-951): the loop from the offset 0 (Z:828). Same as
`Flat.buildBottomUp` (FM:635), with the `loop` of this module. -/
def buildBottomUp (st : St) : Outcome Status := loop st 0

/-! ## `Emission.run` -/

/-- `Emission.run` (Z:956-978): `emissionPrologue` (Z:958-975), then `buildBottomUp` (Z:977) if the
prologue is `.done`. Same as `Flat.emissionRun` (FP:364), over the new `St`: `planned` and the
scratch `Locals` of `permuteAtLowestHeight` are arguments as there. -/
def emissionRun (planned : Vector Word maxStackSize) (l : Locals) (st : St) : Outcome Status :=
  let r := emissionPrologue planned l st
  if r.1 ≠ .done then r else buildBottomUp r.2

end Lift.Shuffler.Zig
