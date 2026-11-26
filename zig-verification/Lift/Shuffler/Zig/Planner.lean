module

public import Lift.Shuffler.Zig.Emission
public import Lift.Shuffler.Ext.FlatPlan

@[expose] public section

/-!
The planner of the Zig flat model (`docs/research/zig-flat-model-design-20261118.md`, unit 4, task
K3h): `Planner`, `PSt`, `copyFrom` with the pads, the constructor `ctorP` of the emission of an
attempt, `runLoop` and `plannerRun` (`Planner.run`, Z:1131-1199).

Z is `Lift/LLVM/data/shuffler/src/shuffler.zig`. The external flat model (`FlatShuffler.Flat`,
`Lift/Shuffler/Ext/FlatPlan.lean`, FP) is the reference. Used unchanged from it: `Mapping` with `init`,
`copy` and `bind`, `Uninit`, `RunU`, `ResolveU`, `Builder`, `buildMapping` (the five phases of the
`MappingBuilder`, Z:354-448, with the seven units `mbMap`, `closestCopy`, `mapInPlace`,
`mapClosestCopies`, `mapWildcardSlotCopies`, `keepWildcardSlots`, `absorbSurplus`), `resolve` and its
loops, `classify`, `isDemanded`, `hasOtherRetainedCopy`, `isRetained`, `spillAdd` (`SpillSet.add`),
`targetsFrom`, `containsFrom`, `droppedCount`, `sourcesFrom`. These see only the `StackSlot` (no
padding), so no padding can change a decision of the planner.

Changed here (the copies):

- `Planner` and `PSt` (FP:189, 388): the pads of the source and the target beside the slots (D42),
  `reach` (the Zig `max_swap_depth`, Z:988, set by `Shuffle.run` Z:1338), `pad` beside `data`, and
  the trace with the padding of each operation (`OpP`).
- `copyFrom` (FP:446): the Zig copies a whole word, the padding too (Z:1171).
- `ctorP` (`FlatShuffler.Flat.ctorP`, FPo:74): `Emission.init` (Z:500-524) gets the reach (Z:1178), so
  the emission has `max_swap_depth` and `max_dup_depth` (Z:513-514), and the pads of the stack and of
  the target. The external constructor has none of these.
- `runLoop` (FP:459): the emission is `Lift.Shuffler.Zig.emissionRun`, the state is `PSt`, the result
  is `Exit` (an emission that runs out of fuel passes up as `outOfFuel`, design section 3.4), and
  `data`, `pad` and `trace` take the state of the emission.
- `plannerRun` (FP:484): the same text over the new `PSt`.

D42: the content of the uninitialised arrays is an argument (`us`, as in the external model), so the
model has no write-before-read statement for the scratch.
-/

namespace Lift.Shuffler.Zig

open FlatShuffler (Word StackSlot maxStackSize)
open FlatShuffler.Flat (NONE Status get put Mapping Uninit RunU Builder buildMapping resolve targetsFrom
  droppedCount droppedCount_le sub_lt_sub sourcesFrom offsets)

/-- The members of `Planner` that `run` does not change (Z:988-1000): the source and the target with
the padding of each word (below the sizes), `spilling_allowed` and `max_swap_depth`, the reach
(`Shuffle.run` sets it to `reachable_stack_depth`, Z:1338). The members that `run` changes are in
`PSt`. -/
structure Planner where
  /-- `source`, Z:989, without the padding of a word. -/
  source : Vector StackSlot maxStackSize
  /-- The padding of each source word. -/
  sourcePad : Vector (BitVec 16) maxStackSize
  /-- `source_size`, Z:990. -/
  sourceSize : Word
  /-- `target`, Z:991, without the padding of a word. -/
  target : Vector StackSlot maxStackSize
  /-- The padding of each target word. -/
  targetPad : Vector (BitVec 16) maxStackSize
  /-- `target_size`, Z:992. -/
  targetSize : Word
  /-- `spilling_allowed`, Z:994. -/
  allowed : Bool
  /-- `max_swap_depth`, Z:998. -/
  reach : Word

/-- The external `Planner` of the same slots: what the reused units read. -/
def Planner.toExt (pl : Planner) : FlatShuffler.Flat.Planner :=
  ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, pl.allowed⟩

/-- The state that `Planner.run` changes: the spill set (Z:993), `dropped` (Z:995),
`saw_wildcard_copy` (Z:997), and the caller's buffers `data` with its padding, the trace of the last
attempt and `sources`. Same as `FlatShuffler.Flat.PSt` (FP:388) with `pad` and the pads of the
trace. -/
structure PSt where
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) maxStackSize
  saw : Bool
  data : Vector StackSlot maxStackSize
  /-- The padding of each word of `data`. -/
  pad : Vector (BitVec 16) maxStackSize
  /-- `ops[0 .. trace_size)` of the last attempt, each with the padding of its slot. -/
  trace : List OpP
  sources : Vector Word maxStackSize

/-- The loop of `run` that copies the source to `data` from `i` on (Z:1171). Changed from
`FlatShuffler.Flat.copyFrom` (FP:446): `data[i] = self.sourceAt(i)` copies the whole word, so the
padding moves with the slot into `pad`. -/
def copyFrom (pl : Planner) (i : Word) (data : Vector StackSlot maxStackSize)
    (pad : Vector (BitVec 16) maxStackSize) :
    Vector StackSlot maxStackSize × Vector (BitVec 16) maxStackSize :=
  if h : i < pl.sourceSize then
    copyFrom pl (i + 1) (put data i (get pl.source i)) (put pad i (get pl.sourcePad i))
  else (data, pad)
termination_by (pl.sourceSize - i).toNat
decreasing_by bv_omega

/-- `Emission.init` (Z:500-524) with `Mapping.copyFrom` (the working mapping is a copy of the planned
one for `source_size` and `target_size`, the rest is the scratch content `u`): `data` holds the source
stack with its padding `pad`, `planned` is the planned mapping. Changed from `FlatShuffler.Flat.ctorP`
(FPo:74): `max_swap_depth` is the reach and `max_dup_depth` one less, wrapping for 0 (Z:513-514), the
target and the stack have their pads, and the trace has the new type. `pending_generations` counts the
target offsets without a position (Z:521-523); `blocked` is not initialised (Z:455), so it is the
scratch content. -/
def ctorP (pl : Planner) (data : Vector StackSlot maxStackSize) (pad : Vector (BitVec 16) maxStackSize)
    (planned : Mapping) (spills : BitVec 32 → BitVec 8) (u : Uninit) : St :=
  let M := Mapping.copy ⟨u.dest, u.pos⟩ planned pl.sourceSize pl.targetSize
  let st : St :=
    { target := pl.target, targetPad := pl.targetPad, targetSize := pl.targetSize, spills,
      maxSwapDepth := pl.reach, maxDupDepth := pl.reach - 1, data, pad, size := pl.sourceSize,
      trace := [], dest := M.dest, pos := M.pos, pend := 0,
      blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess }
  (offsets pl.targetSize).foldl
    (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st

/-- The `while (true)` loop of `Planner.run` (Z:1151-1198), with the content `us k` of the scratch
arrays of attempt `k`. An attempt resets the mapping (Z:1153) and builds it with the five phases
(Z:1164-1168), keeps `saw_wildcard_copy` (Z:1169), copies the source (Z:1171), runs the emission with
the reach (Z:1172-1181): Done writes `sources` (Z:1182) and returns; the trace is that of the
emission (Z:1183). Blocked resolves (Z:1192) and asserts that the number of dropped slots grew
(Z:1196); the next attempt runs on the new `dropped`. An assertion of the builder, the emission, or
`resolve` (Z:1186-1187, 1192) ends the run, and `resolve` with no victim is Blocked. Changed from
`FlatShuffler.Flat.runLoop` (FP:459): `copyFrom` with pads, `ctorP` with the reach, `emissionRun` of
the Zig model, `data`, `pad` and `trace` from the state of the emission, and `Exit` (`outOfFuel` of
the emission passes up). The loop ends: each attempt that continues drops at least one more slot
(the assertion otherwise), up to `source_size` slots. -/
def runLoop (pl : Planner) (take : Bool) (s : PSt) (us : Nat → RunU) : Exit Status × PSt :=
  let M := (us 0).mapping.init pl.sourceSize pl.targetSize
  match buildMapping ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, s.dropped, take⟩ M with
  | none => (.assertionExit, s)
  | some (M, saw) =>
    let c := copyFrom pl 0 s.data s.pad
    let s := { s with saw := s.saw || saw, data := c.1, pad := c.2 }
    let r := emissionRun M.pos (us 0).l (ctorP pl s.data s.pad M s.spills (us 0).u)
    let s := { s with data := r.2.data, pad := r.2.pad, trace := r.2.trace }
    if r.1 ≠ .blocked then
      if r.1 = .done then (r.1, { s with sources := sourcesFrom pl.targetSize 0 M s.sources })
      else (r.1, s)
    else
      let before := droppedCount pl.sourceSize s.dropped
      let q := resolve pl.toExt s.spills s.dropped M r.2.blockedOffset r.2.blockedExcess
        ⟨r.2.dest, r.2.pos⟩ r.2.size (us 0).r
      let s := { s with spills := q.2.1, dropped := q.2.2 }
      match q.1 with
      | .stuck => (.blocked, s)
      | .assertionExit => (.assertionExit, s)
      | .dropped =>
        if h : droppedCount pl.sourceSize s.dropped > before then runLoop pl take s fun k => us (k + 1)
        else (.assertionExit, s)
termination_by (pl.sourceSize - droppedCount pl.sourceSize s.dropped).toNat
decreasing_by exact sub_lt_sub (droppedCount_le _ _) (droppedCount_le _ _) h

/-- `Planner.run` (Z:1131-1199): `saw_wildcard_copy = false` (Z:1141), the check that each target
slot is a wildcard, can be generated, is on the source or is spilled (Z:1142-1150), then the loop.
Changed from `FlatShuffler.Flat.plannerRun` (FP:484): the same text over the new `PSt`. -/
def plannerRun (pl : Planner) (take : Bool) (s : PSt) (us : Nat → RunU) : Exit Status × PSt :=
  let s := { s with saw := false }
  if !targetsFrom pl.toExt s.spills 0 then (.assertionExit, s)
  else runLoop pl take s us

end Lift.Shuffler.Zig
