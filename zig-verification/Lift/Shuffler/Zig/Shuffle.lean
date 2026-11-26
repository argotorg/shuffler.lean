module

public import Lift.Shuffler.Zig.Planner

@[expose] public section

/-!
The entry level of the Zig flat model (`docs/research/zig-flat-model-design-20261118.md`, units 1-3,
task K3i): `Input`, `Attempt`, `plan`, `commit`, `shuffle` (`solidity_shuffler_shuffle`, Z:1363, with
`Shuffle.run`, Z:1322-1359), `workspaceSize` (Z:1371) and `workspaceAlignment` (Z:1375).

Z is `Lift/LLVM/data/shuffler/src/shuffler.zig`.

`shuffle` has the Zig text of `Shuffle.plan` (Z:1267-1301), `Shuffle.commit` (Z:1304-1313) and
`Shuffle.run` (Z:1322-1359) over `plannerRun`. The spill bytes are the caller's buffer, which the
planner and `plan` change in place: in the model they are a function `Spills` that each step takes and
gives back. The content of the uninitialised workspace is an argument (D42): `plan` takes `us`, and
`shuffle` takes one `us` for each of the two plans.

The result `Out` holds what the C entry writes and the caller reads (Z:1363-1369 and
`ZigShuffler.cpp`:180-204): the status, the spill bytes, and for Done the `target_size` words of the
stack with their padding (`stack`), the trace with the padding of each operation, and `sources`. The
words of the workspace that no caller reads (`dropped`, the scratch, the other plan) are not in it.
The L3 `Spec.view` joins a stack word and its padding with `Slot.join`.
-/

namespace Lift.Shuffler.Zig

open FlatShuffler (Word StackSlot maxStackSize)
open FlatShuffler.Flat (get RunU offsets spillIsSpilled setByte boolByte isVariable)

/-- The spill buffer of the caller: the variable id `i` is spilled if its byte is not 0 (Z:159-190).
The buffer is a function of all ids; `Shuffle.run` reads and writes the ids of the variables of the
source and the target only. -/
abbrev Spills := BitVec 32 → BitVec 8

/-- The record `Shuffle` (Z:1241-1253) and the bytes that it points to: the source and the target with
the padding of each word (below the sizes), the spill buffer, `reachable_stack_depth` and
`spilling_allowed`. The workspace pointer is not a field: its content is the argument `us`. -/
structure Input where
  /-- `source[0 .. source_size)`, without the padding of a word. -/
  source : Vector StackSlot maxStackSize
  /-- The padding of each source word. -/
  sourcePad : Vector (BitVec 16) maxStackSize
  /-- `source_size`. -/
  sourceSize : Word
  /-- `target[0 .. target_size)`, without the padding of a word. -/
  target : Vector StackSlot maxStackSize
  /-- The padding of each target word. -/
  targetPad : Vector (BitVec 16) maxStackSize
  /-- `target_size`. -/
  targetSize : Word
  /-- `spills`: the bytes of the caller before the call. -/
  spills : Spills
  /-- `reachable_stack_depth`. -/
  reach : Word
  /-- `spilling_allowed`. -/
  allowed : Bool

/-- The planner of `Shuffle.run` (Z:1329-1340): the inputs of the planner (`Planner` of Z:988-1000). -/
def Input.toPlanner (x : Input) : Planner :=
  ⟨x.source, x.sourcePad, x.sourceSize, x.target, x.targetPad, x.targetSize, x.allowed, x.reach⟩

/-- A `Plan` of the workspace (Z:1210-1222) after `Shuffle.plan` that returned (Z:1267-1301). -/
structure Attempt where
  /-- `Planner.run` returned Done (the result of `plan`, Z:1267). -/
  done : Bool
  /-- `planner.saw_wildcard_copy` after the run (Z:997, read at Z:1346). -/
  saw : Bool
  /-- `data` with its padding, the trace and `sources` of the plan, and the planner state. -/
  ps : PSt
  /-- `result.spilled[i]` for `i < source_size` (Z:1290). -/
  spilled : List Bool
  /-- `result.spill_count` (Z:1291-1299). -/
  spillCount : Nat

/-- `Shuffle.plan` (Z:1267-1301): `dropped[0 .. source_size) = 0` (Z:1274; the model zeroes all of
`dropped`: the planner reads `dropped` below `source_size` only), `Planner.run` with `strategy = take`
(Z:1275-1286), the spilled flags of the source (Z:1290), and the restore (Z:1291-1299): a source
variable that the planner spilled and that was not spilled before `Shuffle.run` (`sp0`,
`spilled_before`, Z:1341-1343) gets the byte 0 and counts, once for each variable (its second copy sees
the byte 0). A failed assertion returns at once (Z:1280-1282), with the spill bytes as the planner
left them, and with no restore; an emission that runs out of fuel is `outOfFuel`. `sp` is the buffer at
the start of the plan, and the second component is the buffer at its end. The buffers `data`, `pad` and
`sources` of the plan have no defined content before the run (Z:1210-1222, 1228); the model starts them as
junk, 0 and `NONE`. A Done return has written `data` below `target_size` and `sources` below
`target_size`, and the caller reads no more. -/
def plan (x : Input) (sp0 sp : Spills) (take : Bool) (us : Nat → RunU) : Exit Attempt × Spills :=
  let src := (offsets x.sourceSize).map (get x.source)
  let ps : PSt :=
    { spills := sp, dropped := Vector.replicate maxStackSize 0, saw := false,
      data := Vector.replicate maxStackSize StackSlot.junk,
      pad := Vector.replicate maxStackSize 0, trace := [],
      sources := Vector.replicate maxStackSize FlatShuffler.Flat.NONE }
  let r := plannerRun x.toPlanner take ps us
  match r.1 with
  | .outOfFuel => (.outOfFuel, r.2.spills)
  | .assertionExit => (.assertionExit, r.2.spills)
  | .returned st =>
    let spilled := src.map (spillIsSpilled r.2.spills)
    let (sp', n) := src.foldl (fun (acc : Spills × Nat) s =>
      if !spillIsSpilled sp0 s && spillIsSpilled acc.1 s then (setByte acc.1 s.payload 0, acc.2 + 1)
      else acc) (r.2.spills, 0)
    (.returned ⟨st == .done, r.2.saw, r.2, spilled, n⟩, sp')

/-- `Shuffle.commit` (Z:1304-1313): each source variable gets the byte of the plan (`result.spilled[i]`,
0 or 1), in the source order (Z:1306-1308). The pointers to the plan (Z:1309-1312) are `Attempt.plan`. -/
def commit (x : Input) (sp : Spills) (a : Attempt) : Spills :=
  ((offsets x.sourceSize).zip a.spilled).foldl (fun sp (i, b) =>
    let s := get x.source i
    if isVariable s then setByte sp s.payload (boolByte b) else sp) sp

/-- What a Done plan hands out (Z:1309-1312) and the caller reads (`ZigShuffler.cpp`:180-204): the
`target_size` words of `stack`, each with its padding, the `trace_size` operations of the trace, each with
the padding of its slot, and the `target_size` entries of `sources` (`OptionalOffset` words, `NONE` is
`2^64 - 1`). -/
structure Plan where
  stack : List (StackSlot × BitVec 16)
  trace : List OpP
  sources : List Word

/-- The memory that a Done plan hands out, for `n = target_size`. -/
def Attempt.toPlan (a : Attempt) (n : Word) : Plan :=
  ⟨(offsets n).map fun i => (get a.ps.data i, get a.ps.pad i), a.ps.trace,
    (offsets n).map (get a.ps.sources)⟩

/-- The status that `shuffle` returns (Z:75, 1363-1369) with the plan after Done. -/
inductive Result where
  /-- Status 0. -/
  | done (p : Plan)
  /-- Status 1. -/
  | blocked
  /-- Status 2. -/
  | assertionFailed

/-- What `shuffle` writes and the caller reads: the result and the spill bytes after the call. -/
structure Out where
  result : Result
  spills : Spills

/-- `shuffle` (Z:1363) with `Shuffle.run` (Z:1322-1359). The checks `2 ≤ reach` and both sizes at most
`max_stack_size` come first (Z:1323-1325; status 2, the spill bytes as before). `plan` with `leave`
(Z:1346); if the planner saw no wildcard copy, Blocked or `commit` of that plan (Z:1347-1350); else
`plan` with `take` (Z:1352), Blocked if neither is done (Z:1354), and `commit` of `take` when
`!leave.done` or `take.done` and it has fewer spills, or as many and a shorter trace (Z:1355-1358; the
trace length is `trace_size`). `us₁` and `us₂` are the content of the scratch at the two plans. The
result is `none` only when an emission used its fuel (`Exit.outOfFuel`, design section 3.4). -/
def shuffle (x : Input) (us₁ us₂ : Nat → RunU) : Option Out :=
  if ¬(2 ≤ x.reach ∧ x.sourceSize ≤ 1024 ∧ x.targetSize ≤ 1024) then
    some ⟨.assertionFailed, x.spills⟩
  else
    match plan x x.spills x.spills false us₁ with
    | (.outOfFuel, _) => none
    | (.assertionExit, sp) => some ⟨.assertionFailed, sp⟩
    | (.returned leave, sp1) =>
      if !leave.saw then
        if !leave.done then some ⟨.blocked, sp1⟩
        else some ⟨.done (leave.toPlan x.targetSize), commit x sp1 leave⟩
      else match plan x x.spills sp1 true us₂ with
        | (.outOfFuel, _) => none
        | (.assertionExit, sp) => some ⟨.assertionFailed, sp⟩
        | (.returned take, sp2) =>
          if !leave.done && !take.done then some ⟨.blocked, sp2⟩
          else
            let useTake := !leave.done || (take.done && (take.spillCount < leave.spillCount ||
              (take.spillCount == leave.spillCount && take.ps.trace.length < leave.ps.trace.length)))
            let a := if useTake then take else leave
            some ⟨.done (a.toPlan x.targetSize), commit x sp2 a⟩

/-- `solidity_shuffler_workspaceSize` (Z:1371): `@sizeOf(Workspace)`, 357,672. The value is the `size` of
`shuffler.Workspace` in `Lift/LLVM/data/shuffler/types.json` (type 54) and the `movl $357672, %eax` of
`solidity_shuffler_workspaceSize` in `Lift/LLVM/data/shuffler/shuffler.s` (line 637). -/
def workspaceSize : Word := 357672

/-- `solidity_shuffler_workspaceAlignment` (Z:1375): `@alignOf(Workspace)`, 8 (`align` of type 54 in
`types.json`; `Lift.Pilot.AlignmentSpec.run`). -/
def workspaceAlignment : Word := 8

end Lift.Shuffler.Zig
