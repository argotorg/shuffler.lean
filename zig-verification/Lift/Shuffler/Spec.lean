module

public import Lift.Shuffler.Zig.Shuffle
public import Lift.Pilot.Slot

@[expose] public section

/-!
The L3 specification `Shuffler.run` of the Zig entry function `shuffle` (`solidity_shuffler_shuffle`,
Z:1363), task K3j. Z is `Lift/LLVM/data/shuffler/src/shuffler.zig`.

`run` is the Zig flat model `Lift.Shuffler.Zig.shuffle` (`Lift/Shuffler/Zig/Shuffle.lean`) with the input
and the output in the types of the caller: `Lift.Pilot.Slot` (with the padding) for the words, lists for
the stacks and the spill buffer. `In` is what the caller gives; `Out` is what the entry writes and the
caller reads: the status, the spill buffer, and after Done the stack words, the trace and `sources`
(`Shuffle`, Z:1241-1253; the plan is written at Z:1309-1312).

Decisions: D39 (L3 is this `Shuffler.run`; `reach` is a parameter; status 2 is a normal result) and D42
(the model has the external slot type, `Lift.Pilot.Slot` is the type of the boundary; the content of the
uninitialised workspace is an argument; a loop that runs out of fuel gives `none`; `C` has no limit on
the reach and the sizes).
-/

namespace Lift.Shuffler.Spec

open Lift.Pilot (Slot)

/-- The inputs of `shuffle` as the caller gives them (the record `Shuffle` and the bytes it points to,
Z:1241-1253). The workspace pointer is not a field: its content is an argument of `run`. -/
structure In where
  /-- `source[0 .. source_size)`: the words of the source stack, deepest first, with their padding
  (`source_size` is the length). -/
  source : List Slot
  /-- `target[0 .. target_size)`: the words of the target stack, deepest first, with their padding
  (`target_size` is the length). -/
  target : List Slot
  /-- `spills`: the spill buffer before the call, one byte for each variable id; the id is spilled if its
  byte is not 0 (Z:159-166). -/
  spills : List (BitVec 8)
  /-- `reachable_stack_depth`. -/
  reach : BitVec 64
  /-- `spilling_allowed`. -/
  spillingAllowed : Bool

/-- A `ShuffleOp` of the trace (Z:144-152): the members that `record` writes (Z:283-286). -/
structure Op where
  /-- `kind`: swap 0, dup 1, pop 2, push 3, load 4. -/
  kind : BitVec 8
  /-- `depth`: the operand of a swap or a dup, else 0. -/
  depth : BitVec 8
  /-- `slot`: the word of a push or a load with its padding; the junk slot, with padding 0, for the
  other kinds. -/
  slot : Slot
  deriving DecidableEq

/-- What a plan hands out (Z:1309-1312). -/
structure Plan where
  /-- `stack[0 .. target_size)`: the stack after the trace, each word with its padding. -/
  stack : List Slot
  /-- `trace[0 .. trace_size)`: the operations that take the source to `stack`. -/
  trace : List Op
  /-- `sources[0 .. target_size)`: for each target offset the source offset that serves it, or
  `2^64 - 1` (`OptionalOffset.none`, Z:132) for a generated offset. -/
  sources : List (BitVec 64)
  deriving DecidableEq

/-- The status that `shuffle` returns (Z:75, 1363-1369), with the plan after Done. -/
inductive Result where
  /-- Status 0 with its plan. -/
  | done (p : Plan)
  /-- Status 1: neither wildcard strategy has a plan. -/
  | blocked
  /-- Status 2: a failed assertion of the Zig code (`yulAssert` of the C++). -/
  | assertionFailed
  deriving DecidableEq

/-- What `shuffle` writes and the caller reads: the result and the spill buffer after the call. -/
structure Out where
  /-- The status, and the plan for status 0. -/
  result : Result
  /-- The spill buffer after the call; its length is that of `In.spills`. -/
  spills : List (BitVec 8)
  deriving DecidableEq

/-- The Zig flat model input for `x`: the first 1,024 words of each list with `Slot.split` (the all-zero
slot after the list), the sizes as words, the spill buffer as a function of the 32-bit id (the byte 0
above the buffer: no input in `C` reads it). A list above 1,024 words is status 2 before any read
(Z:1324-1325). -/
def embed (x : In) : Zig.Input :=
  let word (l : List Slot) (i : Fin FlatShuffler.maxStackSize) := Zig.Slot.split (l.getD i default)
  { source := Vector.ofFn (word x.source · |>.1), sourcePad := Vector.ofFn (word x.source · |>.2),
    sourceSize := BitVec.ofNat 64 x.source.length,
    target := Vector.ofFn (word x.target · |>.1), targetPad := Vector.ofFn (word x.target · |>.2),
    targetSize := BitVec.ofNat 64 x.target.length,
    spills := fun i => x.spills.getD i.toNat 0, reach := x.reach, allowed := x.spillingAllowed }

/-- The L3 output of the model output `o` for the input `x`: `Slot.join` of each stack word with its
padding and of the slot of each trace operation, and the spill buffer as the byte of each 32-bit id
(the bytes of an input buffer above `2^32` are not addressed, so they stay). -/
def view (x : In) (o : Zig.Out) : Out where
  result :=
    match o.result with
    | .done p => .done ⟨p.stack.map Zig.Slot.join,
        p.trace.map fun t => ⟨t.op.kind, t.op.depth, Zig.Slot.join (t.op.slot, t.pad)⟩, p.sources⟩
    | .blocked => .blocked
    | .assertionFailed => .assertionFailed
  spills := x.spills.mapIdx fun k b => if k < 2 ^ 32 then o.spills (BitVec.ofNat 32 k) else b

/-- `Shuffler.run`: the Zig `shuffle` result for result. `none` only when an emission runs out of fuel
(D42, 2). `w₁` and `w₂` are the content of the scratch at the start of each attempt (in the machine: what
the earlier attempt or plan left there) for the first plan (`leave`) and the second plan (`take`): for each
attempt `k` of `Planner.run`, the content of its scratch arrays (D42, 4). The trusted statement quantifies
them with ∃ (decision D44). -/
def run (x : In) (w₁ w₂ : Nat → FlatShuffler.Flat.RunU) : Option Out :=
  (Zig.shuffle (embed x) w₁ w₂).map (view x)

/-- The contract: the spill buffer has a byte for each variable id of the source and the target. A slot
is a variable when its kind is 0 and its opcode is not 0 (`isVariable`, Z:108-110), and only a variable
indexes the buffer, by its payload (`isSpilled` Z:165-166, the loops of `Shuffle.run` Z:1342 and
`Shuffle.commit` Z:1307, the check of the target Z:1148). There is no limit on the reach (status 2
below 2), on the sizes (status 2 above 1,024), or on the kind, opcode and padding of other words. -/
def C (x : In) : Prop :=
  ∀ s ∈ x.source ++ x.target, s.kind = 0 → s.opcode ≠ 0 → s.payload.toNat < x.spills.length

end Lift.Shuffler.Spec
