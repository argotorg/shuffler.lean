import Lift.Trusted.Call
import Lift.Trusted.Encode
import Lift.Pilot.Encode
import Lift.Pilot.Slot
import Lift.Shuffler.Zig.Emission

/-! The shared encoding of the flat state for the proposed internal statements (task INT-Q, W7 c). Each proposed statement
`Lift.Shuffler.Internal.Proposed.<N>Statement` takes its objects from this module, so that the statements of a caller and of
its callees put each field of the state at the same address with the same fields.

The layout is the record layout of `Lift/Shuffler/Statement.lean:17-31` applied to `Emission` (Z:478-499; Z is
`Lift/LLVM/data/shuffler/src/shuffler.zig`; 120 bytes, alignment 8; `Lift/Shuffler/Internal/PopStatement.lean` reads the same
offsets 48 to 72):

    offset  field (Z)                   L3 (`Lift.Shuffler.Zig.St`)
    0       target: [*]const StackSlot  the address `e.target` of the target words (`St.target`, `St.targetPad`)
    8       target_size                 `St.targetSize`
    16      spills.spilled: [*]u8       the address `e.spills` of the spill bytes (`St.spills`)
    24      max_swap_depth              `St.maxSwapDepth`
    32      max_dup_depth               `St.maxDupDepth`
    40      stack.data                  the address `e.data` of the stack words (`St.data`, `St.pad`)
    48      stack.size                  `St.size`
    56      stack.trace                 the address `e.trace` of the trace
    64      stack.trace_size            the length of `St.trace`
    72      mapping: *Mapping           the address `e.mapping` (`destination_of` at 0, `position_of` at 8192)
    80      pending_generations         `St.pend`
    88      blocked.offset              `St.blockedOffset`
    96      blocked.excess              `St.blockedExcess`

`Env` has the addresses, and the padding of a slot argument (the model does not read a padding, D42). Each object is a
function of `Env`, the state and the flag `w` (writable). -/

namespace Lift.Shuffler.Internal.Proposed.Layout

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Shuffler.Zig
open FlatShuffler (StackSlot Word maxStackSize)

/-- The addresses of a call: the `Emission` record `self`, and the arrays that its pointer fields name. `pad` is the padding of
a slot argument. -/
structure Env where
  self : BitVec 64
  target : BitVec 64
  spills : BitVec 64
  data : BitVec 64
  trace : BitVec 64
  mapping : BitVec 64
  pad : BitVec 16

/-- The 64-bit word of a slot with the padding `pad` (`Slot.word` of `Slot.join`). -/
def slotWord (s : StackSlot) (pad : BitVec 16) : BitVec 64 := (Slot.join (s, pad)).word

/-- A field is its own encoding: the statements give the result as `Encode.encode (result y) = [r]`, the form of the moved
statements (`Encode.encode y = [r]`). -/
instance : Encode Field where
  encode f := [f]
  decode
    | [f] => some f
    | _ => none

/-- One word field. -/
def word (v : BitVec 64) : List Field := [⟨.W64, v⟩]

/-! ## The fields of `Emission` -/

def targetPtr (e : Env) : Object := ⟨e.self, word e.target, false⟩
def targetSize (e : Env) (st : St) (w : Bool) : Object := ⟨e.self + 8, word st.targetSize, w⟩
def spillsPtr (e : Env) : Object := ⟨e.self + 16, word e.spills, false⟩
def maxSwapDepth (e : Env) (st : St) (w : Bool) : Object := ⟨e.self + 24, word st.maxSwapDepth, w⟩
def maxDupDepth (e : Env) (st : St) (w : Bool) : Object := ⟨e.self + 32, word st.maxDupDepth, w⟩
def dataPtr (e : Env) : Object := ⟨e.self + 40, word e.data, false⟩
def size (e : Env) (st : St) (w : Bool) : Object := ⟨e.self + 48, word st.size, w⟩
def tracePtr (e : Env) : Object := ⟨e.self + 56, word e.trace, false⟩
def traceSize (e : Env) (st : St) (w : Bool) : Object :=
  ⟨e.self + 64, word (BitVec.ofNat 64 st.trace.length), w⟩
def mappingPtr (e : Env) : Object := ⟨e.self + 72, word e.mapping, false⟩
def pend (e : Env) (st : St) (w : Bool) : Object := ⟨e.self + 80, word st.pend, w⟩
def blocked (e : Env) (st : St) (w : Bool) : Object :=
  ⟨e.self + 88, word st.blockedOffset ++ word st.blockedExcess, w⟩

/-! ## The arrays -/

/-- The stack words `[0, maxStackSize)` at `e.data`, with their padding. -/
def data (e : Env) (st : St) (w : Bool) : Object :=
  ⟨e.data, (List.range maxStackSize).map fun i => ⟨.W64, slotWord (st.data.toList.getD i default) (st.pad.toList.getD i 0)⟩, w⟩

/-- The target words `[0, maxStackSize)` at `e.target`, with their padding. -/
def target (e : Env) (st : St) : Object :=
  ⟨e.target, (List.range maxStackSize).map fun i =>
    ⟨.W64, slotWord (st.target.toList.getD i default) (st.targetPad.toList.getD i 0)⟩, false⟩

/-- The trace array at `e.trace`: `maxTraceSize` operations (`ShuffleOp`, 12 bytes each: the kind, the depth, two alignment
bytes, and the slot word at offset 4). Slot padding occupies bytes 10 and 11. This canonical array uses zero alignment
bytes. The operations after the last one of `st.trace` are the zero operation. A function that records
an operation writes it, so the trace is a writable object there. -/
def trace (e : Env) (st : St) (w : Bool) : Object :=
  ⟨e.trace, (List.range maxTraceSize).flatMap fun i =>
    let o := st.trace.getD i ⟨⟨0, 0, default⟩, 0⟩
    [⟨.W8, o.op.kind⟩, ⟨.W8, o.op.depth⟩, ⟨.W16, 0⟩, ⟨.W64, slotWord o.op.slot o.pad⟩], w⟩

/-- `mapping.destination_of` at `e.mapping`. -/
def dest (e : Env) (st : St) (w : Bool) : Object := ⟨e.mapping, st.dest.toList.map fun v => ⟨.W64, v⟩, w⟩

/-- `mapping.position_of` at `e.mapping + 8192`. -/
def pos (e : Env) (st : St) (w : Bool) : Object := ⟨e.mapping + 8192, st.pos.toList.map fun v => ⟨.W64, v⟩, w⟩

/-- The spill byte of the variable `id` at `e.spills + id` (`SpillSet.spilled[id]`, Z:165-167). -/
def spillByte (e : Env) (st : St) (id : BitVec 32) (w : Bool) : Object :=
  ⟨e.spills + id.setWidth 64, [⟨.W8, st.spills id⟩], w⟩

end Lift.Shuffler.Internal.Proposed.Layout
