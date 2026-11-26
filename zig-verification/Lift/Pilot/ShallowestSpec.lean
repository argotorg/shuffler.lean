module

public import Lift.Pilot.Slot
public import Lift.Pilot.IsRetainedSpec

@[expose] public section

/-! The L3 specification of `Emission.shallowestCopyPosition` (`shuffler.zig`, `noinline fn
shallowestCopyPosition(self: *const Emission, slot: StackSlot) OptionalOffset`):

    var pos = self.stack.size;
    while (pos > 0) {
        pos -= 1;
        if (self.stack.at(pos).eql(slot)) return .some(pos);
    }
    return .none;

The L3 inputs are the 1024 slots of `stack.data`, the field `stack.size`, and the searched slot. The
assembly `.Lshuffler.Emission.shallowestCopyPosition` (`Lift/Level3/data/pilot.s`) reads `stack.size`
at `48(%rdi)`, then in each iteration `stack.data` at `40(%rdi)` and the slot at
`-8(%rdx,%rax,8)`, as 8-byte words. -/

namespace Lift.Pilot.ShallowestSpec

open Lift.Pilot

/-- `StackSlot.eql` (`shuffler.zig` line 97): equal `payload`, `kind` and `value_opcode`. The padding
is not compared. -/
def eql (a b : Slot) : Bool := a.payload = b.payload && a.kind = b.kind && a.opcode = b.opcode

/-- The memory that the function reads. `data` is `*self.stack.data`, the array `[1024]StackSlot`
(its slots at and above `size` are not read). `size` is the 64-bit field `self.stack.size`. `slot`
is the argument. -/
structure In where
  data : Vector Slot 1024
  size : BitVec 64
  slot : Slot

/-- L3: the position of the topmost slot of `data[0 .. size)` that is `eql` to `slot`, or
`OptionalOffset.none` (the word of all ones, `IsRetainedSpec.none64`) when there is none. The slots
of `data[0 .. size)` are paired with their positions and searched from the top, as the Zig loop goes
down from `size - 1`. The result is `none` (no value) only outside the contract, where `size` is
above 1024. -/
def run (x : In) : Option (BitVec 64) :=
  if x.size.toNat ≤ 1024 then
    some (match ((x.data.toList.take x.size.toNat).zipIdx.reverse.find? fun (s, _) => eql s x.slot) with
      | some (_, p) => BitVec.ofNat 64 p
      | none => Lift.Pilot.IsRetainedSpec.none64)
  else none

/-- The contract: `size` is at most 1024. `stack.at` is `self.data[0..self.size][offset]` and the
release build has no bounds check, so a larger `size` reads outside `[1024]StackSlot`. No other fact
is needed: the slots of `data` have no invariant (a slot is any 64-bit word). -/
def C (x : In) : Prop := x.size.toNat ≤ 1024

theorem total : ∀ x, C x → ∃ y, run x = some y := by
  intro x h
  have hx : x.size.toNat ≤ 1024 := h
  simp only [run, hx, ↓reduceIte, Option.some.injEq, exists_eq']

end Lift.Pilot.ShallowestSpec
