module

public import Lift.Pilot.Slot

@[expose] public section

/-! The L3 specification of `SpillSet.add` (`shuffler.zig`, lines 170 to 174):

    noinline fn add(self: *const SpillSet, slot: StackSlot) AssertionError!void {
        try assert(slot.isVariable()); // Lean
        try assert(self.spilled[slot.payload] == 0); // can't spill a value twice
        self.spilled[slot.payload] = 1;
    }

The L3 inputs are the slot and the buffer `spilled`, which has one byte for each variable id.
The result is the error code of `AssertionError!void`: `0` for `ok` and `1` for `AssertionFailed`
(`pilot.s`: `movw $1, %ax` on the error path, `xorl %eax, %eax` on the ok path). -/

namespace Lift.Pilot.AddSpec

open Lift.Pilot

/-- L3: `add` of the slot `slot` on the buffer `buf`. The result is the error code and the buffer
after the call. A slot that is not a variable (`kind` 0 and `value_opcode` not 0) fails with the
buffer unchanged. A variable whose byte is not 0 fails with the buffer unchanged. Otherwise the
byte at the payload is set to 1 and the result is `ok`. The result is `none` outside `C`. -/
def run {n : Nat} (slot : Slot) (buf : Vector (BitVec 8) n) :
    Option (BitVec 16 × Vector (BitVec 8) n) :=
  if slot.kind = 0 ∧ slot.opcode ≠ 0 then
    if h : slot.payload.toNat < n then
      if buf[slot.payload.toNat]'h = 0 then
        some (0, buf.set slot.payload.toNat 1 h)
      else some (1, buf)
    else none
  else some (1, buf)

/-- The contract: when the slot is a variable, its payload is an index of the buffer. The code
reads and writes `spilled[payload]` with no test of the index (`pilot.s`, `movl %esi, %ecx` then
`cmpb $0, (%rdx,%rcx)`). The buffer has a byte for each variable id of the caller, so its length is
the bound. A slot that is not a variable reads no byte of the buffer, so it needs no bound. -/
def C {n : Nat} (buf : Vector (BitVec 8) n) (slot : Slot) : Prop :=
  (slot.kind = 0 ∧ slot.opcode ≠ 0) → slot.payload.toNat < buf.size

/-- Each slot and buffer in the contract: `run` gives a value. -/
theorem total {n : Nat} (buf : Vector (BitVec 8) n) (slot : Slot) (h : C buf slot) :
    ∃ y, run slot buf = some y := by
  unfold run
  split
  · rename_i hv
    split
    · rename_i hp
      split <;> exact ⟨_, rfl⟩
    · rename_i hp
      exact absurd (h hv) hp
  · exact ⟨_, rfl⟩

end Lift.Pilot.AddSpec
