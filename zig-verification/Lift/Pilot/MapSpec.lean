module

public import Lift.Pilot.IsRetainedSpec

@[expose] public section

/-! The L3 specification of `MappingBuilder.map` (`shuffler.zig`, lines 354 to 359):

    noinline fn map(self: *MappingBuilder, source_offset: usize, target_offset: usize) AssertionError!void {
        try assert(self.mappable(source_offset));
        // slot already has a destination
        try assert(self.mapping.destinationOf(source_offset) == .none);
        // destination already bound to a slot
        try assert(self.mapping.positionOf(target_offset) == .none);
        self.mapping.bind(source_offset, target_offset);
    }

`mappable(s)` is `dropped[s] == 0` and `destinationOf(s) == .none` (line 326 to 328); `bind` sets
`destination_of[s] = some(t)` and `position_of[t] = some(s)` (line 206 to 208).

The L3 inputs are the array `dropped`, the two tables `destination_of` and `position_of` of the
`Mapping`, and the two indices. The result is the error code of `AssertionError!void` (`0` for `ok`,
`1` for `AssertionFailed`), then the two tables after the call. -/

namespace Lift.Pilot.MapSpec

open Lift.Pilot.IsRetainedSpec (none64)

/-- L3: `map` of the source offset `s` to the target offset `t`, with the array `dropped` and the
tables `dest` (`destination_of`) and `pos` (`position_of`). The result is the error code and the two
tables after the call. The code writes the tables only when the three assertions hold: the source is
not dropped, `dest[s]` is `none` and `pos[t]` is `none`. Otherwise the tables are unchanged and the
result is `AssertionFailed` (1). The result is `none` outside `C`. -/
def run (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024) (s t : Nat) :
    Option (BitVec 16 × Vector (BitVec 64) 1024 × Vector (BitVec 64) 1024) :=
  if h : s < 1024 ∧ t < 1024 then
    if dropped[s]'h.1 = 0 ∧ dest[s]'h.1 = none64 ∧ pos[t]'h.2 = none64 then
      some (0, dest.set s (BitVec.ofNat 64 t) h.1, pos.set t (BitVec.ofNat 64 s) h.2)
    else some (1, dest, pos)
  else none

/-- The contract: both indices are below 1024, the length of `dropped` and of the two tables
(`shuffler.zig` line 53, `max_stack_size = 1024`; line 180 `destination_of: [max_stack_size]`; line 306
`dropped: *const [max_stack_size]u8`). The code reads `dropped[s]`, `destination_of[s]` and
`position_of[t]` with no test of the index (`pilot.s`, `.Lshuffler.MappingBuilder.map`). No other fact
is needed: each entry of a table is a word, and every word is a valid `OptionalOffset`. -/
def C (s t : Nat) : Prop := s < 1024 ∧ t < 1024

/-- Each admitted input: `run` gives a value. -/
theorem total (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024) (s t : Nat)
    (h : C s t) : ∃ y, run dropped dest pos s t = some y := by
  unfold run
  split
  · split <;> exact ⟨_, rfl⟩
  · rename_i hn
    exact absurd h hn

end Lift.Pilot.MapSpec
