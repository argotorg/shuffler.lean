module

@[expose] public section

/-! The L3 specification of `toyFill` (`Lift/Toys/data/toy.zig`): pure values only.

    export fn toyFill(p: [*]u64, n: u64) callconv(.c) void {
        var i: u64 = 0;
        while (i < n) : (i += 1) p[i] = i;
    }

The input is the old contents of the array, so its length is `n`. The result is the new contents. -/

namespace Lift.Toys.FillSpec

/-- The old contents of the array, from the first element on. -/
abbrev In := List (BitVec 64)

/-- The new contents: element `i` is `i`. The code counts with a 64-bit register, so the length
must fit in 64 bits (see `C`). -/
def run (x : In) : Option (List (BitVec 64)) := some ((List.range x.length).map (BitVec.ofNat 64))

/-- The contract: the length fits in the 64-bit argument `n`. -/
def C (x : In) : Prop := x.length < 2 ^ 64

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Toys.FillSpec
