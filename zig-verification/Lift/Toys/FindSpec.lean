module

@[expose] public section

/-! The L3 specification of `toyFind` (`Lift/Toys/data/toy.zig`): pure values only.

    export fn toyFind(p: [*]const u64, n: u64, key: u64) callconv(.c) u64 {
        var i: u64 = 0;
        while (i < n) : (i += 1) { if (p[i] == key) return i; }
        return n;
    }

The input is the array `xs` (the `n` words at `p`) and the `key`. The result is the index of the
first word that equals `key`, or the length of `xs` if no word does. -/

namespace Lift.Toys.FindSpec

/-- The words of the array, and the key. -/
structure In where
  xs : List (BitVec 64)
  key : BitVec 64

/-- The index of the first `key` in `xs`, or the length of `xs` if there is none. -/
def run (x : In) : Option (BitVec 64) := some (BitVec.ofNat 64 (x.xs.idxOf x.key))

/-- The contract: the length fits in the 64-bit `n` argument. -/
def C (x : In) : Prop := x.xs.length < 2 ^ 64

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Toys.FindSpec
