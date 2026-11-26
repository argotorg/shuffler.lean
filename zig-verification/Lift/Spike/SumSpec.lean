module

@[expose] public section

/-! The L3 specification of `toySum` (`Lift/LLVM/data/toy/toy.zig`): pure values only.

    export fn toySum(p: [*]const u64, n: u64) callconv(.c) u64 {
        var s: u64 = 0;
        for (p[0..n]) |v| s +%= v;
        return s;
    }

The input is the array `xs` of `n` words. The result is the wrapping sum. -/

namespace Lift.Spike.SumSpec

/-- L3: the wrapping sum. -/
def run (xs : List (BitVec 64)) : Option (BitVec 64) := some xs.sum

/-- The contract: the inputs on which L3 must return. No bound on the length: the result does not depend on it, and `Mem.has` in `Fn.Entry` gives `p + 8 * length ≤ 2^64`. -/
def C (_ : List (BitVec 64)) : Prop := True

theorem total : ∀ xs, C xs → ∃ y, run xs = some y :=
  fun xs _ => ⟨xs.sum, rfl⟩

end Lift.Spike.SumSpec
