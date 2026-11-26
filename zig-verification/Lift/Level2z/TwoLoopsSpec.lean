module

@[expose] public section

/-! The L3 specification of `l2zTwoLoops` (`Lift/LLVM/data/level2z/level2z.zig`): pure values only.

    export fn l2zTwoLoops(f: [*]u8, n: u64) callconv(.c) u64 {
        const s = f[0..n];
        var c: u64 = 0;
        for (s) |v| c +%= b(v != 0);
        for (s) |*v| v.* = 0;
        return c;
    }

The input is the old contents `xs` of the array (the `n` bytes at `f`), so its length is `n`. The
result is the count of the non-zero bytes of `xs` and the new contents of the array. -/

namespace Lift.Level2z.TwoLoopsSpec

/-- The old contents of the array, from the first byte on. -/
abbrev In := List (BitVec 8)

/-- The count of the bytes that are not 0, and the new contents: each byte is 0. -/
def run (x : In) : Option (BitVec 64 × List (BitVec 8)) :=
  some (BitVec.ofNat 64 (x.countP (· != 0)), List.replicate x.length 0)

/-- The contract: the length fits in the 64-bit argument `n`. -/
def C (x : In) : Prop := x.length < 2 ^ 64

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Level2z.TwoLoopsSpec
