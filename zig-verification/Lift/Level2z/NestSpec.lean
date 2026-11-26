module

@[expose] public section

/-! The L3 specification of `l2zNest` (`Lift/LLVM/data/level2z/level2z.zig`): pure values only.

    export fn l2zNest(out: [*]u64, r: u64, c: u64) callconv(.c) void {
        for (0..r) |i| {
            for (0..c) |j| out[i *% c +% j] = i +% j;
        }
    }

The input is the old contents `out` of the array, the row count `r` and the column count `c`. The
result is the new contents. The function has no result value. -/

namespace Lift.Level2z.NestSpec

/-- The old contents of the array `out` from the first word on, `r` and `c`. -/
structure In where
  out : List (BitVec 64)
  r : BitVec 64
  c : BitVec 64

/-- The new contents. The index `i * c + j` with `i < r` and `j < c` covers the indices below
`r * c` once each, and the word at the index `k` is `i + j` with `i = k / c` and `j = k % c`; each
word at `r * c` or above is not written. -/
def run (x : In) : Option (List (BitVec 64)) :=
  some (x.out.mapIdx fun k old =>
    if k < x.r.toNat * x.c.toNat then BitVec.ofNat 64 (k / x.c.toNat + k % x.c.toNat) else old)

/-- The contract: the stores are in the array, so `r * c` (a product of naturals, with no wrap) is at
most the length of the array. The count of the words of the array is not an argument, so the length
has no other bound than the memory of the call. -/
def C (x : In) : Prop := x.r.toNat * x.c.toNat ≤ x.out.length

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Level2z.NestSpec
