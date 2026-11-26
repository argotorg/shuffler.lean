module

@[expose] public section

/-! The L3 specification of `l2zExit3` (`Lift/LLVM/data/level2z/level2z.zig`): pure values only.

    export fn l2zExit3(p: [*]const u64, n: u64, key: u64, lim: u64) callconv(.c) u64 {
        for (p[0..n], 0..) |v, i| {
            if (v == key) return i;
            if (v > lim) return none;
        }
        return none;
    }

with `none = ~@as(u64, 0)`. The input is the array `xs` (the `n` words at `p`), the `key` and the
limit `lim`. The result is the index of the first word that equals `key` when no earlier word is
above `lim`; else `none` (the first word above `lim` is before every `key`, or the array ends). -/

namespace Lift.Level2z.Exit3Spec

/-- The words of the array, the key and the limit. -/
structure In where
  xs : List (BitVec 64)
  key : BitVec 64
  lim : BitVec 64

/-- `none` of the Zig source: the word of all ones. -/
def none64 : BitVec 64 := BitVec.allOnes 64

/-- The loop from the index `i` over the words `ws`: a word that is `key` gives its index, else a
word above `lim` gives `none64`, else the next word; the end of the list gives `none64`. -/
def loop (key lim : BitVec 64) : Nat → List (BitVec 64) → BitVec 64
  | _, [] => none64
  | i, v :: vs => if v = key then BitVec.ofNat 64 i else if lim < v then none64 else loop key lim (i + 1) vs

/-- The result of the loop from index 0 over all of `xs`. -/
def run (x : In) : Option (BitVec 64) := some (loop x.key x.lim 0 x.xs)

/-- The contract: the length fits in the 64-bit argument `n`. -/
def C (x : In) : Prop := x.xs.length < 2 ^ 64

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Level2z.Exit3Spec
