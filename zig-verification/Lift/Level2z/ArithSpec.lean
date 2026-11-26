module

@[expose] public section

/-! The L3 specification of `l2zArith` (`Lift/LLVM/data/level2z/level2z.zig`, `export fn l2zArith(x:
u64, y: u64, z: u64) callconv(.c) u64`). -/

namespace Lift.Level2z.ArithSpec

/-- The Zig `@intFromBool`: 1 if `p`, else 0. -/
def bit (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

/-- L3: the value of `l2zArith(x, y, z)`, modulo `2^64`. `w` is the low 32 bits of `y - 1 + z - x`,
zero-extended to 64 bits in the sum. -/
def val (x y z : BitVec 64) : BitVec 64 :=
  let w : BitVec 32 := (y - 1 + z - x).setWidth 32
  12 * (x - y - 1) + bit (z ≠ 0) + bit (w ≠ 0) + w.setWidth 64 + (if y = 0 then 3 else 4)

/-- L3: the result of `l2zArith(x, y, z)`. -/
def run (x y z : BitVec 64) : Option (BitVec 64) := some (val x y z)

/-- The contract: no condition. -/
def C (_ _ _ : BitVec 64) : Prop := True

theorem total : ∀ x y z, C x y z → ∃ r, run x y z = some r := fun x y z _ => ⟨val x y z, rfl⟩

end Lift.Level2z.ArithSpec
