module

public import Lift.Level2z.ArithSpec

@[expose] public section

/-! The L3 specification of `l2zArgs8` (`Lift/LLVM/data/level2z/level2z.zig`, `export fn l2zArgs8(a,
bb, c, d, e, f, g, h: u64) callconv(.c) u64`). The arguments `g` and `h` are on the stack. -/

namespace Lift.Level2z.Args8Spec

/-- L3: the value of `l2zArgs8(a, ..., h)`, modulo `2^64`: `l2zArith(a + b, c + d, e) + ((f ^ g) - h)`. -/
def val (a b c d e f g h : BitVec 64) : BitVec 64 :=
  ArithSpec.val (a + b) (c + d) e + ((f ^^^ g) - h)

/-- L3: the result of `l2zArgs8(a, ..., h)`. -/
def run (a b c d e f g h : BitVec 64) : Option (BitVec 64) := some (val a b c d e f g h)

/-- The contract: no condition. -/
def C (_ _ _ _ _ _ _ _ : BitVec 64) : Prop := True

theorem total : ∀ a b c d e f g h, C a b c d e f g h → ∃ r, run a b c d e f g h = some r :=
  fun a b c d e f g h _ => ⟨val a b c d e f g h, rfl⟩

end Lift.Level2z.Args8Spec
