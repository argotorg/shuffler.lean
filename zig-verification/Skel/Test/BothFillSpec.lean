import Lift.Toys.FillStatement
import Lift.Pilot.Encode

/-! A test fixture of the suite `genupperloops` (task L3-U7): the L3 specification of a fill that returns a value, a result of
the kind `both`. The input and the code are those of `toyFill` (`Lift/Toys/data/toy.zig`): the loop writes `i` at the cell `i`
and leaves its count in `rax`. The result is the count in 16 bits (the low 16 bits of `rax`) and the new contents of the array.
The statement's `post` states the value and the array at the end. The module name is the namespace. -/

namespace Skel.Test.BothFillSpec

open Lift.P2.Total Lift.Trusted

/-- The contract of `toyFill`. -/
def C (x : Lift.Toys.FillSpec.In) : Prop := Lift.Toys.FillSpec.C x

/-- L3: the count in 16 bits, and the new contents of `toyFill`. -/
def run (x : Lift.Toys.FillSpec.In) : Option (BitVec 16 × List (BitVec 64)) :=
  (Lift.Toys.FillSpec.run x).map fun ys => (BitVec.ofNat 16 x.length, ys)

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

/-- At the return: the result field is the count of L3, and the array at `p` has the new contents. -/
def post (x : Lift.Toys.FillSpec.In) (p : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y.1 = [r] ∧ Mem.has policy m ⟨p, Encode.encode y.2, true⟩

end Skel.Test.BothFillSpec
