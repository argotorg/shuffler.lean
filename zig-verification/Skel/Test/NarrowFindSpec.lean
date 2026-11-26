import Lift.Toys.FindSpec
import Lift.Pilot.Encode

/-! A test fixture of the suite `genupperloops` (task L3-U7): the L3 specification of a scan with a result of 16 bits. The input
and the code are those of `toyFind` (`Lift/Toys/data/toy.zig`); the result is the index of the first key, or the length, in
16 bits: the low 16 bits of the 64-bit register that the loop returns. The module name is the namespace, as the generators of
the sampler need. -/

namespace Skel.Test.NarrowFindSpec

/-- The contract of `toyFind`. -/
def C (x : Lift.Toys.FindSpec.In) : Prop := Lift.Toys.FindSpec.C x

/-- L3: the index of `toyFind`, in 16 bits. -/
def run (x : Lift.Toys.FindSpec.In) : Option (BitVec 16) := (Lift.Toys.FindSpec.run x).map (·.setWidth 16)

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Skel.Test.NarrowFindSpec
