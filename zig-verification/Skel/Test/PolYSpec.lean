import Lift.Trusted.Call
import Lift.Trusted.Encode

/-! A test fixture of the suite `genaf2b` (task AF2-B): the L3 specification of `toyFind` whose inputs have the names `policy` and
`y`, names that the generated texts bind. The module name is the namespace. -/

namespace Skel.Test.PolYSpec

def run (policy : List (BitVec 64)) (y : BitVec 64) : Option (BitVec 64) := some (BitVec.ofNat 64 (policy.idxOf y))

def C (policy : List (BitVec 64)) (_y : BitVec 64) : Prop := policy.length < 2 ^ 64

theorem total : ∀ policy y, C policy y → ∃ z, run policy y = some z := fun _ _ _ => ⟨_, rfl⟩

def objects (policy : List (BitVec 64)) (p : BitVec 64) : List Lift.Trusted.Object :=
  [⟨p, Lift.Trusted.Encode.encode policy, false⟩]

end Skel.Test.PolYSpec
