import Lift.Trusted.Call
import Lift.Trusted.Encode

/-! Test fixtures of the suite `genaf2b` (task AF2-B): the L3 specification of `toyFind` whose inputs have the names `a` and `b` (the form of `∀ a b, C a b → …`),
names that the generated texts bind. -/

namespace Skel.Test.ABFindSpec

def run (a : List (BitVec 64)) (b : BitVec 64) : Option (BitVec 64) := some (BitVec.ofNat 64 (a.idxOf b))

def C (a : List (BitVec 64)) (_b : BitVec 64) : Prop := a.length < 2 ^ 64

theorem total : ∀ a b, C a b → ∃ y, run a b = some y := fun _ _ _ => ⟨_, rfl⟩

def objects (a : List (BitVec 64)) (p : BitVec 64) : List Lift.Trusted.Object :=
  [⟨p, Lift.Trusted.Encode.encode a, false⟩]

end Skel.Test.ABFindSpec
