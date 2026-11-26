import Lift.Trusted.Call
import Lift.Trusted.Encode

/-! A test fixture of the suite `genupperinputs` (task L3-U2): the L3 specification of `toyFind` with the two inputs as flat
variables (`∀ vals key, C vals key → …`), the form of the pilot statements, in place of the record `Lift.Toys.FindSpec.In`.
`run` has the parameters `vals` and `key`: the generators apply it to the inputs of the statement by name. The module name is
the namespace, as the generators of the sampler need (`opens` of the refute file). -/

namespace Skel.Test.FlatFindSpec

/-- The index of the first `key` in `vals`, or the length of `vals` if there is none. -/
def run (vals : List (BitVec 64)) (key : BitVec 64) : Option (BitVec 64) := some (BitVec.ofNat 64 (vals.idxOf key))

/-- The contract: the length fits in the 64-bit `n` argument. -/
def C (vals : List (BitVec 64)) (_key : BitVec 64) : Prop := vals.length < 2 ^ 64

theorem total : ∀ vals key, C vals key → ∃ y, run vals key = some y := fun _ _ _ => ⟨_, rfl⟩

/-- The array object: the words of `vals` at `p`, read-only. -/
def objects (vals : List (BitVec 64)) (p : BitVec 64) : List Lift.Trusted.Object :=
  [⟨p, Lift.Trusted.Encode.encode vals, false⟩]

end Skel.Test.FlatFindSpec
