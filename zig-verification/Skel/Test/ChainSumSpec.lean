/-! A test fixture of the suite `genloop` (task AF2-C): the L3 specification of a chain sum. The nodes are those of
`toyWalk` (`Lift.Toys.WalkStatement.nodes`: `val` at offset 0, `next` at offset 8); the result is the wrapping sum of the
values, where `toyWalk` counts the nodes. The module name is the namespace, as the generators of the sampler need. -/

namespace Skel.Test.ChainSumSpec

/-- The `val` fields of the nodes, from the head to the last node. -/
abbrev In := List (BitVec 64)

/-- L3: the wrapping sum of the values. -/
def run (x : In) : Option (BitVec 64) := some x.sum

/-- The contract: each list. -/
def C (_ : In) : Prop := True

theorem total : ∀ x, C x → ∃ y, run x = some y := fun x _ => ⟨x.sum, rfl⟩

end Skel.Test.ChainSumSpec
