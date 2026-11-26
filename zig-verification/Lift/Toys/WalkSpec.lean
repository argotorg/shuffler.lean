module

@[expose] public section

/-! The L3 specification of `toyWalk` (`Lift/Toys/data/toy.zig`): pure values only.

    const Node = extern struct { val: u64, next: ?*const Node };
    export fn toyWalk(head: ?*const Node) u64

The input is the list of the `val` fields of the nodes, in the order of the chain. A list is finite,
so L3 has no cycle: the acyclicity of the chain is a part of the trusted statement (the node objects
end with a `next` of 0), not of `C`. -/

namespace Lift.Toys.WalkSpec

/-- The `val` fields of the nodes, from the head to the last node. -/
abbrev In := List (BitVec 64)

/-- The number of nodes; the code counts with a 64-bit register, so the count wraps. -/
def run (x : In) : Option (BitVec 64) := some (BitVec.ofNat 64 x.length)

/-- The contract: each list. -/
def C (_ : In) : Prop := True

theorem total : ∀ x, C x → ∃ y, run x = some y := fun _ _ => ⟨_, rfl⟩

end Lift.Toys.WalkSpec
