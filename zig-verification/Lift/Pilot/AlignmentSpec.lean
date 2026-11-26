module

@[expose] public section

/-! The L3 specification of `workspaceAlignment` (`shuffler.zig`, `fn workspaceAlignment() callconv(.c)
usize`, `return @alignOf(Workspace)`). The function returns a constant. The assembly of
`solidity_shuffler_workspaceAlignment` (`Lift/Level3/data/pilot.s`) is `pushq $8; popq %rax; retq`,
so it also returns 8. -/

namespace Lift.Pilot.AlignmentSpec

/-- L3: the alignment of `Workspace`, which is 8. `types.json` gives `shuffler.Workspace` the
alignment 8 (type 54), and the assembly returns the same 8 in `rax`. -/
def run : Option (BitVec 64) := some 8

/-- The contract: no input. The function has no argument, so every call is admitted. -/
def C : Prop := True

theorem total : C → ∃ y, run = some y := fun _ => ⟨8, rfl⟩

end Lift.Pilot.AlignmentSpec
