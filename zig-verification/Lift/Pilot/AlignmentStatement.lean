module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.AlignmentSpec
public import Lift.Level3.Code

@[expose] public section

/-! The trusted statement of `workspaceAlignment` (`shuffler.zig`, `fn workspaceAlignment()
callconv(.c) usize`, exported as `solidity_shuffler_workspaceAlignment`). Not proved.

    fn workspaceAlignment() callconv(.c) usize {
        return @alignOf(Workspace);
    }
-/

namespace Lift.Pilot.AlignmentStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot.AlignmentSpec

/-- `workspaceAlignment` in `Lift.Level3.Code.code`: the entry `0x100000`; the room 8, the bytes
that `pushq $8` writes below `rsp` (the net change of `rsp` is zero, as `popq` reads them back); and
the 64-bit result in `rax`, which is the `usize` of the Zig return type. -/
def workspaceAlignment : Fn := ⟨Lift.Level3.Code.code, 0x100000, 8, .W64⟩

/-- The entry is the label `solidity_shuffler_workspaceAlignment`. -/
theorem workspaceAlignment_entry :
    Lift.Level3.Code.code.labels.label "solidity_shuffler_workspaceAlignment" =
      workspaceAlignment.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The function reads no object: the result is a constant. -/
def objects : List Object := []

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause
of `Fn.Return` keeps each byte, because the function writes only its room. -/
def post (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run = some y ∧ Encode.encode y = [r]

/-- The call of `workspaceAlignment` (no argument, so `C` is the only contract) returns the result
of L3. -/
def AlignmentStatement : Prop :=
  C → workspaceAlignment.Call [] objects post

end Lift.Pilot.AlignmentStatement
