-- Generated from Lift/Pilot/IsRetainedStatement.lean by tools/shuffler-pilot/internal_statements.py. Do not edit by hand.
-- Rule: Lift.Level3.Code -> Lift.Shuffler.Code; the entry 0x1000b4 -> 0x10190d (Lift/Shuffler/Entry.lean);
-- the room 0 -> 0 in the Fn definition (frameFacts of the derived blocks of the shuffler; comments keep the ReleaseSmall text);
-- Lift.Pilot.<M>Statement -> Lift.Shuffler.Internal.<M>Statement.
module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.IsRetainedSpec
public import Lift.Shuffler.Code

@[expose] public section

/-! The trusted statement of `Planner.isRetained` (`shuffler.zig`, `noinline fn isRetained(mapping:
*const Mapping, source_offset: usize) bool`). Not proved.

    noinline fn isRetained(mapping: *const Mapping, source_offset: usize) bool {
        return mapping.destinationOf(source_offset) != .none;
    }
-/

namespace Lift.Shuffler.Internal.IsRetainedStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot.IsRetainedSpec

/-- `Planner.isRetained` in `Lift.Shuffler.Code.code`: the entry `0x10190d` (label
`.Lshuffler.Planner.isRetained`), no stack room (the function is a leaf: no push, no write), and
the result in `al`, which is the `bool` of 8 bits. The bits 8 to 63 of `rax` are not written by
`setne %al`, so the result has 8 bits. -/
def isRetained : Fn := ⟨Lift.Shuffler.Code.code, 0x10190d, 0, .W8⟩

/-- The entry is the label `.Lshuffler.Planner.isRetained`. -/
theorem isRetained_entry :
    Lift.Shuffler.Code.code.labels.label ".Lshuffler.Planner.isRetained" = isRetained.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The object: `destination_of` of the mapping at `p`, read-only. It is the 1024 words of 8 bytes
at offsets `0, 8, …, 8184` (types.json: `shuffler.Mapping`, field `destination_of` at offset 0,
size 8192). The function reads only this field, so `position_of` (at offset 8192) is not in the
object. -/
def objects (dest : Vector (BitVec 64) 1024) (p : BitVec 64) : List Object :=
  [⟨p, Encode.encode dest, false⟩]

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause
of `Fn.Return` keeps each byte, because the table is read-only and the room is empty. -/
def post (dest : Vector (BitVec 64) 1024) (i : Nat) (_ : CpuPolicy) (r : Field) (_ : DataMem) :
    Prop :=
  ∃ y, run dest i = some y ∧ Encode.encode y = [r]

/-- For each table `dest` and index `i` in the contract, and each address `p` of the table, the
call `isRetained(p, i)` returns the result of L3. -/
def IsRetainedStatement : Prop :=
  ∀ dest i, C dest i → ∀ p : BitVec 64,
    isRetained.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 i⟩] (objects dest p) (post dest i)

end Lift.Shuffler.Internal.IsRetainedStatement
