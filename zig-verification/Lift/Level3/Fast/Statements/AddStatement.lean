-- Generated from Lift/Pilot/AddStatement.lean by tools/shuffler-pilot/fast_statements.py. Do not edit by hand.
-- Rule: Lift.Level3.Code -> Lift.Level3.Fast.Code; the entry 0x100004 -> 0x100006 (Lift/Level3/Fast/L1.lean);
-- the room 0 -> 0 in the Fn definition (frameFacts of the derived blocks; comments keep the ReleaseSmall text);
-- Lift.Pilot.<M>Statement -> Lift.Level3.Fast.Statements.<M>Statement.
module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Pilot.AddSpec
public import Lift.Level3.Fast.Code

@[expose] public section

/-! The trusted statement of `SpillSet.add` (`shuffler.zig`, lines 170 to 174, quoted in
`Lift.Pilot.AddSpec`). Not proved. -/

namespace Lift.Level3.Fast.Statements.AddStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Pilot.AddSpec

/-- `SpillSet.add` in `Lift.Level3.Fast.Code.code`: the entry `0x100006` (label
`.Lshuffler.SpillSet.add`), no stack room (a leaf: no push and no `sub rsp`), and the result in
`ax`, which is 16 bits: the error path writes `ax` with `movw`, so the bits 16 to 63 of `rax` are not
the result. -/
def add : Fn := ⟨Lift.Level3.Fast.Code.code, 0x100006, 0, .W16⟩

/-- The entry is the label `.Lshuffler.SpillSet.add`. -/
theorem add_entry :
    Lift.Level3.Fast.Code.code.labels.label ".Lshuffler.SpillSet.add" = add.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The record `SpillSet` at `self`: its field `spilled`, of 8 bytes at offset 0 (types.json:
`shuffler.SpillSet`, uid 1001, size 8), which holds the pointer `sp` to the buffer. The function
reads it and does not write it, so it is read-only. -/
def spilledField (self sp : BitVec 64) : Object := ⟨self, Encode.encode sp, false⟩

/-- The buffer `spilled` at `sp`, with the old contents `buf`: one byte for each element, so
`buf.size` bytes. `[*]u8` has no length in types.json; the length is the number of variable ids of
the caller, and `C` bounds the payload by it. The function writes one byte, so it is writable. -/
def spilledBuf {n : Nat} (buf : Vector (BitVec 8) n) (sp : BitVec 64) : Object :=
  ⟨sp, Encode.encode buf, true⟩

/-- The objects of a call with the old buffer `buf`, the record at `self` and the buffer at `sp`:
the field `spilled` and the buffer. The record holds no other field that the function touches. -/
def objects {n : Nat} (buf : Vector (BitVec 8) n) (self sp : BitVec 64) : List Object :=
  [spilledField self sp, spilledBuf buf sp]

/-- At the return: the result field holds the error code of L3, and the buffer at `sp` has the new
contents of L3. The read-only record is unchanged by the frame clause of `Fn.Return`. -/
def post {n : Nat} (slot : Slot) (buf : Vector (BitVec 8) n) (sp : BitVec 64) (policy : CpuPolicy)
    (r : Field) (m : DataMem) : Prop :=
  ∃ y, run slot buf = some y ∧
    -- the result field `ax` (16 bits) is the error code `y.1`
    Encode.encode y.1 = [r] ∧
    -- the buffer at `sp` has the contents `y.2` (writable)
    Mem.has policy m ⟨sp, Encode.encode y.2, true⟩

/-- For each buffer `buf` and slot `slot` in the contract, and each address `self` of the record
and `sp` of the buffer, the call `add(self, slot)` returns:
the result and the buffer are those of L3. -/
def AddStatement : Prop :=
  ∀ {n : Nat} (buf : Vector (BitVec 8) n) (slot : Slot), C buf slot → ∀ self sp : BitVec 64,
    -- the call `add(self, slot)` returns with `post`
    add.Call [⟨.W64, self⟩, ⟨.W64, slot.word⟩] (objects buf self sp) (post slot buf sp)

end Lift.Level3.Fast.Statements.AddStatement
