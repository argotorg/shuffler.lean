-- Generated from Lift/Pilot/MapStatement.lean by tools/shuffler-pilot/fast_statements.py. Do not edit by hand.
-- Rule: Lift.Level3.Code -> Lift.Level3.Fast.Code; the entry 0x1000bd -> 0x1000cb (Lift/Level3/Fast/L1.lean);
-- the room 0 -> 0 in the Fn definition (frameFacts of the derived blocks; comments keep the ReleaseSmall text);
-- Lift.Pilot.<M>Statement -> Lift.Level3.Fast.Statements.<M>Statement.
module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.MapSpec
public import Lift.Level3.Fast.Code

@[expose] public section

/-! The trusted statement of `MappingBuilder.map` (`shuffler.zig`, lines 354 to 359, quoted in
`Lift.Pilot.MapSpec`). Not proved. -/

namespace Lift.Level3.Fast.Statements.MapStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot.MapSpec

/-- `MappingBuilder.map` in `Lift.Level3.Fast.Code.code`: the entry `0x1000cb` (label
`.Lshuffler.MappingBuilder.map`), no stack room (a leaf: no push and no `sub rsp`), and the result in
`ax`, which is 16 bits: the error path writes `ax` with `movw`, so the bits 16 to 63 of `rax` are not
the result. -/
def map : Fn := ⟨Lift.Level3.Fast.Code.code, 0x1000cb, 0, .W16⟩

/-- The entry is the label `.Lshuffler.MappingBuilder.map`. -/
theorem map_entry :
    Lift.Level3.Fast.Code.code.labels.label ".Lshuffler.MappingBuilder.map" = map.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The field `dropped` of the record `MappingBuilder` at `self`: a pointer of 8 bytes at offset 32
(types.json: `shuffler.MappingBuilder`, uid 12005, size 8), holding `dp`. The function reads it and
does not write it, so it is read-only. -/
def droppedField (self dp : BitVec 64) : Object := ⟨self + 32, Encode.encode dp, false⟩

/-- The field `mapping` of the record at `self`: a pointer of 8 bytes at offset 48 (types.json: uid
12007, size 8), holding `mp`. The function reads it and does not write it, so it is read-only. -/
def mappingField (self mp : BitVec 64) : Object := ⟨self + 48, Encode.encode mp, false⟩

/-- The array `dropped` at `dp`: 1024 bytes (types.json: `[1024]u8`, size 1024), one byte for each
source offset. The function reads one byte of it, so it is read-only. -/
def droppedArr (dropped : Vector (BitVec 8) 1024) (dp : BitVec 64) : Object :=
  ⟨dp, Encode.encode dropped, false⟩

/-- The table `destination_of` of the `Mapping` at `mp`: 1024 words of 8 bytes (types.json: offset
0, size 8192, uid 19001). The function reads one word and writes one word of it, so it is writable. -/
def destArr (dest : Vector (BitVec 64) 1024) (mp : BitVec 64) : Object :=
  ⟨mp, Encode.encode dest, true⟩

/-- The table `position_of` of the `Mapping` at `mp`: 1024 words of 8 bytes at offset 8192 (types.json:
size 8192, uid 19002). The function reads one word and writes one word of it, so it is writable. -/
def posArr (pos : Vector (BitVec 64) 1024) (mp : BitVec 64) : Object :=
  ⟨mp + 8192, Encode.encode pos, true⟩

/-- The objects of a call with the record at `self`, the array `dropped` at `dp`, the tables
`dest` and `pos` of the `Mapping` at `mp`. The function touches no other field of the record. -/
def objects (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024)
    (self dp mp : BitVec 64) : List Object :=
  [droppedField self dp, mappingField self mp, droppedArr dropped dp, destArr dest mp,
    posArr pos mp]

/-- At the return: the result field holds the error code of L3, `destination_of` at `mp` has the
new contents of L3, and `position_of` at `mp + 8192` has the new contents of L3. -/
def post (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024) (s t : Nat)
    (mp : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run dropped dest pos s t = some y ∧
    -- the result field `ax` (16 bits) is the error code `y.1`
    Encode.encode y.1 = [r] ∧
    -- `destination_of` at `mp` has the contents `y.2.1` (writable)
    Mem.has policy m ⟨mp, Encode.encode y.2.1, true⟩ ∧
    -- `position_of` at `mp + 8192` has the contents `y.2.2` (writable)
    Mem.has policy m ⟨mp + 8192, Encode.encode y.2.2, true⟩

/-- For each `dropped`, `dest`, `pos`, and indices `s`, `t` in the contract, and each address
`self` of the record, `dp` of the array and `mp` of the mapping, the call `map(self, s, t)` returns: the result and the two tables are those of L3. -/
def MapStatement : Prop :=
  ∀ (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024) (s t : Nat),
    -- the indices are in the contract
    C s t → ∀ self dp mp : BitVec 64,
    -- the call `map(self, s, t)` returns with `post`
    map.Call [⟨.W64, self⟩, ⟨.W64, BitVec.ofNat 64 s⟩, ⟨.W64, BitVec.ofNat 64 t⟩]
      (objects dropped dest pos self dp mp) (post dropped dest pos s t mp)

end Lift.Level3.Fast.Statements.MapStatement
