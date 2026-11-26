module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Pilot.MapStatement
public import Lift.Pilot.MapInPlaceSpec
public import Lift.Level3.Code

@[expose] public section

/-! The trusted statement of `MappingBuilder.mapInPlace` (`shuffler.zig`, lines 385 to 391, quoted in
`Lift.Pilot.MapInPlaceSpec`). Not proved.

The function and its callee `map` read and write nine places, each with one width, and each access
agrees with a field of an object, so the form is `Fn.Call`. `mapInPlace` calls `map` and does not
call `closestCopy`. A call is not an access of the caller; the accesses of `map` are in the objects
because `map` is a callee:

    movq 8(%rdi),%rax; movq 24(%rdi),%r15     source_size, target_size: read 8
    movq (%rbx),%rax; movq 16(%rbx),%rcx      source, target: read 8
    movq (%rcx,%r14,8),%rcx                   target[j]: read 8
    xorq (%rax,%r14,8),%rcx                   source[j]: read 8
    movq 32(%rbx),%rax; cmpb $0,(%rax,%r14)   dropped, dropped[j]: read 8, read 1
    movq 48(%rbx),%rax; cmpq $-1,(%rax,%r14,8)  mapping, destination_of[j]: read 8, read 8
    callq .Lshuffler.MappingBuilder.map       dropped[j], destination_of[j], position_of[j]: read;
                                              destination_of[j], position_of[j]: write 8 -/

namespace Lift.Pilot.MapInPlaceStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Pilot.MapInPlaceSpec
open Lift.Pilot.MapStatement (droppedField mappingField droppedArr destArr posArr)

/-- `MappingBuilder.mapInPlace` in `Lift.Level3.Code.code`: the entry `0x1001bb` (label
`.Lshuffler.MappingBuilder.mapInPlace`), the stack room 32, and the result in `ax`, which is 16 bits
(`AssertionError!void`; the error path writes `ax` with `movw`). The room is 24 bytes of pushes
(`pushq %r15; pushq %r14; pushq %rbx`), 8 bytes of the return word of the call of `map`, and the 0
bytes of the room of `map`. -/
def mapInPlace : Fn := ⟨Lift.Level3.Code.code, 0x1001bb, 32, .W16⟩

/-- The entry is the label `.Lshuffler.MappingBuilder.mapInPlace`. -/
theorem mapInPlace_entry :
    Lift.Level3.Code.code.labels.label ".Lshuffler.MappingBuilder.mapInPlace" =
      mapInPlace.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The objects. `self` is the address of the `MappingBuilder` (64 bytes; types.json:
`shuffler.MappingBuilder`), `sp` of the source, `tp` of the target, `dp` of the array `dropped` and
`mp` of the `Mapping`. The record fields that the function touches are `source` at 0, `source_size`
at 8, `target` at 16, `target_size` at 24 (here), `dropped` at 32 and `mapping` at 48
(`MapStatement.droppedField`, `mappingField`), 8 bytes each, read-only; the other fields are not in an
object. The arrays are the whole source and the whole target (read-only; the loop reads the first
`min source_size target_size` slots, at run-time indices), `dropped` (read-only), and the tables
`destination_of` at `mp` and `position_of` at `mp + 8192` (writable: `map` writes one word of each).
`MapStatement` defines `dropped`, the tables and their sizes. -/
def objects (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest pos : Vector (BitVec 64) 1024) (self sp tp dp mp : BitVec 64) : List Object :=
  [ -- `source` at offset 0, the pointer `sp`
    ⟨self, Encode.encode sp, false⟩,
    -- `source_size` at offset 8
    ⟨self + 8, Encode.encode (BitVec.ofNat 64 src.length), false⟩,
    -- `target` at offset 16, the pointer `tp`
    ⟨self + 16, Encode.encode tp, false⟩,
    -- `target_size` at offset 24
    ⟨self + 24, Encode.encode (BitVec.ofNat 64 tgt.length), false⟩,
    -- `dropped` at offset 32, the pointer `dp`
    droppedField self dp,
    -- `mapping` at offset 48, the pointer `mp`
    mappingField self mp,
    -- the source slots at `sp`, each a 64-bit word
    ⟨sp, Encode.encode (src.map Slot.word), false⟩,
    -- the target slots at `tp`, each a 64-bit word
    ⟨tp, Encode.encode (tgt.map Slot.word), false⟩,
    -- the array `dropped` at `dp`
    droppedArr dropped dp,
    -- `destination_of` at `mp` (writable)
    destArr dest mp,
    -- `position_of` at `mp + 8192` (writable)
    posArr pos mp ]

/-- At the return: the result field holds the error code of L3, `destination_of` at `mp` has the
new contents of L3, and `position_of` at `mp + 8192` has the new contents of L3. -/
def post (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest pos : Vector (BitVec 64) 1024) (mp : BitVec 64) (policy : CpuPolicy) (r : Field)
    (m : DataMem) : Prop :=
  ∃ y, run src tgt dropped dest pos = some y ∧
    -- the result field `ax` (16 bits) is the error code `y.1`
    Encode.encode y.1 = [r] ∧
    -- `destination_of` at `mp` has the contents `y.2.1` (writable)
    Mem.has policy m (destArr y.2.1 mp) ∧
    -- `position_of` at `mp + 8192` has the contents `y.2.2` (writable)
    Mem.has policy m (posArr y.2.2 mp)

/-- For each `src`, `tgt`, `dropped`, `dest` and `pos` in the contract, and each address `self` of the
record, `sp` of the source, `tp` of the target, `dp` of `dropped` and `mp` of the mapping, the call
`mapInPlace(self)` returns: the result and the two tables are those of L3. -/
def MapInPlaceStatement : Prop :=
  ∀ (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024) (dest pos : Vector (BitVec 64) 1024),
    -- the contract
    C src tgt → ∀ self sp tp dp mp : BitVec 64,
    -- the call `mapInPlace(self)` returns with `post`
    mapInPlace.Call [⟨.W64, self⟩] (objects src tgt dropped dest pos self sp tp dp mp)
      (post src tgt dropped dest pos mp)

end Lift.Pilot.MapInPlaceStatement
