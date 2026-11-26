module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Call
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Pilot.ClosestCopySpec
public import Lift.Level3.Code

@[expose] public section

/-! The trusted statement of `MappingBuilder.closestCopy` (`shuffler.zig`, lines 365 to 383, quoted in
`Lift.Pilot.ClosestCopySpec`). Not proved.

The function reads seven places. Each slot of `source` and of `target` is read as 8 bytes
(`movq (%r14,%r9,8)`, `movq (%rbx,%rsi,8)`), and the `kind` byte of `target[i]` as 1 byte
(`movzbl 4(%rbx,%r9,8)`). No field list of the array `target` agrees with both widths, so the form
is `Fn.CallB` (`Lift.Pilot.Call`): `Fn.Call`, and the policy permits each access of each width inside
each object.

    movq 8(%rdi),%rcx                 source_size: read 8
    movq (%rdi),%r14                  source: read 8
    movq 16(%rdi),%rbx                target: read 8
    movq (%rbx,%rsi,8),%r15           target[t]: read 8
    xorq (%r14,%r9,8),%r15            source[i]: read 8
    movq 32(%rdi),%r14                dropped: read 8
    cmpb $0,(%r14,%r9)                dropped[i]: read 1
    movq 48(%rdi),%r14                mapping: read 8
    cmpq $-1,(%r14,%r9,8)             mapping.destination_of[i]: read 8
    cmpq 24(%rdi),%r9                 target_size: read 8
    movzbl 4(%rbx,%r9,8),%ebx         target[i].kind: read 1

The function writes no memory, except the four pushes of the callee-saved registers. -/

namespace Lift.Pilot.ClosestCopyStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Pilot.ClosestCopySpec

/-- `MappingBuilder.closestCopy` in `Lift.Level3.Code.code`: the entry `0x1000f0` (label
`.Lshuffler.MappingBuilder.closestCopy`), the stack room 32 (`pushq %rbp; pushq %r15; pushq %r14;
pushq %rbx` write the 32 bytes below the return word; no call, no `sub rsp`), and the result in
`rax`: an `OptionalOffset`, which is a `usize`, 64 bits. -/
def closestCopy : Fn := ⟨Lift.Level3.Code.code, 0x1000f0, 32, .W64⟩

/-- The entry is the label `.Lshuffler.MappingBuilder.closestCopy`. -/
theorem closestCopy_entry :
    Lift.Level3.Code.code.labels.label ".Lshuffler.MappingBuilder.closestCopy" =
      closestCopy.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The objects, all read-only, because the function writes no memory. `self` is the address of the
`MappingBuilder` (64 bytes; types.json: `shuffler.MappingBuilder`), `sp` of the source, `tp` of the
target, `dp` of the array `dropped` and `mp` of the `Mapping`. The function touches six fields of
the record: `source` at 0, `source_size` at 8, `target` at 16, `target_size` at 24, `dropped` at 32
and `mapping` at 48 (8 bytes each). The other fields (`wildcard_slots_strategy` at 40,
`saw_wildcard_copy` at 56) are not in an object. The arrays are the whole source (`source_size` slots
of 8 bytes: the loop reads each one), the whole target (`target_size` slots: the code reads `target[t]`
and `target[i]` at run-time indices), the array `dropped` (1024 bytes, types.json `[1024]u8`) and
`destination_of` (1024 words, 8192 bytes, at `mp`; `position_of` is not touched). -/
def objects (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest : Vector (BitVec 64) 1024) (self sp tp dp mp : BitVec 64) : List Object :=
  [ -- `source` at offset 0, the pointer `sp`
    ⟨self, Encode.encode sp, false⟩,
    -- `source_size` at offset 8
    ⟨self + 8, Encode.encode (BitVec.ofNat 64 src.length), false⟩,
    -- `target` at offset 16, the pointer `tp`
    ⟨self + 16, Encode.encode tp, false⟩,
    -- `target_size` at offset 24
    ⟨self + 24, Encode.encode (BitVec.ofNat 64 tgt.length), false⟩,
    -- `dropped` at offset 32, the pointer `dp`
    ⟨self + 32, Encode.encode dp, false⟩,
    -- `mapping` at offset 48, the pointer `mp`
    ⟨self + 48, Encode.encode mp, false⟩,
    -- the source slots at `sp`, each a 64-bit word
    ⟨sp, Encode.encode (src.map Slot.word), false⟩,
    -- the target slots at `tp`, each a 64-bit word
    ⟨tp, Encode.encode (tgt.map Slot.word), false⟩,
    -- the array `dropped` at `dp`
    ⟨dp, Encode.encode dropped, false⟩,
    -- `destination_of` at `mp`
    ⟨mp, Encode.encode dest, false⟩ ]

/-- At the return, the result is the result of L3. The memory is not in `post`: the objects are
read-only and the frame clause of `Fn.Return` keeps each byte. -/
def post (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024) (dest : Vector (BitVec 64) 1024)
    (t : Nat) (loc : BitVec 8) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run src tgt dropped dest t loc = some y ∧ Encode.encode y = [r]

/-- For each `src`, `tgt`, `dropped`, `dest`, offset `t` and byte `loc` in the contract, and each
address `self` of the record, `sp` of the source, `tp` of the target, `dp` of `dropped` and `mp` of
the mapping, the call `closestCopy(self, t, loc)` returns the result of L3. The third argument is
the 8-bit field of `dl`: the code reads only that byte, and the bits 8 to 63 of `rdx` are free. -/
def ClosestCopyStatement : Prop :=
  ∀ (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024) (dest : Vector (BitVec 64) 1024)
    (t : Nat) (loc : BitVec 8),
    -- the contract
    C src tgt t → ∀ self sp tp dp mp : BitVec 64,
    -- the call `closestCopy(self, t, loc)` returns with `post`
    closestCopy.CallB [⟨.W64, self⟩, ⟨.W64, BitVec.ofNat 64 t⟩, ⟨.W8, loc⟩]
      (objects src tgt dropped dest self sp tp dp mp) (post src tgt dropped dest t loc)

end Lift.Pilot.ClosestCopyStatement
