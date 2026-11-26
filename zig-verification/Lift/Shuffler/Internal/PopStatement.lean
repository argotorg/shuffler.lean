-- Generated from Lift/Pilot/PopStatement.lean by tools/shuffler-pilot/internal_statements.py. Do not edit by hand.
-- Rule: Lift.Level3.Code -> Lift.Shuffler.Code; the entry 0x10005a -> 0x101714 (Lift/Shuffler/Entry.lean);
-- the room 0 -> 0 in the Fn definition (frameFacts of the derived blocks of the shuffler; comments keep the ReleaseSmall text);
-- Lift.Pilot.<M>Statement -> Lift.Shuffler.Internal.<M>Statement.
module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Pilot.PopSpec
public import Lift.Shuffler.Code

@[expose] public section

/-! The trusted statement of `Emission.pop` (`shuffler.zig`, `noinline fn pop(self: *Emission)
AssertionError!void`). Not proved. The Zig source and the L3 function are in `PopSpec`.

The function reads and writes seven places, each with one width, and each access agrees with a field
of an object, so the form is `Fn.Call`:

    movq 48(%rdi),%rcx ... movq %rcx,48(%rdi)      stack.size: read 8, write 8
    movq 64(%rdi),%rdx ... incq 64(%rdi)           stack.trace_size: read 8, read-modify-write 8
    movq 56(%rdi),%rax                             stack.trace: read 8
    movw $2,(%rax,%rdx)                            trace[trace_size], kind and depth: write 2
    movq %rsi,4(%rax,%rdx)                         trace[trace_size].slot: write 8
    movq 72(%rdi),%rax                             mapping: read 8
    movq (%rax,%rcx,8),%rcx                        mapping.destination_of[size - 1]: read 8
    orq $-1,8192(%rax,%rcx,8)                      mapping.position_of[d]: read-modify-write 8 -/

namespace Lift.Shuffler.Internal.PopStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Pilot.PopSpec

/-- `AssertionError!void` is 16 bits (types.json: `error{AssertionFailed}!void`, size 2): 0 for
`ok`, 1 for `AssertionFailed` (`xorl %eax,%eax` and `movw $1,%ax`). -/
instance : Encode Assert where
  encode
    | .ok => [⟨.W16, 0⟩]
    | .failed => [⟨.W16, 1⟩]
  decode
    | [⟨.W16, v⟩] => if v = 0 then some .ok else if v = 1 then some .failed else none
    | _ => none

/-- `ShuffleOp` for the code of `Emission.pop`: three fields, `kind` and `depth` together as one
16-bit field at 0 (`movw $2,(%rax,%rdx)`: `kind` is the low byte and `depth` the high byte, the byte
order of the store), the padding as one 16-bit field at 2, and `slot` as one 64-bit field at 4. The
full shuffler writes `kind` and `depth` as two 8-bit stores (the census of the pilot); `Fn.Call`
permits only the widths of the field list, so the full shuffler will need `Fn.CallB` for this
type. -/
instance : Encode ShuffleOp where
  encode o := [⟨.W16, o.depth ++ o.kind⟩, ⟨.W16, o.pad⟩, ⟨.W64, o.slot.word⟩]
  decode
    | [⟨.W16, kd⟩, ⟨.W16, p⟩, ⟨.W64, w⟩] =>
      some ⟨kd.extractLsb' 0 8, kd.extractLsb' 8 8, p, Slot.ofWord w⟩
    | _ => none

/-- `Emission.pop` in `Lift.Shuffler.Code.code`: the entry `0x101714` (label
`.Lshuffler.Emission.pop`), no stack room (no push, no call), and the result in `ax`: the 16 bits of
`AssertionError!void`. The function writes only `rax`, `rcx`, `rdx` and `rsi`. -/
def pop : Fn := ⟨Lift.Shuffler.Code.code, 0x101714, 0, .W16⟩

/-- The entry is the label `.Lshuffler.Emission.pop`. -/
theorem pop_entry :
    Lift.Shuffler.Code.code.labels.label ".Lshuffler.Emission.pop" = pop.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The writable objects, with the contents `size`, `ts`, `trace`, `pos`. `self` is the address of
the `Emission` (120 bytes; types.json: `shuffler.Emission`), `tr` the address of the trace and `mp`
the address of the `Mapping` (16384 bytes: `destination_of` at 0, `position_of` at 8192). The
function writes four places: `stack.size` at `self + 48`; `stack.trace_size` at `self + 64`; the
trace, the whole array `[10240]ShuffleOp` (122880 bytes) because the function writes the one element
at the run-time index `trace_size`, which the contract does not fix, and a full trace is a valid
input; and `position_of` at `mp + 8192`, the whole array for the same reason. -/
def written (self tr mp size ts : BitVec 64) (trace : Vector ShuffleOp 10240)
    (pos : Vector (BitVec 64) 1024) : List Object :=
  [⟨self + 48, Encode.encode size, true⟩, ⟨self + 64, Encode.encode ts, true⟩,
    ⟨tr, Encode.encode trace, true⟩, ⟨mp + 8192, Encode.encode pos, true⟩]

/-- The objects of the call: the four written ones, then the pointers `stack.trace` at `self + 56`
and `mapping` at `self + 72` (read-only), and `destination_of` at `mp` (read-only, the array
`[1024]OptionalOffset`, 8192 bytes, because the function reads the one entry at the run-time index
`size - 1`). The other fields of `Emission` are not in an object. -/
def objects (x : In) (self tr mp : BitVec 64) : List Object :=
  written self tr mp x.size x.traceSize x.trace x.pos ++
    [⟨self + 56, Encode.encode tr, false⟩, ⟨self + 72, Encode.encode mp, false⟩,
      ⟨mp, Encode.encode x.dest, false⟩]

/-- At the return, L3 gives `y`: the result is the result of `y`, and the four written objects have
the contents of `y`. -/
def post (x : In) (self tr mp : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y.res = [r] ∧
    ∀ o ∈ written self tr mp y.size y.traceSize y.trace y.pos, Mem.has policy m o

/-- For each input `x` in the contract, and each address `self` of the `Emission`, `tr` of the trace
and `mp` of the mapping, the call `pop(self)` returns the result of L3, and the written objects have
the contents of L3. -/
def PopStatement : Prop :=
  ∀ x, C x → ∀ self tr mp : BitVec 64,
    pop.Call [⟨.W64, self⟩] (objects x self tr mp) (post x self tr mp)

end Lift.Shuffler.Internal.PopStatement
