module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Pilot.ShallowestSpec
public import Lift.Level3.Code

@[expose] public section

/-! The trusted statement of `Emission.shallowestCopyPosition` (`shuffler.zig`, `noinline fn
shallowestCopyPosition(self: *const Emission, slot: StackSlot) OptionalOffset`). Not proved.

    noinline fn shallowestCopyPosition(self: *const Emission, slot: StackSlot) OptionalOffset {
        var pos = self.stack.size;
        while (pos > 0) {
            pos -= 1;
            if (self.stack.at(pos).eql(slot)) return .some(pos);
        }
        return .none;
    }

The function reads three places, each with one width: `stack.size` as 8 bytes, `stack.data` as 8
bytes, and each slot as 8 bytes. Each read agrees with a field of an object, so the form is
`Fn.Call`. -/

namespace Lift.Pilot.ShallowestStatement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Pilot.ShallowestSpec

/-- `Emission.shallowestCopyPosition` in `Lift.Level3.Code.code`: the entry `0x100034` (label
`.Lshuffler.Emission.shallowestCopyPosition`), the stack room 8 (`pushq $-1` writes the 8 bytes below
`rsp`), and the result in `rax`: an `OptionalOffset`, which is a `usize`, 64 bits. -/
def shallowestCopyPosition : Fn := ⟨Lift.Level3.Code.code, 0x100034, 8, .W64⟩

/-- The entry is the label `.Lshuffler.Emission.shallowestCopyPosition`. -/
theorem shallowestCopyPosition_entry :
    Lift.Level3.Code.code.labels.label ".Lshuffler.Emission.shallowestCopyPosition" =
      shallowestCopyPosition.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The objects, all read-only. `self` is the address of the `Emission` (120 bytes; types.json:
`shuffler.Emission`) and `dp` the address of the slot array. The function touches two fields of
`Emission`: `stack.data` (the pointer `dp`) at `self + 40`, and `stack.size` at `self + 48`
(`stack` is at 40 in `Emission`, `data` at 0 and `size` at 8 in `Stack`). The array is the 1024
slots, 8192 bytes, of `stack.data`: the Zig type `*[max_stack_size]StackSlot` gives all of them, and
the function reads those below `size`. The other fields of `Emission` are not in an object. -/
def objects (x : In) (self dp : BitVec 64) : List Object :=
  [⟨self + 40, Encode.encode dp, false⟩, ⟨self + 48, Encode.encode x.size, false⟩,
    ⟨dp, Encode.encode x.data, false⟩]

/-- At the return, the result is the result of L3. The memory is not in `post`: the objects are
read-only and the frame clause of `Fn.Return` keeps each byte. -/
def post (x : In) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y = [r]

/-- For each input `x` in the contract, and each address `self` of the `Emission` and `dp` of its
slot array, the call `shallowestCopyPosition(self, slot)` returns the result of L3. -/
def ShallowestStatement : Prop :=
  ∀ x, C x → ∀ self dp : BitVec 64,
    shallowestCopyPosition.Call [⟨.W64, self⟩, ⟨.W64, x.slot.word⟩] (objects x self dp) (post x)

end Lift.Pilot.ShallowestStatement
