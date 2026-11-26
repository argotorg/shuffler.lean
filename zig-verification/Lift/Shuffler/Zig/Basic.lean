module

public import Lift.Shuffler.Ext.Model
public import Lift.Pilot.Slot

@[expose] public section

/-!
The basic types of the Zig flat model (`docs/research/zig-flat-model-design-20261118.md`,
sections 2 and 3.1, task K3c).

The model uses the `StackSlot` of the `Ext` model, which has no padding. The padding of a slot
is carried beside it: `Slot.split` takes the `Lift.Pilot.Slot` of the L3 boundary to a `StackSlot`
and its padding, and `Slot.join` is the inverse. `OpP` is an `Op` of the trace with the padding of
its slot.
-/

namespace Lift.Shuffler.Zig

/-- The result of a unit of the Zig model. `returned v` is a normal return with the value `v`.
`assertionExit` is a failed assertion of the Zig code. `outOfFuel` is a loop that ran out of
fuel (`permute`, design section 3.4). -/
inductive Exit (α : Type) where
  | returned (v : α)
  | assertionExit
  | outOfFuel
  deriving DecidableEq, Repr

/-- The number of entries of the trace array (`max_trace_size`, Z:56): `(6 + 4) * max_stack_size`. -/
def maxTraceSize : Nat := 10240

/-- An operation of the trace with the padding of its slot. `pad` is the padding of the word that
was pushed for a push or a load, and 0 for a swap or a dup. -/
structure OpP where
  op : FlatShuffler.Op
  pad : BitVec 16
  deriving DecidableEq, Repr

/-- The split of a slot: the `StackSlot` of the model (payload, kind and opcode) and the padding
of the slot. -/
def Slot.split (s : Lift.Pilot.Slot) : FlatShuffler.StackSlot × BitVec 16 :=
  (⟨s.payload, s.kind, s.opcode⟩, s.pad)

/-- The join of a `StackSlot` and its padding: the inverse of `Slot.split`. -/
def Slot.join (p : FlatShuffler.StackSlot × BitVec 16) : Lift.Pilot.Slot :=
  ⟨p.1.payload, p.1.kind, p.1.valueOpcode, p.2⟩

/-- `join` after `split` is the identity. -/
theorem Slot.join_split (s : Lift.Pilot.Slot) : Slot.join (Slot.split s) = s :=
  rfl

/-- `split` after `join` is the identity. -/
theorem Slot.split_join (p : FlatShuffler.StackSlot × BitVec 16) :
    Slot.split (Slot.join p) = p :=
  rfl

/-- `split` keeps the payload, the kind and the opcode of a slot, and gives its padding. -/
theorem Slot.split_fields (s : Lift.Pilot.Slot) :
    (Slot.split s).1.payload = s.payload ∧ (Slot.split s).1.kind = s.kind ∧
      (Slot.split s).1.valueOpcode = s.opcode ∧ (Slot.split s).2 = s.pad :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The `=` of two splits is the compare of the two slots without padding (`eql` of the Zig
`StackSlot`, Z:96-99). -/
theorem Slot.split_eq_iff (a b : Lift.Pilot.Slot) :
    (Slot.split a).1 = (Slot.split b).1 ↔
      a.payload = b.payload ∧ a.kind = b.kind ∧ a.opcode = b.opcode := by
  simp [Slot.split, FlatShuffler.StackSlot.mk.injEq]

end Lift.Shuffler.Zig
