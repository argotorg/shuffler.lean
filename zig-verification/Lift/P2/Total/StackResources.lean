module

public import Lift.P2.Total.ProjectionRules
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

namespace Lift.P2.Total.Stack

/-- A private frame has a fixed size. Its bytes and the public return word
fit in one address space, including when RSP wraps through zero. -/
structure Frame where
  bytes : Nat
  bounded : bytes + 8 ≤ 2 ^ 64

/-- A whole access below the entry RSP. A slot cannot include the return word. -/
structure Slot (frame : Frame) where
  depth : Nat
  width : Width
  lower : width.bytes ≤ depth
  upper : depth ≤ frame.bytes

def Frame.start (frame : Frame) (rsp : BitVec 64) : BitVec 64 :=
  rsp - BitVec.ofNat 64 frame.bytes

def Frame.privateByte (frame : Frame) (rsp : BitVec 64) : BitVec 64 → Bool :=
  byteRange (frame.start rsp) frame.bytes

def Slot.address {frame : Frame} (slot : Slot frame) (rsp : BitVec 64) : BitVec 64 :=
  rsp - BitVec.ofNat 64 slot.depth

inductive Use where
  | read
  | write

structure Request (frame : Frame) where
  use : Use
  slot : Slot frame

def Request.access {frame : Frame} (request : Request frame) (rsp : BitVec 64) : Access :=
  match request.use with
  | .read => .read (request.slot.address rsp) request.slot.width
  | .write => .write (request.slot.address rsp) request.slot.width

/-- Mapping is required only for these fixed bytes. Permissions are required
only for the access kinds and widths in the checked finite request list. -/
structure Room (frame : Frame) (requests : List (Request frame)) (policy : CpuPolicy)
    (rsp : BitVec 64) (memory : DataMem) : Prop where
  mapped : ∀ i < frame.bytes,
    memory.get? (frame.start rsp + BitVec.ofNat 64 i) ≠ none
  permitted : ∀ request ∈ requests, policy.permits (request.access rsp) = true

theorem Slot.byte_address {frame : Frame} (slot : Slot frame) (rsp : BitVec 64)
    (i : Nat) :
    slot.address rsp + BitVec.ofNat 64 i =
      frame.start rsp + BitVec.ofNat 64 (frame.bytes - slot.depth + i) := by
  have sum : frame.bytes = slot.depth + (frame.bytes - slot.depth) := by
    have := slot.upper
    omega
  have base : rsp - BitVec.ofNat 64 slot.depth =
      (rsp - BitVec.ofNat 64 frame.bytes) + BitVec.ofNat 64 (frame.bytes - slot.depth) := by
    have expanded := congrArg (BitVec.ofNat 64) sum
    rw [BitVec.ofNat_add] at expanded
    rw [expanded, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  simpa only [Slot.address, Frame.start, BitVec.ofNat_add, ← BitVec.add_assoc] using
    congrArg (fun a => a + BitVec.ofNat 64 i) base

theorem Slot.private {frame : Frame} (slot : Slot frame) (rsp : BitVec 64)
    (i : Nat) (inside : i < slot.width.bytes) :
    frame.privateByte rsp (slot.address rsp + BitVec.ofNat 64 i) = true := by
  rw [slot.byte_address rsp i]
  apply byteRange_inside
  have := slot.lower
  have := slot.upper
  omega

/-- No minimum numerical RSP is needed. The ranges are disjoint modulo 2^64. -/
theorem Frame.separate_return (frame : Frame) (rsp : BitVec 64) :
    ByteDisjoint (frame.start rsp) frame.bytes rsp 8 := by
  intro i hi j hj equal
  have shifted := congrArg (fun a => a + BitVec.ofNat 64 frame.bytes) equal
  have rearrange (a b c : BitVec 64) : a - c + b + c = a + b := by
    rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  simp only [Frame.start, rearrange, BitVec.add_assoc] at shifted
  have cancel := (BitVec.add_right_inj rsp).mp shifted
  have bounded := frame.bounded
  have value := congrArg BitVec.toNat cancel
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at value
  rw [Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by omega : j < 2^64),
    Nat.mod_eq_of_lt (by omega : frame.bytes < 2^64),
    Nat.mod_eq_of_lt (by omega : j + frame.bytes < 2^64)] at value
  omega

theorem Frame.public_return (frame : Frame) (rsp : BitVec 64) (memory : DataMem) :
    Mem.loadInt (hideRam (frame.privateByte rsp) memory) rsp 8 =
      Mem.loadInt memory rsp 8 := by
  exact hideRam_load_separate _ _ _ _ _ (frame.separate_return rsp)

/-- Disjoint slot intervals stay disjoint when RSP wraps. -/
theorem Slot.separate {frame : Frame} (left right : Slot frame) (rsp : BitVec 64)
    (apart : left.depth + right.width.bytes ≤ right.depth ∨
      right.depth + left.width.bytes ≤ left.depth) :
    ByteDisjoint (left.address rsp) left.width.bytes (right.address rsp) right.width.bytes := by
  intro i hi j hj equal
  rw [left.byte_address rsp i, right.byte_address rsp j] at equal
  have raw := (BitVec.add_right_inj (frame.start rsp)).mp equal
  have numeric := congrArg BitVec.toNat raw
  have := frame.bounded
  have := left.lower
  have := left.upper
  have := right.lower
  have := right.upper
  simp only [BitVec.toNat_ofNat] at numeric
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at numeric
  rcases apart with apart | apart <;> omega

theorem Slot.hide_store {frame : Frame} (slot : Slot frame) (rsp : BitVec 64)
    (memory : DataMem) (value : Int) :
    hideRam (frame.privateByte rsp)
        (Mem.storeInt memory (slot.address rsp) slot.width.bytes value) =
      hideRam (frame.privateByte rsp) memory := by
  exact hideRam_storeInt _ _ _ _ _ (slot.private rsp)

theorem Slot.preserves_return {frame : Frame} (slot : Slot frame) (rsp : BitVec 64)
    (memory : DataMem) (value : Int) :
    Mem.loadInt (Mem.storeInt memory (slot.address rsp) slot.width.bytes value) rsp 8 =
      Mem.loadInt memory rsp 8 := by
  apply loadInt_storeInt_separate
  intro i hi j hj equal
  apply frame.separate_return rsp (frame.bytes - slot.depth + i)
    (by have := slot.lower; have := slot.upper; omega) j hj
  rw [← slot.byte_address rsp i]
  exact equal

theorem loadInt_mapped (memory : DataMem) (address : BitVec 64) (bytes : Nat)
    (mapped : ∀ i < bytes, memory.get? (address + BitVec.ofNat 64 i) ≠ none) :
    Mem.loadInt memory address bytes ≠ none := by
  have loads : ∀ indices : List Nat, (∀ i ∈ indices, i < bytes) →
      ((indices.map fun i => memory.get? (address + BitVec.ofNat 64 i)).mapM id).isSome = true := by
    intro indices bounded
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp
        (Option.isSome_iff_ne_none.mpr (mapped i (bounded i (by simp))))
      obtain ⟨values, loads⟩ := Option.isSome_iff_exists.mp
        (ih fun j hj => bounded j (by simp [hj]))
      simp only [List.map_cons, List.mapM_cons, id, loaded, loads]
      rfl
  apply Option.isSome_iff_ne_none.mp
  simpa only [Mem.loadInt, Mem.loadBytes, List.allSome, Option.isSome_map] using
    loads (List.range bytes) (fun i hi => List.mem_range.mp hi)

theorem Room.slot_mapped {frame : Frame} {requests : List (Request frame)}
    {policy : CpuPolicy} {rsp : BitVec 64} {memory : DataMem}
    (room : Room frame requests policy rsp memory) (slot : Slot frame) :
    Mem.loadInt memory (slot.address rsp) slot.width.bytes ≠ none := by
  apply loadInt_mapped
  intro i hi
  rw [slot.byte_address rsp i]
  exact room.mapped _ (by have := slot.lower; have := slot.upper; omega)

/-- Stores keep every mapped byte. Heap success is not an assumption. -/
theorem Room.store {frame : Frame} {requests : List (Request frame)}
    {policy : CpuPolicy} {rsp : BitVec 64} {memory : DataMem}
    (room : Room frame requests policy rsp memory)
    (address : BitVec 64) (bytes : Nat) (value : Int) :
    Room frame requests policy rsp (Mem.storeInt memory address bytes value) := by
  refine ⟨?_, room.permitted⟩
  intro i hi
  apply Option.isSome_iff_ne_none.mp
  exact Mem.DomainGrows.storeInt memory address bytes value _
    (Option.isSome_iff_ne_none.mpr (room.mapped i hi))

/-- A callee's private bytes lie inside the caller's transitive frame. -/
theorem Room.descend_mapped {frame : Frame} {requests : List (Request frame)}
    {policy : CpuPolicy} {rsp : BitVec 64} {memory : DataMem}
    (room : Room frame requests policy rsp memory) (callee : Frame) (depth : Nat)
    (fits : depth + callee.bytes ≤ frame.bytes) :
    ∀ i < callee.bytes,
      memory.get? (callee.start (rsp - BitVec.ofNat 64 depth) + BitVec.ofNat 64 i) ≠ none := by
  intro i hi
  have total : depth + callee.bytes ≤ frame.bytes := fits
  have base : callee.start (rsp - BitVec.ofNat 64 depth) =
      frame.start rsp + BitVec.ofNat 64 (frame.bytes - (depth + callee.bytes)) := by
    have sum : frame.bytes = (depth + callee.bytes) + (frame.bytes - (depth + callee.bytes)) := by omega
    have expanded := congrArg (BitVec.ofNat 64) sum
    rw [BitVec.ofNat_add] at expanded
    simp only [Frame.start, expanded, BitVec.ofNat_add, ← BitVec.sub_sub,
      BitVec.sub_add_cancel]
  rw [base, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact room.mapped _ (by omega)


/-- Translate a callee slot by the call-site depth in the parent frame. -/
def Slot.shift {callee : Frame} (slot : Slot callee) (parent : Frame) (depth : Nat)
    (fits : depth + callee.bytes ≤ parent.bytes) : Slot parent where
  depth := depth + slot.depth
  width := slot.width
  lower := by have := slot.lower; omega
  upper := by have := slot.upper; omega

theorem Slot.shift_address {callee : Frame} (slot : Slot callee) (parent : Frame)
    (depth : Nat) (fits : depth + callee.bytes ≤ parent.bytes) (rsp : BitVec 64) :
    (slot.shift parent depth fits).address rsp =
      slot.address (rsp - BitVec.ofNat 64 depth) := by
  simp only [Slot.address, Slot.shift, BitVec.ofNat_add, BitVec.sub_sub]

def Request.shift {callee : Frame} (request : Request callee) (parent : Frame) (depth : Nat)
    (fits : depth + callee.bytes ≤ parent.bytes) : Request parent :=
  ⟨request.use, request.slot.shift parent depth fits⟩

theorem Request.shift_access {callee : Frame} (request : Request callee) (parent : Frame)
    (depth : Nat) (fits : depth + callee.bytes ≤ parent.bytes) (rsp : BitVec 64) :
    (request.shift parent depth fits).access rsp =
      request.access (rsp - BitVec.ofNat 64 depth) := by
  cases request with
  | mk use slot =>
    cases use <;> simp only [Request.shift, Request.access, Slot.shift_address] <;> rfl

/-- Exact list inclusion carries both the access kind and width to a callee. -/
theorem Room.descend {parent : Frame} {requests : List (Request parent)}
    {policy : CpuPolicy} {rsp : BitVec 64} {memory : DataMem}
    (room : Room parent requests policy rsp memory) (callee : Frame) (depth : Nat)
    (fits : depth + callee.bytes ≤ parent.bytes) (calleeRequests : List (Request callee))
    (included : ∀ request ∈ calleeRequests, request.shift parent depth fits ∈ requests) :
    Room callee calleeRequests policy (rsp - BitVec.ofNat 64 depth) memory := by
  refine ⟨room.descend_mapped callee depth fits, ?_⟩
  intro request member
  rw [← request.shift_access parent depth fits rsp]
  exact room.permitted _ (included request member)

/-- A public heap read retains its success or its exact fault and projected RAM. -/
theorem readRam_public (frame : Frame) (policy : CpuPolicy) (rsp : BitVec 64)
    (memory : DataMem) (address : BitVec 64) (width : Width)
    (separate : ByteDisjoint (frame.start rsp) frame.bytes address width.bytes) :
    readRam policy (hideRam (frame.privateByte rsp) memory) address width =
      (readRam policy memory address width).mapError
        (fun failure => (failure.1, hideRam (frame.privateByte rsp) failure.2)) := by
  simp only [readRam, Frame.privateByte,
    hideRam_load_separate (frame.start rsp) address frame.bytes width.bytes memory separate]
  split
  · cases Mem.loadInt memory address width.bytes <;> rfl
  · rfl

end Lift.P2.Total.Stack
