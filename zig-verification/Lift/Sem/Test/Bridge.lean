module

public import Lift.Sem.Bridge
public import Lift.Sem.HeapBytesSound
public import Lift.Pilot.Call
public import Lift.Trusted.Test.Mem
import all Kraken.Mem

@[expose] public section

/-! Tests of `Lift/Sem/Bridge.lean`: `Mem.has` and `Heap.Holds` on a concrete memory, a heap with
another field order, two writable objects that overlap, two read-only objects that overlap, the
owned bytes, the modular and the natural byte ranges with and without wrap, the return word and
the stack room; the byte-range permission of `Fn.CallB` (`permits_iff`, `Fn.EntryB.holds_permits`) with a
policy that permits the byte reads of a slot and a policy that permits only its word. -/

namespace Lift.Sem.Test.Bridge

open Lift.P2.Total Lift.Sem Lift.Sem.Bridge Lift.Trusted Lift.Trusted.Test.Mem

/-- A policy that permits each access. -/
def polAll : CpuPolicy := ⟨fun _ => true⟩

/-- The words `2` and `1` at `0x1000`, two zero words of stack room at `0x7ff0`, the return word
`0x200000` at `0x8000`. -/
def m0 : DataMem :=
  (∅ : DataMem) |>.storeInt 0x1000 8 2 |>.storeInt 0x1008 8 1
    |>.storeInt 0x7ff0 8 0 |>.storeInt 0x7ff8 8 0 |>.storeInt 0x8000 8 0x200000

macro "read_m0" : tactic =>
  `(tactic| (simp (disch := decide) only [readRam, m0, load_past, load_at, Width.bytes]; rfl))

/-- The fields `[2, 1]` at `0x1000`, the order of the memory. -/
def oRev : Object := ⟨0x1000, [⟨.W64, 2⟩, ⟨.W64, 1⟩], false⟩

/-- The fields `[1, 2]` at `0x1000`: the same values in the other order. -/
def oFwd : Object := ⟨0x1000, [⟨.W64, 1⟩, ⟨.W64, 2⟩], false⟩

/-- The first word as a writable object. -/
def oW : Object := ⟨0x1000, [⟨.W64, 2⟩], true⟩

theorem has_rev : Mem.has polAll m0 oRev := by
  refine ⟨by decide, ?_⟩
  simp only [oRev, Trusted.offsets, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨⟨by read_m0, nofun⟩, ⟨by read_m0, nofun⟩⟩

theorem has_w : Mem.has polAll m0 oW := by
  refine ⟨by decide, ?_⟩
  simp only [oW, Trusted.offsets, List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact ⟨by read_m0, fun _ => rfl⟩

theorem not_has_fwd : ¬ Mem.has polAll m0 oFwd := by
  intro h
  have h1 := (h.2 (0, ⟨.W64, 1⟩) (by simp [oFwd, Trusted.offsets])).1
  have h2 : readRam polAll m0 (oFwd.addr + BitVec.ofNat 64 0) .W64 = .ok 2 := by
    simp (disch := decide) only [oFwd, readRam, m0, load_past, load_at, Width.bytes]
    rfl
  rw [h2] at h1
  injection h1 with e
  revert e
  decide

/-! ### `holds_iff` -/

theorem holds_rev : Heap.Holds polAll [toObj oRev] m0 :=
  (holds_iff _ _ _).mpr ⟨by simp only [List.mem_singleton, forall_eq]; exact has_rev,
    List.pairwise_singleton _ _⟩

/-- `Mem.has` does not follow from `Holds` of a heap with another field order. -/
example : ¬ (Heap.Holds polAll [toObj oRev] m0 → Mem.has polAll m0 oFwd) :=
  fun h => not_has_fwd (h holds_rev)

/-- `Holds` of a heap gives `Mem.has` of its objects. -/
example : Mem.has polAll m0 oRev :=
  ((holds_iff polAll [oRev] m0).mp holds_rev).1 _ List.mem_cons_self

/-- Two writable objects that overlap: each is in the memory, but the heap is not held. -/
example : ¬ Heap.Holds polAll [toObj oW, toObj oW] m0 := by
  intro h
  have := ((holds_iff polAll [oW, oW] m0).mp h).2
  revert this
  unfold Separate Apart
  decide

/-- Two read-only objects that overlap: the heap is held. -/
example : Heap.Holds polAll [toObj oRev, toObj oRev] m0 :=
  (holds_iff polAll [oRev, oRev] m0).mpr
    ⟨(by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self, forall_eq]; exact has_rev),
      (by unfold Separate Apart; decide)⟩

/-! ### Owned bytes -/

example : Heap.Owned [toObj oW] 0x1007 :=
  (owned_iff [oW] 0x1007).mpr ⟨oW, List.mem_cons_self, rfl, by unfold InBytes oW; decide⟩

example : ¬ Heap.Owned [toObj oW] 0x1008 := by
  change ¬ Heap.Owned ([oW].map toObj) 0x1008
  rw [owned_iff]
  rintro ⟨o, ho, -, hb⟩
  simp only [List.mem_singleton] at ho
  subst ho
  revert hb
  unfold InBytes
  decide

/-- A read-only object has no owned byte. -/
example : ¬ Heap.Owned [toObj oRev] 0x1000 := by
  change ¬ Heap.Owned ([oRev].map toObj) 0x1000
  rw [owned_iff]
  rintro ⟨o, ho, hw, -⟩
  simp only [List.mem_singleton] at ho
  subst ho
  cases hw

/-! ### Byte ranges -/

example : SysV.Below 0x8000 16 0x7ff0 ↔ InBytes (0x8000 - BitVec.ofNat 64 16) 16 0x7ff0 :=
  below_iff (by decide)

example : SysV.Below 0x8000 16 0x7ff0 ∧ ¬ SysV.Below 0x8000 16 0x8000 := by
  unfold SysV.Below; decide

/-- With `sp < n` the room wraps: the byte `4` is below `8` modulo `2^64`, but it is not in the
natural range from `8 - 16`. -/
example : SysV.Below 8 16 4 ∧ ¬ InBytes (8 - BitVec.ofNat 64 16) 16 4 := by
  unfold SysV.Below InBytes; decide

/-- A range that wraps: the modular distance is small, the natural range is empty of `b`. -/
example : ((2 : BitVec 64) - (BitVec.allOnes 64)).toNat < 8 ∧ ¬ InBytes (BitVec.allOnes 64) 8 2 := by
  unfold InBytes; decide

example : ¬ (toObj oW).Covers 0x1008 ∧ (toObj oW).Covers 0x1000 := by
  rw [covers_toObj, covers_toObj]; unfold InBytes oW; decide

/-! ### The return word and the stack room -/

/-- A state with `rsp = 0x8000` and the memory `m0`. -/
def s0 : MachineState := ⟨{ regs := { rsp := 0x8000, rdi := 0x1000 }, dmem := m0 }, 0⟩

theorem ret_s0 : Mem.has polAll m0 (retWord s0 0x200000) := by
  refine ⟨by decide, ?_⟩
  simp only [retWord, s0, Trusted.offsets, List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact ⟨by read_m0, nofun⟩

example : SysV.retAddr s0 = some 0x200000 := (ret_of_has ret_s0).2.1

/-- A return word that wraps past `2^64` is not in the memory. -/
example : ¬ Mem.has polAll m0 (retWord ⟨{ regs := { rsp := 0xfffffffffffffffc }, dmem := m0 }, 0⟩ 0) :=
  fun h => absurd h.1 (by decide)

theorem room_s0 : SysV.StackRoom polAll s0 16 := by
  refine stackRoom_of_has (ws := [0, 0]) (by decide) rfl ⟨by decide, ?_⟩
  simp only [s0, Trusted.offsets, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq]
  exact ⟨⟨by read_m0, fun _ => rfl⟩, ⟨by read_m0, fun _ => rfl⟩⟩

/-- A stack object in a memory without the word at `0x7ff0` is not in the memory. -/
example : ¬ Mem.has polAll ((∅ : DataMem).storeInt 0x7ff8 8 0)
    ⟨s0.data.regs.rsp.toBitVec - BitVec.ofNat 64 16, [⟨.W64, 0⟩, ⟨.W64, 0⟩], true⟩ := by
  intro h
  have hr := (h.2 (0, ⟨.W64, 0⟩) (by simp [Trusted.offsets])).1
  have hn : Mem.loadInt ((∅ : DataMem).storeInt 0x7ff8 8 0)
      (s0.data.regs.rsp.toBitVec - BitVec.ofNat 64 16 + BitVec.ofNat 64 0) 8 = none := by
    rw [load_past (by decide)]
    simp only [Mem.loadInt, Mem.loadBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.getElem?_empty]
    decide
  obtain ⟨-, v, hv⟩ := readRam_ok hr
  rw [show Width.W64.bytes = 8 from rfl, hn] at hv
  cases hv

/-- The first argument is `rdi`. -/
example : s0.data.regs.rdi.toBitVec = 0x1000 :=
  rdi_of_argsIn ⟨by decide, by simp [argRegs, s0, Field.InReg, Width.bits]⟩

/-! ### The bridge of `Fn.CallB`: `PermitsRange` and `Heap.Permits`

A slot of 8 bytes at `0x2000` with the byte `0x44` at offset 4 (the `kind` byte of a slot). The
policy `polAll` permits the read of the byte; the policy `polExact` permits only the read of the
word, so `Mem.has` holds under it and `Heap.Permits` does not. -/

/-- The word `0x0000004400000011` at `0x2000`. -/
def m1 : DataMem := (∅ : DataMem) |>.storeInt 0x2000 8 0x0000004400000011

/-- The slot as a read-only object of one word. -/
def oK : Object := ⟨0x2000, [⟨.W64, 0x0000004400000011⟩], false⟩

/-- Only the read of 8 bytes at `0x2000` is permitted. -/
def polExact : CpuPolicy := ⟨fun
  | .read a w => a == 0x2000 && w == .W64
  | _ => false⟩

theorem has_k (policy : CpuPolicy) (hp : policy.permits (.read 0x2000 .W64) = true) :
    Mem.has policy m1 oK := by
  refine ⟨by decide, ?_⟩
  simp only [oK, Trusted.offsets, List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  refine ⟨?_, nofun⟩
  simp (disch := decide) only [readRam, m1, load_at, Width.bytes, BitVec.add_zero, hp]
  rfl

theorem holds_k (policy : CpuPolicy) (hp : policy.permits (.read 0x2000 .W64) = true) :
    Heap.Holds policy [toObj oK] m1 :=
  (holds_iff _ _ _).mpr ⟨by simp only [List.mem_singleton, forall_eq]; exact has_k policy hp,
    List.pairwise_singleton _ _⟩

/-- The concrete instance: `PermitsRange` of the slot gives `Heap.Permits` of its heap. -/
theorem permits_k : Heap.Permits polAll [toObj oK] :=
  (permits_iff polAll [oK]).mpr fun _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩

/-- The byte fallback load of the `kind` byte. -/
theorem loadB_k : Heap.loadB [toObj oK] (0x2000 + BitVec.ofNat 64 4) .W8 = .ok 0x44 := by
  rfl

/-- With `Holds` and `Permits`, the byte load of the model is the read of the memory. -/
example : readRam polAll m1 (0x2000 + BitVec.ofNat 64 4) .W8 = .ok 0x44 :=
  Heap.loadB_sound (holds_k polAll rfl) permits_k loadB_k

/-- The exact load of the model has no cell of 8 bits at the byte: only `loadB` gives it. -/
example : Heap.load [toObj oK] (0x2000 + BitVec.ofNat 64 4) .W8 =
    .stuck "load: no cell of this width at this address" := rfl

/-- The negative instance: `polExact` holds the heap (the exact word), but has no byte-range
permission, and the read of the byte is not permitted. -/
example : Heap.Holds polExact [toObj oK] m1 := holds_k polExact rfl

theorem not_permits_exact : ¬ Heap.Permits polExact [toObj oK] := fun h => by
  have := (h (toObj oK) List.mem_cons_self 4 .W8 (by decide)).1
  revert this
  decide

example : ¬ ∀ o ∈ [oK], PermitsRange polExact o.addr o.size o.writable :=
  fun h => not_permits_exact ((permits_iff polExact [oK]).mpr h)

/-- No `Fn.EntryB` state has the slot under `polExact`: the bridge gives `Heap.Permits`. -/
example (f : Fn) (args : List Field) (ra : BitVec 64) (s : MachineState) :
    ¬ f.EntryB polExact args [oK] ra s :=
  fun h => not_permits_exact (Fn.EntryB.holds_permits h).2

/-- The read of the byte under `polExact` is not permitted: it is not the value of `loadB`. -/
example : polExact.permits (.read (0x2000 + BitVec.ofNat 64 4) .W8) = false := by decide

/-- The bridge gives `Holds` and `Permits` of the heap of each `Fn.EntryB` state. -/
example (f : Fn) (policy : CpuPolicy) (args : List Field) (ra : BitVec 64) (s : MachineState)
    (h : f.EntryB policy args [oK] ra s) :
    Heap.Holds policy [toObj oK] s.data.dmem ∧ Heap.Permits policy [toObj oK] :=
  Fn.EntryB.holds_permits h

end Lift.Sem.Test.Bridge
