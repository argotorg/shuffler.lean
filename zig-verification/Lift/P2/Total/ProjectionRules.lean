module

public import Lift.P2.Total.Projection

@[expose] public section

namespace Lift.P2.Total

/-- A finite modular byte range. No order on machine addresses is assumed. -/
def byteRange (start : BitVec 64) (bytes : Nat) (address : BitVec 64) : Bool :=
  (List.range bytes).any (fun offset => address == start + BitVec.ofNat 64 offset)

theorem byteRange_inside (start : BitVec 64) (bytes offset : Nat) (inside : offset < bytes) :
    byteRange start bytes (start + BitVec.ofNat 64 offset) = true := by
  apply List.any_eq_true.mpr
  exact ⟨offset, List.mem_range.mpr inside, by simp⟩

theorem byteRange_outside (start address : BitVec 64) (bytes count offset : Nat)
    (separate : ByteDisjoint start bytes address count) (inside : offset < count) :
    byteRange start bytes (address + BitVec.ofNat 64 offset) = false := by
  apply Bool.eq_false_iff.mpr
  intro member
  obtain ⟨i, hi, equal⟩ := List.any_eq_true.mp member
  exact separate i (List.mem_range.mp hi) offset inside (of_decide_eq_true equal).symm

theorem hideRam_store_range (start : BitVec 64) (bytes : Nat) (memory : DataMem) (value : Int) :
    hideRam (byteRange start bytes) (Mem.storeInt memory start bytes value) =
      hideRam (byteRange start bytes) memory := by
  exact hideRam_storeInt _ _ _ _ _ (fun i hi => byteRange_inside start bytes i hi)

theorem hideRam_load_separate (start address : BitVec 64) (bytes count : Nat) (memory : DataMem)
    (separate : ByteDisjoint start bytes address count) :
    Mem.loadInt (hideRam (byteRange start bytes) memory) address count =
      Mem.loadInt memory address count := by
  exact hideRam_loadInt _ _ _ _ (fun i hi => byteRange_outside start address bytes count i separate hi)

/-- The eight scratch bytes immediately below the initial RSP. -/
def stackScratch (rsp : BitVec 64) : BitVec 64 → Bool := byteRange (rsp - 8#64) 8

theorem stackScratch_separate_return (rsp : BitVec 64) : ByteDisjoint (rsp - 8#64) 8 rsp 8 := by
  intro i hi j hj equal
  have shifted := congrArg (fun x => x + 8#64) equal
  have rearrange (a b : BitVec 64) : a - 8#64 + b + 8#64 = a + b := by
    calc
      a - 8#64 + b + 8#64 = a - 8#64 + (b + 8#64) := BitVec.add_assoc _ _ _
      _ = a - 8#64 + (8#64 + b) := by rw [BitVec.add_comm b]
      _ = (a - 8#64 + 8#64) + b := (BitVec.add_assoc _ _ _).symm
      _ = a + b := by rw [BitVec.sub_add_cancel]
  rw [rearrange, BitVec.add_assoc] at shifted
  have cancel := (BitVec.add_right_inj rsp).mp shifted
  have smallI : i < 2^64 := by omega
  have smallJ : j < 2^64 := by omega
  have value := congrArg BitVec.toNat cancel
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallI,
    Nat.mod_eq_of_lt smallJ] at value
  omega

theorem stackScratch_hide_store (rsp : BitVec 64) (memory : DataMem) (value : Int) :
    hideRam (stackScratch rsp) (Mem.storeInt memory (rsp - 8#64) 8 value) =
      hideRam (stackScratch rsp) memory :=
  hideRam_store_range _ _ _ _

theorem stackScratch_public_return (rsp : BitVec 64) (memory : DataMem) :
    Mem.loadInt (hideRam (stackScratch rsp) memory) rsp 8 = Mem.loadInt memory rsp 8 :=
  hideRam_load_separate _ _ _ _ _ (stackScratch_separate_return rsp)

theorem stackScratch_preserves_return (rsp : BitVec 64) (memory : DataMem) (value : Int) :
    Mem.loadInt (Mem.storeInt memory (rsp - 8#64) 8 value) rsp 8 = Mem.loadInt memory rsp 8 :=
  loadInt_storeInt_separate _ _ _ _ _ _ (stackScratch_separate_return rsp)

theorem writeRam_mapped (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (width : Width) (value : width.type)
    (allowed : policy.permits (.write address width) = true)
    (mapped : Mem.loadInt memory address width.bytes ≠ none) :
    writeRam policy memory address width value =
      .ok (Mem.storeInt memory address width.bytes value.toInt) := by
  simp only [writeRam, allowed, ↓reduceIte]
  cases read : Mem.loadInt memory address width.bytes with
  | none => exact (mapped read).elim
  | some old => rfl

theorem readRam_stored64 (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (value : BitVec 64) (allowed : policy.permits (.read address .W64) = true) :
    readRam policy (Mem.storeInt memory address 8 value.toInt) address .W64 = .ok value := by
  simp [readRam, allowed, Width.bytes, Mem.loadInt_storeInt_64,
    BitVec.ofInt_ofBytes_toBytes_64]

theorem readRam_storeInt64 (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (value : Int) (allowed : policy.permits (.read address .W64) = true) :
    readRam policy (Mem.storeInt memory address 8 value) address .W64 =
      .ok (BitVec.ofInt 64 value) := by
  simp [readRam, allowed, Width.bytes, Mem.loadInt_storeInt_64,
    BitVec.ofInt_ofBytes_toBytes_64]

end Lift.P2.Total
