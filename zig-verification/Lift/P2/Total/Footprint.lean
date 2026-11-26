module

public import Lift.P2.Total.Memory

@[expose] public section

namespace Lift.P2.Total

/-- Two byte ranges do not meet, including when an address wraps modulo 2^64. -/
def ByteDisjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  ∀ i < n, ∀ j < k, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j

theorem ByteDisjoint.symm {a b : BitVec 64} {n k : Nat}
    (separate : ByteDisjoint a n b k) : ByteDisjoint b k a n := by
  intro j hj i hi equal
  exact separate i hi j hj equal.symm

theorem loadInt_storeInt_separate (memory : DataMem) (a b : BitVec 64)
    (n k : Nat) (value : Int) (separate : ByteDisjoint a n b k) :
    Mem.loadInt (Mem.storeInt memory a n value) b k = Mem.loadInt memory b k := by
  apply Mem.loadInt_congr
  intro j hj
  apply Mem.get?_storeInt_of_ne
  intro i hi equal
  exact separate i hi j hj equal.symm

/-- A successful store preserves each disjoint load. No object size is invented. -/
theorem writeRam_preserves_load (policy : CpuPolicy) (memory memory' : DataMem)
    (a b : BitVec 64) (width : Width) (k : Nat) (value : width.type)
    (separate : ByteDisjoint a width.bytes b k)
    (stored : writeRam policy memory a width value = .ok memory') :
    Mem.loadInt memory' b k = Mem.loadInt memory b k := by
  unfold writeRam at stored
  split at stored
  · split at stored
    · cases stored
      exact loadInt_storeInt_separate _ _ _ _ _ _ separate
    · cases stored
  · cases stored

end Lift.P2.Total
