module

public import Lift.Sem.HeapBytesSound

@[expose] public section

/-! The frame part of the soundness of the byte fallback store `Heap.storeB`: a byte-range write
inside one writable object does not fault (with `Heap.Permits`), and it leaves the bytes apart from
the range, and so each cell of each other object, as they are. The part for the written object
itself is not in this module. -/

namespace Lift.Sem

open Lift.P2.Total Lift.Sem.ByteLemmas

/-- A write that succeeds stores the integer of the value. -/
theorem writeRam_ok_eq {policy : CpuPolicy} {m m' : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (h : writeRam policy m a w v = .ok m') :
    m' = Mem.storeInt m a w.bytes v.toInt := by
  unfold writeRam at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- The write of a byte range inside a writable object does not fault, and gives the store of
the integer of the value. -/
theorem writeRam_ok_of_permits {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) (hp : h.Permits policy) {o : Obj} (ho : o ∈ h)
    (hw : o.writable = true) {k : Nat} {w : Width} (hk : k + w.bytes ≤ o.size) (v : w.type) :
    writeRam policy m (o.addr + BitVec.ofNat 64 k) w v =
      .ok (Mem.storeInt m (o.addr + BitVec.ofNat 64 k) w.bytes v.toInt) := by
  have hperm := (hp o ho k w hk).2 hw
  have hc := Contains.slice (hh.contains ho) k w.bytes
  have hlen : ((o.bytes.drop k).take w.bytes).length = w.bytes := by
    simp only [List.length_take, List.length_drop, Obj.bytes_length]; omega
  have hl := hc.loadInt_eq hlen
  unfold writeRam
  simp only [hperm, ↓reduceIte, hl]

/-- A store of an integer keeps the bytes that are apart from the stored range. -/
theorem storeInt_keeps_apart {m m' : DataMem} {a : BitVec 64} {n : Nat} {x : Int}
    (hm : m' = Mem.storeInt m a n x) {b : BitVec 64} {bs : List UInt8}
    (hd : ByteDisjoint a n b bs.length) :
    m'.Contains b bs ↔ m.Contains b bs := by
  subst hm
  simp only [Mem.Contains.iff]
  have key : ∀ i < bs.length,
      (Mem.storeInt m a n x).get? (b + BitVec.ofNat 64 i) =
        m.get? (b + BitVec.ofNat 64 i) :=
    fun i hi => Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj e => hd j hj i hi e.symm
  constructor <;> intro H i hi
  · rw [← key i hi]; exact H i hi
  · rw [key i hi]; exact H i hi

/-- A write keeps the bytes that are apart from the written range. -/
theorem writeRam_keeps_apart {policy : CpuPolicy} {m m' : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hm : writeRam policy m a w v = .ok m') {b : BitVec 64}
    {bs : List UInt8} (hd : ByteDisjoint a w.bytes b bs.length) :
    m'.Contains b bs ↔ m.Contains b bs :=
  storeInt_keeps_apart (writeRam_ok_eq hm) hd

/-- `Heap.Holds.other_of_write` for the memory with the stored integer: no permission of the
write is needed. -/
theorem Heap.Holds.other_of_storeInt {policy : CpuPolicy} {h : Heap} {m m' : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) (hw : o.writable = true) {k : Nat} {w : Width}
    (hk : k + w.bytes ≤ o.size) {z : Int}
    (hm : m' = Mem.storeInt m (o.addr + BitVec.ofNat 64 k) w.bytes z) {o' : Obj} (ho' : o' ∈ h)
    (hne : o' ≠ o) :
    ∀ x ∈ offsets 0 o'.cells,
      readRam policy m' (o'.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v := by
  intro x hx
  have hr := hh.read o' ho' x hx
  obtain ⟨hperm, -⟩ := readRam_ok hr
  have hc : m.Contains (o'.addr + BitVec.ofNat 64 x.1) x.2.bytes := readRam_contains hr
  have n₀ := hh.noWrap o ho
  have n₁ := hh.noWrap o' ho'
  obtain ⟨e₁, b₁⟩ := Obj.toNat_cell n₁ hx
  have hapart := pairwise_of_mem (R := fun o o' => (o.writable ∨ o'.writable) → o.Apart o')
    (fun h hw' => Or.symm (h (Or.symm hw'))) hh.apart ho ho' (Ne.symm hne) (.inl (by simp [hw]))
  unfold Obj.Apart at hapart
  have ea : (o.addr + BitVec.ofNat 64 k).toNat = o.addr.toNat + k :=
    toNat_add_ofNat _ _ (by unfold Obj.size at hk n₀; have := width_bytes_pos w; omega)
  have hd : ByteDisjoint (o.addr + BitVec.ofNat 64 k) w.bytes
      (o'.addr + BitVec.ofNat 64 x.1) x.2.bytes.length := by
    rw [Cell.bytes_length]
    apply byteDisjoint_of_nat (by unfold Obj.size at hk n₀; omega) (by omega)
    rw [ea, e₁]
    omega
  exact readRam_of_contains ((storeInt_keeps_apart hm hd).mpr hc) hperm

/-- The frame part of `Heap.storeB_sound`: a write of a byte range inside a writable object keeps
the value of each cell of each other object. -/
theorem Heap.Holds.other_of_write {policy : CpuPolicy} {h : Heap} {m m' : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) (hw : o.writable = true) {k : Nat} {w : Width}
    (hk : k + w.bytes ≤ o.size) {v : w.type}
    (hm : writeRam policy m (o.addr + BitVec.ofNat 64 k) w v = .ok m') {o' : Obj} (ho' : o' ∈ h)
    (hne : o' ≠ o) :
    ∀ x ∈ offsets 0 o'.cells,
      readRam policy m' (o'.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v :=
  hh.other_of_storeInt ho hw hk (writeRam_ok_eq hm) ho' hne

end Lift.Sem
