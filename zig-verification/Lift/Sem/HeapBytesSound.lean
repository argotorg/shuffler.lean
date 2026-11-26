module

public import Lift.Sem.HeapBytes
public import Lift.Sem.ByteLemmas
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

/-! The soundness of the byte fallback load `Heap.loadB`: with the memory and the policy that hold
the heap, and a permission for each byte range inside an object (decision D38), a `loadB` that
gives `v` is a `readRam` that gives `v`. `Heap.Holds` permits only the exact access of each cell;
a narrower read inside a cell needs `Heap.Permits`. -/

namespace Lift.Sem

open Lift.P2.Total Lift.Sem.ByteLemmas

/-- The byte-range permission of D38: each read of `w` bytes inside an object is permitted, and
each write of an access inside a writable object is permitted. It is the `Heap` form of
`PermitsRange` of `Lift/Pilot/Call.lean`, which this module does not import. -/
def Heap.Permits (policy : CpuPolicy) (h : Heap) : Prop :=
  ∀ o ∈ h, ∀ (k : Nat) (w : Width), k + w.bytes ≤ o.size →
    policy.permits (.read (o.addr + BitVec.ofNat 64 k) w) = true ∧
      (o.writable = true → policy.permits (.write (o.addr + BitVec.ofNat 64 k) w) = true)

/-! ### Bytes of cells and objects -/

/-- The bytes of the cell in little-endian order. -/
def Cell.bytes (c : Cell) : List UInt8 := Int.toBytes c.w.bytes c.v.toInt

theorem Obj.bytes_eq (o : Obj) : o.bytes = o.cells.flatMap Cell.bytes := rfl

theorem Cell.bytes_length (c : Cell) : c.bytes.length = c.w.bytes := Int.toBytes_length _ _

theorem flatMap_bytes_length (cs : List Cell) :
    (cs.flatMap Cell.bytes).length = (cs.map fun c => c.w.bytes).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, ih, Cell.bytes_length]

theorem Obj.bytes_length (o : Obj) : o.bytes.length = o.size := flatMap_bytes_length _

/-! ### Reads of the memory -/

/-- A read of a cell gives its bytes. -/
theorem readRam_contains {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (h : readRam policy m a w = .ok v) :
    m.Contains a (Int.toBytes w.bytes v.toInt) := by
  obtain ⟨-, x, hx⟩ := readRam_ok h
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hl := Mem.length_of_loadBytes_eq_some hb
  unfold readRam at h
  simp only [Mem.loadInt, hb] at h
  split at h
  · rename_i hp
    simp only [Option.map_some] at h
    cases h
    have e : Int.toBytes w.bytes (BitVec.ofInt w.bits (Int.ofBytes bs)).toInt = bs := by
      have := toBytes_toInt_ofInt_ofBytes w.bytes bs hl
      rwa [← width_bits_eq w] at this
    rw [e]
    unfold Mem.Contains
    rw [← hl] at hb
    exact hb
  · cases h

/-- The memory holds the bytes of the cells from offset `n`. -/
theorem contains_offsets {policy : CpuPolicy} {m : DataMem} (base : BitVec 64) :
    ∀ (n : Nat) (cs : List Cell),
      (∀ x ∈ offsets n cs, readRam policy m (base + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) →
      m.Contains (base + BitVec.ofNat 64 n) (cs.flatMap Cell.bytes)
  | n, [], _ => by
    apply Mem.Contains.iff.mpr; intro i hi; simp at hi
  | n, c :: cs, h => by
    simp only [List.flatMap_cons]
    apply Contains.append
    · exact readRam_contains (h (n, c) (by simp [offsets]))
    · have ih := contains_offsets base (n + c.w.bytes) cs
        (fun x hx => h x (by simp [offsets, hx]))
      rw [Cell.bytes_length, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ih

/-- The memory holds the bytes of each object of the heap. -/
theorem Heap.Holds.contains {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) : m.Contains o.addr o.bytes := by
  have := contains_offsets (policy := policy) (m := m) o.addr 0 o.cells (hh.read o ho)
  simpa [Obj.bytes_eq] using this

/-- A read inside an object gives the value of the covered bytes, little-endian. -/
theorem readRam_slice {policy : CpuPolicy} {h : Heap} {m : DataMem} (hh : h.Holds policy m)
    {o : Obj} (ho : o ∈ h) {a : BitVec 64} {w : Width} {k : Nat}
    (ha : a = o.addr + BitVec.ofNat 64 k) (hk : k + w.bytes ≤ o.size)
    (hp : policy.permits (.read a w) = true) :
    readRam policy m a w =
      .ok (BitVec.ofInt w.bits (Int.ofBytes ((o.bytes.drop k).take w.bytes))) := by
  have hc := Contains.slice (hh.contains ho) k w.bytes
  rw [← ha] at hc
  have hlen : ((o.bytes.drop k).take w.bytes).length = w.bytes := by
    simp only [List.length_take, List.length_drop, Obj.bytes_length]; omega
  unfold readRam
  simp only [hp, ↓reduceIte]
  rw [Mem.loadInt, hc.loadBytes_eq hlen]
  rfl

/-- A cell whose bytes are in the memory, and that the policy lets us read, reads back. -/
theorem readRam_of_contains {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {c : Cell}
    (h : m.Contains a c.bytes) (hp : policy.permits (.read a c.w) = true) :
    readRam policy m a c.w = .ok c.v := by
  have hl := c.bytes_length
  unfold readRam
  simp only [hp, ↓reduceIte]
  rw [Mem.loadInt, h.loadBytes_eq hl]
  simp only [Option.map_some]
  congr 1
  unfold Cell.bytes
  rw [BitVec.ofInt_ofBytes_toBytes _ _ (width_bits_eq c.w), BitVec.ofInt_toInt]

/-- The cells from offset `n` read back from the bytes in the memory. -/
theorem read_of_contains {policy : CpuPolicy} {m : DataMem} (base : BitVec 64) :
    ∀ (n : Nat) (cs : List Cell),
      m.Contains (base + BitVec.ofNat 64 n) (cs.flatMap Cell.bytes) →
      (∀ x ∈ offsets n cs, policy.permits (.read (base + BitVec.ofNat 64 x.1) x.2.w) = true) →
      ∀ x ∈ offsets n cs, readRam policy m (base + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v
  | n, [], _, _ => by simp [offsets]
  | n, c :: cs, h, hp => by
    simp only [List.flatMap_cons] at h
    intro x hx
    simp only [offsets, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact readRam_of_contains (Contains.left h) (hp (n, c) (by simp [offsets]))
    · have hr := Contains.right h
      rw [Cell.bytes_length, BitVec.add_assoc, ← BitVec.ofNat_add] at hr
      exact read_of_contains base (n + c.w.bytes) cs hr
        (fun x hx => hp x (by simp [offsets, hx])) x hx

/-! ### `loadB` -/

/-- A load of the bytes of an object: the offset of the access, and the value of the bytes. -/
theorem Obj.loadBytes_spec {o : Obj} {a : BitVec 64} {w : Width} {v : w.type}
    (h : o.loadBytes a w = some v) :
    ∃ k, a = o.addr + BitVec.ofNat 64 k ∧ k + w.bytes ≤ o.size ∧
      v = BitVec.ofInt w.bits (Int.ofBytes ((o.bytes.drop k).take w.bytes)) := by
  unfold Obj.loadBytes at h
  split at h
  · rename_i hs
    cases h
    obtain ⟨h1, h2⟩ := hs
    have hlt := a.isLt
    refine ⟨a.toNat - o.addr.toNat, ?_, by omega, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · cases h

/-- A load of `loadB` is a read of the memory. -/
theorem Heap.loadB_sound {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hp : h.Permits policy)
    (hl : h.loadB a w = .ok v) : readRam policy m a w = .ok v := by
  unfold Heap.loadB at hl
  split at hl
  · rename_i v' hl'
    cases hl
    exact Heap.load_sound hh hl'
  · split at hl
    · rename_i v' hf
      cases hl
      obtain ⟨o, ho, hlb⟩ := List.exists_of_findSome?_eq_some hf
      obtain ⟨k, ha, hk, rfl⟩ := Obj.loadBytes_spec hlb
      have hperm := (hp o ho k w hk).1
      rw [← ha] at hperm
      exact readRam_slice hh ho ha hk hperm
    · cases hl

end Lift.Sem
