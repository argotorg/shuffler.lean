module

public import Lift.Sem.HeapBytesObj

@[expose] public section

/-! The soundness of the byte fallback store `Heap.storeB`: with the memory and the policy that hold
the heap, and the byte-range permission `Heap.Permits` (decision D38), a `storeB` that gives `h'` is
a `writeRam` that gives a memory that holds `h'`. The exact-cell case is `Heap.store_sound`. In the
fallback case, one writable object spans the access; the write is inside it. The parts for the
other objects and for the written object are in `Lift/Sem/HeapBytesStore.lean` and
`Lift/Sem/HeapBytesObj.lean`. -/

namespace Lift.Sem

open Lift.P2.Total Lift.Sem.ByteLemmas

/-! ### `Heap.Permits` -/

/-- `Heap.Permits` depends on the address, the size and the `writable` flag of each object. -/
theorem Heap.Permits_map {policy : CpuPolicy} {h : Heap} {f : Obj → Obj}
    (hp : h.Permits policy)
    (hf : ∀ o ∈ h, (f o).addr = o.addr ∧ (f o).size = o.size ∧ (f o).writable = o.writable) :
    Heap.Permits policy (h.map f) := by
  intro o' ho' k w hk
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
  obtain ⟨e₁, e₂, e₃⟩ := hf o ho
  rw [e₁, e₃]
  rw [e₂] at hk
  exact hp o ho k w hk

/-- The exact-cell store keeps the permission. -/
theorem Heap.Permits_store {policy : CpuPolicy} {h h' : Heap} {a : BitVec 64} {w : Width}
    {v : w.type} (hs : h.store a w v = .ok h') (hp : h.Permits policy) : h'.Permits policy := by
  unfold Heap.store at hs
  split at hs
  · cases hs
    exact Heap.Permits_map hp fun o _ => ⟨Obj.set_addr _ _ _ _, Obj.set_size _ _ _ _,
      Obj.set_writable _ _ _ _⟩
  · split at hs <;> cases hs

/-- The byte fallback store keeps the permission. -/
theorem Heap.Permits_storeB {policy : CpuPolicy} {h h' : Heap} {a : BitVec 64} {w : Width}
    {v : w.type} (hs : h.storeB a w v = .ok h') (hp : h.Permits policy) : h'.Permits policy := by
  unfold Heap.storeB at hs
  split at hs
  · exact Heap.Permits_store hs hp
  · split at hs
    · cases hs
      exact Heap.Permits_map hp fun o _ => ⟨Obj.setBytes_addr _ _ _ _, Obj.setBytes_size _ _ _ _,
        Obj.setBytes_writable _ _ _ _⟩
    · split at hs <;> cases hs

/-! ### The objects that a store does not change -/

/-- Two objects that span the same access are not apart. -/
theorem Obj.not_apart_of_spans {o o' : Obj} {a : BitVec 64} {w : Width} (h : o.Spans a w)
    (h' : o'.Spans a w) : ¬ o.Apart o' := by
  unfold Obj.Spans at h h'
  unfold Obj.Apart
  have := width_bytes_pos w
  omega

/-- A writable object that spans the access is the only object that `setBytes` changes. -/
theorem Heap.Holds.setBytes_other {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o o' : Obj} (ho : o ∈ h) (ho' : o' ∈ h) (hne : o' ≠ o)
    (hw : o.writable = true) {a : BitVec 64} {w : Width} (hs : o.Spans a w) {v : w.type} :
    Obj.setBytes a w v o' = o' := by
  by_cases hs' : o'.Spans a w
  · by_cases hw' : o'.writable = true
    · exfalso
      have hapart := pairwise_of_mem
        (R := fun o o' => (o.writable ∨ o'.writable) → o.Apart o')
        (fun h hw' => Or.symm (h (Or.symm hw'))) hh.apart ho ho' (Ne.symm hne)
        (.inl (by simp [hw]))
      exact Obj.not_apart_of_spans hs hs' hapart
    · exact Obj.setBytes_of_not_writable (by simpa using hw')
  · exact Obj.setBytes_of_not_spans hs'

/-- After a store of the bytes of `v` in a writable object that spans the access, the memory with
the stored integer holds the heap of `setBytes`. No permission of the write is needed: the cells keep
their addresses and widths. -/
theorem Heap.Holds.map_setBytes {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} (v : w.type) (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h)
    (hwr : o.writable = true) (hsp : o.Spans a w) :
    Heap.Holds policy (h.map (Obj.setBytes a w v)) (Mem.storeInt m a w.bytes v.toInt) := by
  have hn := hh.noWrap o ho
  have hlt := a.isLt
  obtain ⟨k, ha, hk⟩ : ∃ k, a = o.addr + BitVec.ofNat 64 k ∧ k + w.bytes ≤ o.size := by
    unfold Obj.Spans at hsp
    refine ⟨a.toNat - o.addr.toNat, ?_, by omega⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  subst ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o' ho' x hx
    obtain ⟨o₂, ho₂, rfl⟩ := List.mem_map.mp ho'
    by_cases hne : o₂ = o
    · subst hne
      rw [Obj.setBytes_addr]
      exact Obj.reads_after_storeInt_of_holds hh ho rfl hk hwr x hx
    · rw [Heap.Holds.setBytes_other hh ho ho₂ hne hwr hsp] at hx ⊢
      exact Heap.Holds.other_of_storeInt hh ho hwr hk rfl ho₂ hne x hx
  · intro o' ho' hw' x hx
    obtain ⟨o₂, ho₂, rfl⟩ := List.mem_map.mp ho'
    rw [Obj.setBytes_writable] at hw'
    obtain ⟨x₀, hx₀, e₁, e₂⟩ := Obj.setBytes_offsets _ _ _ _ x hx
    rw [Obj.setBytes_addr, e₁, e₂]
    exact hh.write o₂ ho₂ hw' x₀ hx₀
  · intro o' ho'
    obtain ⟨o₂, ho₂, rfl⟩ := List.mem_map.mp ho'
    rw [Obj.setBytes_addr, Obj.setBytes_size]
    exact hh.noWrap o₂ ho₂
  · rw [List.pairwise_map]
    refine hh.apart.imp fun h' => ?_
    simp only [Obj.Apart, Obj.setBytes_addr, Obj.setBytes_size, Obj.setBytes_writable]
    exact h'

/-- After a `storeB`, some memory holds the new heap. With no `Heap.Permits`: the next access of a
chain of byte stores has a `Holds` (`addStoreHolds` of `Lift/Tactic/HeapField.lean`). -/
theorem Heap.storeB_holds {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.storeB a w v = .ok h') :
    ∃ m', h'.Holds policy m' := by
  unfold Heap.storeB at hs
  split at hs
  · exact let ⟨m', _, hm', _⟩ := Heap.store_sound hh hs; ⟨m', hm'⟩
  · split at hs
    · rename_i hc
      cases hs
      obtain ⟨o, ho, hoc⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hoc
      exact ⟨_, Heap.Holds.map_setBytes v hh ho hoc.1 hoc.2⟩
    · split at hs <;> cases hs

/-! ### Soundness -/

/-- The case of the fallback: a writable object `o` spans the access. -/
theorem Heap.storeB_sound_span {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} (v : w.type) (hh : h.Holds policy m) (hp : h.Permits policy) {o : Obj}
    (ho : o ∈ h) (hwr : o.writable = true) (hsp : o.Spans a w) :
    ∃ m', writeRam policy m a w v = .ok m' ∧ Heap.Holds policy (h.map (Obj.setBytes a w v)) m' ∧
      ∃ o ∈ h, o.writable ∧ ∀ b, ¬ o.Covers b → m'.get? b = m.get? b := by
  have hn := hh.noWrap o ho
  have hwb := width_bytes_pos w
  have hlt := a.isLt
  obtain ⟨k, ha, hk, ea⟩ : ∃ k, a = o.addr + BitVec.ofNat 64 k ∧ k + w.bytes ≤ o.size ∧
      a.toNat = o.addr.toNat + k := by
    unfold Obj.Spans at hsp
    refine ⟨a.toNat - o.addr.toNat, ?_, by omega, by omega⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  subst ha
  have hw := writeRam_ok_of_permits hh hp ho hwr hk v
  refine ⟨_, hw, Heap.Holds.map_setBytes v hh ho hwr hsp, o, ho, hwr, ?_⟩
  · intro b hb
    apply Mem.get?_storeInt_of_ne
    intro i hi e
    apply hb
    subst e
    unfold Obj.Covers
    rw [toNat_add_ofNat (o.addr + BitVec.ofNat 64 k) i (by omega), ea]
    constructor <;> omega

/-- A store of `storeB` is a write of the memory; the memory holds the new heap; each byte outside
the writable object of the store does not change. The statement has the form of `Heap.store_sound`,
with the byte-range permission `Heap.Permits`. -/
theorem Heap.storeB_sound {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hp : h.Permits policy)
    (hs : h.storeB a w v = .ok h') :
    ∃ m', writeRam policy m a w v = .ok m' ∧ h'.Holds policy m' ∧
      ∃ o ∈ h, o.writable ∧ ∀ b, ¬ o.Covers b → m'.get? b = m.get? b := by
  unfold Heap.storeB at hs
  split at hs
  · exact Heap.store_sound hh hs
  · split at hs
    · rename_i hc
      cases hs
      obtain ⟨o, ho, hoc⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hoc
      exact Heap.storeB_sound_span v hh hp ho hoc.1 hoc.2
    · split at hs <;> cases hs

end Lift.Sem
