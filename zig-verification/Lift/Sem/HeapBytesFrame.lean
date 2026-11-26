module

public import Lift.Sem.HeapBytesStoreSound
public import Lift.Sem.HeapLemmas
public import Lift.Sem.StackPush

@[expose] public section

/-! The frame lemmas of the byte fallback store `Heap.storeB`, in the form of the lemmas of
`Heap.store` in `Lift/Sem/HeapLemmas.lean` (`Heap.owned_store`, `Heap.store_frame`,
`owned_of_store`). The proof texts of `refines_l2p` for a function in the form `Fn.CallB` use them
in place of those of `Heap.store` (decision D40). -/

namespace Lift.Sem

open Lift.P2.Total

/-- Heap order does not change byte-range permissions. -/
theorem Heap.Permits_perm {policy : CpuPolicy} {h h' : Heap} (hp : h.Perm h') :
    h.Permits policy ↔ h'.Permits policy :=
  ⟨fun hm o ho => hm o (hp.symm.subset ho), fun hm o ho => hm o (hp.subset ho)⟩

/-- A byte fallback store keeps the covered bytes. -/
theorem Heap.covered_storeB {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.storeB a w v = .ok h') (b : BitVec 64) : Covered h' b ↔ Covered h b := by
  unfold Heap.storeB at hs
  split at hs
  · exact Heap.covered_store hs b
  · split at hs
    · cases hs
      constructor
      · rintro ⟨o', ho', hc⟩
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
        exact ⟨o, ho, by simpa only [Obj.Covers, Obj.setBytes_addr, Obj.setBytes_size] using hc⟩
      · rintro ⟨o, ho, hc⟩
        exact ⟨Obj.setBytes a w v o, List.mem_map_of_mem ho,
          by simpa only [Obj.Covers, Obj.setBytes_addr, Obj.setBytes_size] using hc⟩
    · split at hs <;> cases hs

/-- The byte fallback store does not change the owned bytes. -/
theorem Heap.owned_storeB {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.storeB a w v = .ok h') (b : BitVec 64) : h'.Owned b ↔ h.Owned b := by
  unfold Heap.storeB at hs
  split at hs
  · exact Heap.owned_store hs b
  · split at hs
    · cases hs
      constructor
      · rintro ⟨o', ho', hw, hc⟩
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
        rw [Obj.setBytes_writable] at hw
        simp only [Obj.Covers, Obj.setBytes_addr, Obj.setBytes_size] at hc
        exact ⟨o, ho, hw, hc⟩
      · rintro ⟨o, ho, hw, hc⟩
        refine ⟨Obj.setBytes a w v o, List.mem_map_of_mem ho, ?_, ?_⟩
        · rw [Obj.setBytes_writable]; exact hw
        · simp only [Obj.Covers, Obj.setBytes_addr, Obj.setBytes_size]; exact hc
    · split at hs <;> cases hs

/-- A byte fallback store writes the memory; the memory holds the new heap; each byte that is not
owned is the same. -/
theorem Heap.storeB_frame {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hp : h.Permits policy)
    (hs : h.storeB a w v = .ok h') :
    ∃ m', writeRam policy m a w v = .ok m' ∧ h'.Holds policy m' ∧
      ∀ b, ¬ h.Owned b → m'.get? b = m.get? b := by
  obtain ⟨m', hw, hh', O, hO, hOw, hb⟩ := Heap.storeB_sound hh hp hs
  exact ⟨m', hw, hh', fun b hn => hb b fun hc => hn ⟨O, hO, hOw, hc⟩⟩

/-- A byte fallback store that succeeds writes bytes that are owned. -/
theorem owned_of_storeB {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.storeB a w v = .ok h') :
    ∀ i, i < w.bytes → h.Owned (a + BitVec.ofNat 64 i) := by
  unfold Heap.storeB at hs
  split at hs
  · exact owned_of_store hh hs
  · split at hs
    · rename_i hc
      obtain ⟨o, ho, hoc⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hoc
      obtain ⟨hw, h1, h2⟩ := hoc
      intro i hi
      have hn := hh.noWrap o ho
      refine ⟨o, ho, hw, ?_⟩
      unfold Obj.Covers
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    · split at hs <;> cases hs

end Lift.Sem
