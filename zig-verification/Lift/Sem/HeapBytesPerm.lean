module

public import Lift.Sem.CallFrame
public import Lift.Sem.HeapBytesSound
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

open Lift.P2.Total
namespace Lift.Sem

-- Byte reads use one memory witness; byte-range permissions are not required.
theorem Heap.loadBytes_value {policy : CpuPolicy} {m : DataMem} {h : Heap}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) {a : BitVec 64}
    {w : Width} {v : w.type} (hl : o.loadBytes a w = some v) :
    (m.loadInt a w.bytes).map (BitVec.ofInt w.bits) = some v := by
  obtain ⟨k, ha, hk, rfl⟩ := Obj.loadBytes_spec hl
  have hc := ByteLemmas.Contains.slice (hh.contains ho) k w.bytes
  rw [← ha] at hc
  have hlen : ((o.bytes.drop k).take w.bytes).length = w.bytes := by
    simp only [List.length_take, List.length_drop, Obj.bytes_length]; omega
  have hm := hc.loadInt_eq hlen
  rw [hm]
  rfl

theorem Heap.loadB_perm_of_holds {policy : CpuPolicy} {m : DataMem} {h h' : Heap}
    (hh : h.Holds policy m) (hp : h.Perm h') (a : BitVec 64) (w : Width) :
    h.loadB a w = h'.loadB a w := by
  have hh' := (Heap.Holds_perm hp).mp hh
  have ht := Heap.load_perm_of_holds hh hp a w
  unfold Heap.loadB
  rw [ht]
  cases ht' : h'.load a w with
  | ok v => rfl
  | stuck why | noFuel =>
    have hn : h.findSome? (fun o => o.loadBytes a w) = none ↔
        h'.findSome? (fun o => o.loadBytes a w) = none := by
      simp only [List.findSome?_eq_none_iff]
      exact ⟨fun hn o ho => hn o (hp.symm.subset ho),
        fun hn o ho => hn o (hp.subset ho)⟩
    cases hf : h.findSome? (fun o => o.loadBytes a w) with
    | none => simp only [hn.mp hf]
    | some v =>
      cases hf' : h'.findSome? (fun o => o.loadBytes a w) with
      | none => have := hn.mpr hf'; rw [hf] at this; cases this
      | some v' =>
        obtain ⟨o, ho, hl⟩ := List.exists_of_findSome?_eq_some hf
        obtain ⟨o', ho', hl'⟩ := List.exists_of_findSome?_eq_some hf'
        have hv := (Heap.loadBytes_value hh ho hl).symm.trans
          (Heap.loadBytes_value hh' ho' hl')
        have eq : v = v' := by
          have := Option.some.inj hv
          exact this
        cases eq
        rfl

-- Each successful store applies one object transformation to the whole heap.
theorem Heap.storeB_map {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.storeB a w v = .ok h') :
    ∃ f : Obj → Obj, h' = h.map f ∧
      ∀ (k : Heap), k.Perm h → k.storeB a w v = .ok (k.map f) := by
  unfold Heap.storeB at hs
  split at hs
  · rename_i ht
    unfold Heap.store at hs
    split at hs
    · rename_i hw
      cases hs
      refine ⟨Obj.set a w v, rfl, ?_⟩
      intro k hp
      have ht' := hp.any_eq (f := fun o => (o.get a w).isSome)
      have hw' := hp.any_eq (f := fun o => o.writable && (o.get a w).isSome)
      simp only [Heap.storeB, ht', ht, ↓reduceIte, Heap.store, hw', hw]
    · cases hs
  · rename_i ht
    split at hs
    · rename_i hb
      cases hs
      refine ⟨Obj.setBytes a w v, rfl, ?_⟩
      intro k hp
      have ht' := hp.any_eq (f := fun o => (o.get a w).isSome)
      have hb' := hp.any_eq (f := fun o => o.writable && decide (o.Spans a w))
      simp only [Heap.storeB, ht', ht, ↓reduceIte, hb', hb, Bool.false_eq_true]
    · split at hs <;> cases hs

theorem Heap.storeB_samePerm {h h' : Heap} (hp : h.Perm h') {a : BitVec 64}
    {w : Width} {v : w.type} {k : Heap} (hs : h.storeB a w v = .ok k) :
    ∃ k', h'.storeB a w v = .ok k' ∧ CallFrame.SamePerm h k h' k' := by
  obtain ⟨f, rfl, hf⟩ := Heap.storeB_map hs
  refine ⟨h'.map f, hf _ hp.symm, ?_⟩
  refine ⟨by simp, by simp, ?_⟩
  have zip_eq : ∀ (l : Heap), l.zip (l.map f) = l.map (fun o => (o, f o)) := by
    intro l
    induction l with
    | nil => rfl
    | cons o l ih => simp only [List.map_cons, List.zip_cons_cons, ih]
  simpa only [zip_eq] using hp.map (fun o => (o, f o))

theorem Heap.storeB_perm {h h' : Heap} (hp : h.Perm h') {a : BitVec 64}
    {w : Width} {v : w.type} {k : Heap} (hs : h.storeB a w v = .ok k) :
    ∃ k', h'.storeB a w v = .ok k' ∧ k.Perm k' := by
  obtain ⟨k', hs', hpair⟩ := Heap.storeB_samePerm hp hs
  exact ⟨k', hs', hpair.perm_out⟩

end Lift.Sem
