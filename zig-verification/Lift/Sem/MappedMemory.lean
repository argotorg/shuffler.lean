module

public import Lift.P2.Total.Memory
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

namespace Lift.Sem.SysV

open Lift.P2.Total

/-- Each mapped word of `m` remains mapped in `m'`. -/
def MappedMemory (m m' : DataMem) : Prop :=
  ∀ a n, Mem.loadInt m a n ≠ none → Mem.loadInt m' a n ≠ none

theorem MappedMemory.refl (m : DataMem) : MappedMemory m m := fun _ _ h => h

theorem MappedMemory.trans {m m' m'' : DataMem} (h : MappedMemory m m') (h' : MappedMemory m' m'') :
    MappedMemory m m'' := fun a n hm => h' a n (h a n hm)

private theorem mapped_allSome {α : Type} :
    ∀ {l : List (Option α)}, (∀ x ∈ l, x.isSome) → l.allSome ≠ none
  | [], _ => by simp [List.allSome]
  | x :: l, h => by
    obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    have := mapped_allSome (l := l) (fun z hz => h z (by simp [hz]))
    simp only [List.allSome, List.mapM_cons, id] at this ⊢
    intro hn
    apply this
    cases hl : l.mapM id with
    | none => rfl
    | some _ => simp [hl] at hn

/-- A store does not remove mapped bytes. -/
theorem MappedMemory.storeInt (m : DataMem) (a : BitVec 64) (w : Nat) (v : Int) :
    MappedMemory m (Mem.storeInt m a w v) := by
  intro b k h
  obtain ⟨xs, hx⟩ := Option.ne_none_iff_exists'.mp h
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hx
  obtain ⟨bs, hb, -⟩ := hx
  have hl := List.allSome_eq_map_some hb
  simp only [Mem.loadInt, Mem.loadBytes, ne_eq, Option.map_eq_none_iff]
  apply mapped_allSome
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hm : (Std.ExtHashMap.get? m (b + BitVec.ofNat 64 i)) ∈ List.map some bs := by
    rw [← hl]; exact List.mem_map_of_mem hi
  obtain ⟨y, -, hy⟩ := List.mem_map.mp hm
  rw [Mem.get?_storeInt]
  have hmem : b + BitVec.ofNat 64 i ∈ m :=
    Std.ExtHashMap.isSome_getElem?_iff_mem.mp (by
      rw [← Std.ExtHashMap.get?_eq_getElem?, ← hy]; rfl)
  simp [hmem]

/-- A successful machine store does not remove mapped bytes. -/
theorem MappedMemory.writeRam {policy : CpuPolicy} {m m' : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    (h : Lift.P2.Total.writeRam policy m a w v = .ok m') : MappedMemory m m' := by
  unfold Lift.P2.Total.writeRam at h
  split at h
  · split at h
    · cases h
      exact MappedMemory.storeInt _ _ _ _
    · cases h
  · cases h

end Lift.Sem.SysV
