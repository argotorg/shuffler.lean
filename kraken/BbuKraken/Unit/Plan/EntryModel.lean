import BbuKraken.Unit.Plan.PlannerRunDefs
import BbuKraken.Unit.SpillSetLemmas

/-! The checks made by the public `plan` entry. -/

namespace Bbu.Unit.EntryU
open Bbu.Sep

theorem checked_spill_id {idCount : Word} {x : StackSlot} {i : Nat}
    (hok : Flat.idOk idCount x = true) (hid : spillId x = some i) :
    i < Flat.ids idCount := by
  unfold spillId at hid
  split at hid
  · rename_i hv
    cases hid
    apply SpillSetProof.lt_ids hok
    simp [Flat.isVariable, isLiteralValue, hv.1, hv.2]
  · cases hid

theorem checked_spill_ids (idCount : Word) (words : List Word)
    (hok : (words.map StackSlot.ofWord).all (Flat.idOk idCount) = true) :
    ∀ i ∈ splIds words, i < Flat.ids idCount := by
  intro i hi
  unfold splIds at hi
  rw [List.mem_eraseDups, List.mem_filterMap] at hi
  obtain ⟨w, hw, hi⟩ := hi
  apply checked_spill_id (List.all_eq_true.mp hok _ (List.mem_map.mpr ⟨w, hw, rfl⟩)) hi

section
variable (m n : Word) (source target : Vector StackSlot MAX_N)
    (spilled : BitVec 32 → BitVec 8) (idCount : Word) (allowed strategy : BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) (data : Vector StackSlot MAX_N)
    (sources : Vector Word MAX_N) (us : Nat → Flat.RunU)

theorem reject_bounds
    (h : m > BitVec.ofNat 64 MAX_N ∨ n > BitVec.ofNat 64 MAX_N ∨
      allowed > 1 ∨ strategy > 1) :
    Flat.planEntry m n source target spilled idCount allowed strategy dropped data sources us =
      (-2, none) := by
  rw [Flat.planEntry, ite_eq_left h]

theorem reject_source
    (hg : ¬(m > BitVec.ofNat 64 MAX_N ∨ n > BitVec.ofNat 64 MAX_N ∨
      allowed > 1 ∨ strategy > 1))
    (h : ((Flat.offsets m).all fun i => Flat.idOk idCount (Flat.get source i)) = false) :
    Flat.planEntry m n source target spilled idCount allowed strategy dropped data sources us =
      (-2, none) := by
  rw [Flat.planEntry, ite_eq_right hg, h]
  rfl

theorem reject_target
    (hg : ¬(m > BitVec.ofNat 64 MAX_N ∨ n > BitVec.ofNat 64 MAX_N ∨
      allowed > 1 ∨ strategy > 1))
    (hs : ((Flat.offsets m).all fun i => Flat.idOk idCount (Flat.get source i)) = true)
    (ht : ((Flat.offsets n).all fun i => Flat.idOk idCount (Flat.get target i)) = false) :
    Flat.planEntry m n source target spilled idCount allowed strategy dropped data sources us =
      (-2, none) := by
  rw [Flat.planEntry, ite_eq_right hg, hs]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ht, Bool.not_false]

end
end Bbu.Unit.EntryU
