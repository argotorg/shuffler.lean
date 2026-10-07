import Shuffler.Optimality.BirthPlacement.RawWord.Counts
import Shuffler.Optimality.BirthPlacement.Plan

namespace Shuffler.Optimality.BirthPlacement.RawWord

-- Every clause uses only the proposed birth word, target, and spill set.
-- The prefix clause states which copies must exist before they leave reach.
def Feasible (spills : SpillSet) (target births : Stack) : Prop :=
  (births : Multiset Value) = (target : Multiset Value) ∧
  (∀ height : Fin (births.length + 1),
    (target.take (height.val - 16) : Multiset Value) ≤ (births.take height.val : Multiset Value)) ∧
  (∀ index : Fin births.length,
    Shuffler.Placement.Free spills births[index] ∨
      (target.take (index.val - 16)).count births[index] <
        (births.take index.val).count births[index])

instance (spills : SpillSet) (target births : Stack) : Decidable (Feasible spills target births) := by
  unfold Feasible
  infer_instance

def values (word : Stack) (size : Nat) (hlen : word.length = size) : Fin size → Value :=
  fun index => word[index.val]'(by omega)

theorem values_positions (word : Stack) (size : Nat) (hlen : word.length = size) (value : Value) :
    Word.positions (values word size hlen) value = positions word value := by
  subst size
  rfl

theorem Feasible.length (h : Feasible spills target births) : births.length = target.length :=
  (Multiset.coe_eq_coe.mp h.1).length_eq

theorem Feasible.balanced (h : Feasible spills target births) :
    Word.Balanced (values births target.length h.length) (fun index => target[index]) := by
  intro value
  rw [values_positions]
  change (positions births value).card = (positions target value).card
  rw [positions_card, positions_card]
  exact List.perm_iff_count.mp (Multiset.coe_eq_coe.mp h.1) value

theorem Feasible.hall (h : Feasible spills target births) :
    Word.Feasible 16 (values births target.length h.length) (fun index => target[index]) := by
  intro value cut
  rw [values_positions]
  change (Hall.due 16 (positions target value) cut).card ≤
    (Hall.born (positions births value) cut).card
  rw [due_card, born_card]
  by_cases hc : cut + 1 ≤ births.length
  · simpa only [Multiset.coe_count] using
      Multiset.le_iff_count.mp (h.2.1 ⟨cut + 1, by omega⟩) value
  · rw [List.take_of_length_le (by omega : births.length ≤ cut + 1)]
    have he := List.perm_iff_count.mp (Multiset.coe_eq_coe.mp h.1) value
    have ht := (List.take_sublist (cut + 1 - 16) target).count_le value
    omega

def Feasible.assignment (h : Feasible spills target births) : Equiv.Perm (Fin target.length) :=
  Word.optimal 16 (values births target.length h.length) (fun index => target[index]) h.balanced

theorem Feasible.assignment_value (h : Feasible spills target births) (index : Fin target.length) :
    target[h.assignment index] = values births target.length h.length index :=
  (Word.optimal_compatible h.balanced index).symm

theorem Feasible.assignment_birthWord (h : Feasible spills target births) :
    birthWord target h.assignment = births := by
  unfold birthWord
  have he : (fun index => target[h.assignment index]) = values births target.length h.length :=
    funext h.assignment_value
  rw [he]
  generalize h.length = hlen
  generalize target.length = size at hlen ⊢
  subst size
  exact List.ofFn_getElem

-- The parser selects an available kind. Cost selection remains a separate step.
def Feasible.plan (h : Feasible spills target births) : Plan spills target where
  assignment := h.assignment
  method := fun index => if Shuffler.Placement.Free spills (values births target.length h.length index)
    then .direct else .dup
  deadlines := Word.optimal_deadline h.balanced h.hall
  available index := by
    rw [h.assignment_birthWord, h.assignment_value]
    have ha := h.2.2 ⟨index.val, by rw [h.length]; exact index.isLt⟩
    split_ifs with hf
    · exact hf
    · exact ha.resolve_left hf

structure Parsed (spills : SpillSet) (target births : Stack) where
  plan : Plan spills target
  word : birthWord target plan.assignment = births

def parse (spills : SpillSet) (target births : Stack) : Option (Parsed spills target births) :=
  if h : Feasible spills target births then some ⟨h.plan, h.assignment_birthWord⟩ else none

end Shuffler.Optimality.BirthPlacement.RawWord
