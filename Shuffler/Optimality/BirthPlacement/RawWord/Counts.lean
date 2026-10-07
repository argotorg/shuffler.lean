import Shuffler.Optimality.BirthPlacement.Word.Theorems
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Count

namespace Shuffler.Optimality.BirthPlacement.RawWord

variable {α : Type*} [DecidableEq α]

theorem count_ofFn (word : Fin size → α) (value : α) :
    (List.ofFn word).count value = (Finset.univ.filter fun index => word index = value).card := by
  rw [Finset.card_filter]
  induction size with
  | zero => simp
  | succ size ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
    rw [ih]
    simp only [beq_iff_eq]
    omega

def positions (word : List α) (value : α) : Finset Nat :=
  Word.positions (fun index : Fin word.length => word[index]) value

theorem positions_card (word : List α) (value : α) :
    (positions word value).card = word.count value := by
  rw [positions, Word.positions, Finset.card_image_of_injective _ Fin.val_injective]
  rw [← count_ofFn]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

theorem mem_positions (word : List α) (value : α) (position : Nat) :
    position ∈ positions word value ↔ ∃ hp : position < word.length, word[position] = value :=
  Word.mem_positions _ _ _

theorem positions_ofFn (word : Fin size → α) (value : α) :
    positions (List.ofFn word) value = Word.positions word value := by
  ext position
  simp only [mem_positions, Word.mem_positions, List.length_ofFn, List.getElem_ofFn]

theorem positions_take (word : List α) (height : Nat) (value : α) :
    positions (word.take height) value = (positions word value).filter (· < height) := by
  ext position
  simp only [mem_positions, Finset.mem_filter, List.length_take]
  constructor
  · rintro ⟨hp, he⟩
    have hw := (Nat.lt_min.mp hp).2
    exact ⟨⟨hw, by simpa only [List.getElem_take] using he⟩, (Nat.lt_min.mp hp).1⟩
  · rintro ⟨⟨hp, he⟩, hh⟩
    exact ⟨Nat.lt_min.mpr ⟨hh, hp⟩, by simpa only [List.getElem_take] using he⟩

theorem born_card (word : List α) (cut : Nat) (value : α) :
    (Hall.born (positions word value) cut).card = (word.take (cut + 1)).count value := by
  rw [← positions_card, positions_take]
  congr 1
  ext position
  simp only [Hall.born, Finset.mem_filter]
  constructor <;> rintro ⟨hm, hi⟩ <;> exact ⟨hm, by omega⟩

theorem due_card (word : List α) (reach cut : Nat) (value : α) :
    (Hall.due reach (positions word value) cut).card =
      (word.take (cut + 1 - reach)).count value := by
  rw [← positions_card, positions_take]
  congr 1
  ext position
  simp only [Hall.due, Finset.mem_filter]
  constructor <;> rintro ⟨hm, hi⟩ <;> exact ⟨hm, by omega⟩

end Shuffler.Optimality.BirthPlacement.RawWord
