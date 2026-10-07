import Shuffler.Optimality.BirthPlacement.Word.Cached
import Shuffler.Permute.Defs

namespace Tests.OptimalityBalancedRank

open Shuffler.Optimality.BirthPlacement
open Shuffler.Permute.Permutation

private def target : Fin 12 → Nat := fun index => [0, 0, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7][index]
private def original : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 10, 8, 6, 4, 2] * List.formPerm [1, 11, 9, 7, 5, 3]
private def firstWitness : Equiv.Perm (Fin 12) := List.formPerm [1, 11, 10, 8, 7, 5, 4, 2]
private def secondWitness : Equiv.Perm (Fin 12) := List.formPerm [0, 9, 7, 6, 4, 3, 1]
private def first : Fin 12 → Nat := fun index => target (firstWitness index)
private def second : Fin 12 → Nat := fun index => target (secondWitness index)
private theorem firstBalanced : Word.Balanced first target :=
  Word.balanced_of_matching firstWitness (fun _ => rfl)
private theorem secondBalanced : Word.Balanced second target :=
  Word.balanced_of_matching secondWitness (fun _ => rfl)
private def firstCanonical := Word.cachedOptimal 2 first target firstBalanced
private def secondCanonical := Word.cachedOptimal 2 second target secondBalanced

private def countThrough (word : Fin 12 → Nat) (value cut : Nat) : Nat :=
  (Finset.univ.filter fun index => index.val ≤ cut ∧ word index = value).card

#guard ∀ index, index.val ≤ (original index).val + 2
#guard original.support.card = 12
#guard ∀ index,
  (first index = target index ∧ second index = target (original index)) ∨
  (second index = target index ∧ first index = target (original index))
#guard ∀ value : Fin 8, ∀ cut : Fin 12,
  countThrough first value.val cut.val ≤ countThrough second value.val cut.val + 1 ∧
    countThrough second value.val cut.val ≤ countThrough first value.val cut.val + 1
#guard firstCanonical = firstWitness
#guard secondCanonical = secondWitness
#guard firstCanonical.support.card = 8
#guard secondCanonical.support.card = 7
#guard arbitrarySwapCount firstCanonical = 7
#guard arbitrarySwapCount secondCanonical = 6
#guard arbitrarySwapCount firstCanonical + arbitrarySwapCount secondCanonical > original.support.card

-- A different balanced coloring does meet the original moved-count budget.
private def goodFirst : Equiv.Perm (Fin 12) := List.formPerm [1, 11, 10, 8, 6, 4, 3]
private def goodSecond : Equiv.Perm (Fin 12) := List.formPerm [0, 9, 7, 5, 4, 2]
#guard ∀ index,
  (target (goodFirst index) = target index ∧ target (goodSecond index) = target (original index)) ∨
  (target (goodSecond index) = target index ∧ target (goodFirst index) = target (original index))
#guard ∀ value : Fin 8, ∀ cut : Fin 12,
  let left := countThrough (fun index => target (goodFirst index)) value.val cut.val
  let right := countThrough (fun index => target (goodSecond index)) value.val cut.val
  left ≤ right + 1 ∧ right ≤ left + 1
#guard ∀ index, index.val ≤ (goodFirst index).val + 2 ∧ index.val ≤ (goodSecond index).val + 2
#guard arbitrarySwapCount goodFirst + arbitrarySwapCount goodSecond = 11

-- Scaling active positions by seven preserves reach 2 at production reach 16.
private def expandedTarget : Fin 78 → Nat := fun index =>
  if index.val % 7 = 0 then target ⟨index.val / 7, by omega⟩
  else 10 + index.val
private def expandedFirstWitness : Equiv.Perm (Fin 78) :=
  List.formPerm [7, 77, 70, 56, 49, 35, 28, 14]
private def expandedSecondWitness : Equiv.Perm (Fin 78) :=
  List.formPerm [0, 63, 49, 42, 28, 21, 7]
private def expandedFirst : Fin 78 → Nat := fun index => expandedTarget (expandedFirstWitness index)
private def expandedSecond : Fin 78 → Nat := fun index => expandedTarget (expandedSecondWitness index)
private theorem expandedFirstBalanced : Word.Balanced expandedFirst expandedTarget :=
  Word.balanced_of_matching expandedFirstWitness (fun _ => rfl)
private theorem expandedSecondBalanced : Word.Balanced expandedSecond expandedTarget :=
  Word.balanced_of_matching expandedSecondWitness (fun _ => rfl)
private def expandedFirstCanonical :=
  Word.cachedOptimal 16 expandedFirst expandedTarget expandedFirstBalanced
private def expandedSecondCanonical :=
  Word.cachedOptimal 16 expandedSecond expandedTarget expandedSecondBalanced

#guard expandedFirstCanonical = expandedFirstWitness
#guard expandedSecondCanonical = expandedSecondWitness
#guard arbitrarySwapCount expandedFirstCanonical = 7
#guard arbitrarySwapCount expandedSecondCanonical = 6
#guard ∀ index, index.val ≤ (expandedFirstCanonical index).val + 16 ∧
  index.val ≤ (expandedSecondCanonical index).val + 16

end Tests.OptimalityBalancedRank
