import Shuffler.Optimality.BirthPlacement.Word.Cached

namespace Tests.OptimalityBirthWord

open Shuffler.Optimality.BirthPlacement

private def births : Fin 4 → Bool := fun index => [true, false, true, false][index]
private def target : Fin 4 → Bool := fun index => [false, false, true, true][index]
private theorem balanced : Word.Balanced births target := by intro value; cases value <;> decide
private def assignment := Word.cachedOptimal 2 births target balanced

-- Both directions run. Position 1 has a correct value but must move.
#guard List.ofFn (fun index => (assignment index).val) = [3, 0, 2, 1]
#guard List.ofFn (fun index => (assignment.symm index).val) = [1, 3, 2, 0]
#guard ∀ index, target (assignment index) = births index
#guard ∀ index, index.val ≤ (assignment index).val + 2
#guard assignment.support.card = 3
#guard (Finset.univ.filter fun index => births index ≠ target index).card = 2

-- An unchanged word has the identity endpoint map, including reach zero.
private theorem sameBalanced : Word.Balanced births births := fun _ => rfl
#guard Word.optimal 0 births births sameBalanced = Equiv.refl _

-- The empty case runs in both directions without a default value or index.
private def emptyWord : Fin 0 → Bool := Fin.elim0
private theorem emptyBalanced : Word.Balanced emptyWord emptyWord := fun _ => rfl
#guard List.ofFn (Word.optimal 2 emptyWord emptyWord emptyBalanced) = []
#guard List.ofFn (Word.optimal 2 emptyWord emptyWord emptyBalanced).symm = []

-- The theorem compares with every compatible assignment within the reach.
example (other : Equiv.Perm (Fin 4))
    (hvalues : ∀ index, births index = target (other index))
    (hreach : ∀ index, index.val ≤ (other index).val + 2) :
    assignment.support.card ≤ other.support.card := by
  rw [assignment, Word.cachedOptimal_eq]
  exact Word.support_card_le balanced other hvalues hreach

-- The pure table also has a total fallback for a key outside its stored set.
#guard Word.Cache.lookup (Word.Cache.entries [1, 2, 1] (fun index : Nat => Fin.last index))
  (fun index => Fin.last index) 1 = Fin.last 1
#guard Word.Cache.lookup (Word.Cache.entries [1, 2, 1] (fun index : Nat => Fin.last index))
  (fun index => Fin.last index) 3 = Fin.last 3

end Tests.OptimalityBirthWord
