import Shuffler.Optimality.BirthPlacement.Word.Cached
import Shuffler.Permute.Defs

namespace Tests.OptimalityEndpointRank

open Shuffler.Optimality.BirthPlacement
open Shuffler.Permute.Permutation

private def smallTarget : Fin 7 → Nat := fun index => [0, 0, 0, 1, 2, 3, 0][index]
private def smallAlternative : Equiv.Perm (Fin 7) :=
  List.formPerm [0, 5, 2] * Equiv.swap 1 3 * Equiv.swap 4 6
private def smallBirths : Fin 7 → Nat := fun index => smallTarget (smallAlternative index)
private theorem smallBalanced : Word.Balanced smallBirths smallTarget :=
  Word.balanced_of_matching smallAlternative (fun _ => rfl)
private def smallCanonical := Word.cachedOptimal 3 smallBirths smallTarget smallBalanced

#guard List.ofFn smallBirths = [3, 1, 0, 0, 0, 0, 2]
#guard List.ofFn (fun index => (smallCanonical index).val) = [5, 3, 2, 0, 1, 6, 4]
#guard List.ofFn (fun index => (smallAlternative index).val) = [5, 3, 0, 1, 6, 2, 4]
#guard smallCanonical.support.card = 6
#guard smallAlternative.support.card = 7
#guard arbitrarySwapCount smallCanonical = 5
#guard arbitrarySwapCount smallAlternative = 4
#guard ∀ index, index.val ≤ (smallAlternative index).val + 3

-- Active position i is placed at 5*i. Each inserted value is distinct and
-- occurs at the same birth and target position, so its endpoint is forced.
private def target : Fin 31 → Nat := fun index =>
  if index.val % 5 = 0 then smallTarget ⟨index.val / 5, by omega⟩
  else 10 + index.val
private def alternative : Equiv.Perm (Fin 31) :=
  List.formPerm [0, 25, 10] * Equiv.swap 5 15 * Equiv.swap 20 30
private def births : Fin 31 → Nat := fun index => target (alternative index)
private theorem balanced : Word.Balanced births target :=
  Word.balanced_of_matching alternative (fun _ => rfl)
private def canonical := Word.cachedOptimal 16 births target balanced

-- These evaluate the actual cached production endpoint function, not the
-- JavaScript model used to find the example.
#guard (List.ofFn fun index => (canonical index).val).zipIdx |>.all fun pair =>
  if pair.2 % 5 = 0 then pair.1 = 5 * ([5, 3, 2, 0, 1, 6, 4][pair.2 / 5]!)
  else pair.1 = pair.2
#guard canonical.support.card = 6
#guard alternative.support.card = 7
#guard arbitrarySwapCount canonical = 5
#guard arbitrarySwapCount alternative = 4
#guard ∀ index, index.val ≤ (alternative index).val + 16
#guard ∀ index, target (canonical index) = births index

-- Minimum moved count is proved for the production choice. This statement
-- deliberately makes no minimum-SWAP claim.
example (other : Equiv.Perm (Fin 31))
    (hvalues : ∀ index, births index = target (other index))
    (hreach : ∀ index, index.val ≤ (other index).val + 16) :
    canonical.support.card ≤ other.support.card := by
  rw [canonical, Word.cachedOptimal_eq]
  exact Word.support_card_le balanced other hvalues hreach

end Tests.OptimalityEndpointRank
