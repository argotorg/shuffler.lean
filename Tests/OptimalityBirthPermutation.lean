import Shuffler.Optimality.BirthPlacement.Permutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Tests.OptimalityBirthPermutation

open Shuffler.Optimality.BirthPlacement

private def target16 (index : Fin 47) : Nat :=
  if index.val = 0 ∨ index.val = 46 then 0 else (index.val - 1) % 15 + 1

private def suffix16 : Finset (Fin 47) := Finset.univ.filter fun index => 32 ≤ index.val

private def valueRank16 (value : Nat) : Nat := if value = 0 then 0 else 16 - value

#guard suffix16.card = 15
#guard target16 ⟨32, by decide⟩ = 2
#guard target16 ⟨45, by decide⟩ = 15
#guard target16 ⟨46, by decide⟩ = 0

-- This checks the permutation certificate for every assignment of equal copies.
-- The separate deadline argument must establish the stated birth suffix.
example (births : Fin 47 → Nat)
    (hsuffix : ∀ index ∈ suffix16, births index = index.val - 31)
    (perm : Equiv.Perm (Fin 47))
    (hcompatible : ∀ index, births index = target16 (perm index)) :
    15 ≤ Shuffler.Permute.Permutation.arbitrarySwapCount perm := by
  have hdecrease : ∀ index ∈ suffix16,
      valueRank16 (target16 index) < valueRank16 (births index) := by
    intro index hi
    rw [hsuffix index hi]
    fin_cases index <;> simp_all [suffix16, target16, valueRank16]
  exact (by decide : 15 = suffix16.card) ▸
    value_rank_card_le_arbitrarySwapCount births target16 perm hcompatible
      suffix16 valueRank16 hdecrease

-- Canonical occurrence matching need not minimize the number of swaps.
-- These words differ by one swap, although canonical matching gives a 4-cycle.
private def repeatedSource (index : Fin 4) : Nat := [0, 0, 1, 1][index]
private def repeatedTarget (index : Fin 4) : Nat := [1, 0, 1, 0][index]
private def oneSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 3

#guard ∀ index, repeatedSource index = repeatedTarget (oneSwap index)
#guard Shuffler.Permute.Permutation.arbitrarySwapCount oneSwap = 1

-- Strict rank decrease is required. A correct position gives no such evidence.
#guard ¬valueRank16 2 < valueRank16 2
#guard ¬valueRank16 1 < valueRank16 2

end Tests.OptimalityBirthPermutation
