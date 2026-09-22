import Shuffler.Mapping
import Mathlib.Data.Fintype.Perm

namespace Mapping.Tests

open Shuffler.Permute (Permutation apply_permutation permute)

private def roundTrip (source : Stack) (perm : Permutation source) : Permutation source :=
  Mapping.toPermutation perm.toPEquiv (Nat.le_refl _) (fun _ => rfl)

-- Conversion preserves every destination, including for the empty stack.
example (source : Stack) (perm : Permutation source) : roundTrip source perm = perm := by
  ext i
  rfl

#guard apply_permutation [] (roundTrip [] 1) = []
#guard apply_permutation [7] (roundTrip [7] 1) = [7]
#guard apply_permutation [7, 7] (roundTrip [7, 7] (Equiv.swap 0 1)) = [7, 7]

-- A three-cycle distinguishes source-to-target from target-to-source order.
private def mapping : Mapping [10, 20, 30] [30, 10, 20] :=
  (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2).toPEquiv

private def finalPermutation : Permutation [10, 20, 30] :=
  mapping.toPermutation (by decide) (fun _ => rfl)

#guard (List.finRange 3).map (fun i => (finalPermutation i).val) = [1, 2, 0]
#guard apply_permutation [10, 20, 30] finalPermutation = [30, 10, 20]
#guard (match permute [10, 20, 30] finalPermutation with
  | .ok ⟨result, _⟩ => result = [30, 10, 20]
  | .error _ => False)

-- Equal lengths alone do not make a partial mapping total.
#guard ¬∀ i, ((⊥ : Mapping [10] [10]) i).isSome

-- Every target can be assigned while a surplus source position remains.
private def surplus : Mapping [10, 20] [10] := PEquiv.single 0 0

#guard ∀ j, (surplus.symm j).isSome
#guard ¬∀ i, (surplus i).isSome

-- Check every permutation of five positions using the executable conversion.
#guard decide (∀ perm : Permutation [0, 1, 2, 3, 4],
  roundTrip [0, 1, 2, 3, 4] perm = perm)

end Mapping.Tests
