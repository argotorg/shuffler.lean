import Shuffler.Permute.Theorems

namespace PermuteTests

open Shuffler.Permute

-- The arbitrary-swap minimum exists even when there are no positions.
example : Permutation.arbitrarySwapCount (1 : Equiv.Perm (Fin 0)) = 0 := by simp
example : ∃ swaps : List (Fin 0 × Fin 0),
    (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = 1 ∧ swaps.length = 0 := by
  have h := Permutation.exists_swaps (1 : Equiv.Perm (Fin 0))
  simp only [Permutation.arbitrarySwapCount_one] at h
  exact h

-- Identity and repeated endpoints do not require a nonempty support.
example : Permutation.swapCount (1 : Equiv.Perm (Fin 1)) 0 = 0 := by simp
example : Permutation.swapCount (1 : Equiv.Perm (Fin 1)) 0 ≤ [0, 0].length := by
  apply Permutation.swapCount_le_length_top_swaps _ _ [0, 0]
  decide

-- A swap involving the top attains both minima in one step.
example : Permutation.swapCount (Equiv.swap (0 : Fin 3) 2) 2 = 1 := by decide
example : Permutation.arbitrarySwapCount (Equiv.swap (0 : Fin 3) 2) = 1 := by decide

-- A swap below a fixed top attains the factor-three bound.
private def belowTop : Equiv.Perm (Fin 3) := Equiv.swap 0 1

example : Permutation.swapCount belowTop 2 = 3 ∧
    Permutation.arbitrarySwapCount belowTop = 1 := by decide

example : Permutation.swapCount belowTop 2 =
    3 * Permutation.arbitrarySwapCount belowTop := by decide

-- No top-swap sequence of length at most two implements this permutation.
example (swaps : List (Fin 3)) (hlen : swaps.length ≤ 2) :
    (swaps.map (Equiv.swap 2)).prod ≠ belowTop := by
  intro hprod
  have h := Permutation.swapCount_le_length_top_swaps belowTop 2 swaps hprod
  have hc : Permutation.swapCount belowTop 2 = 3 := by decide
  omega

-- No empty arbitrary-swap sequence implements a nonidentity permutation.
example (swaps : List (Fin 3 × Fin 3)) (hlen : swaps.length = 0) :
    (swaps.map (fun p => Equiv.swap p.1 p.2)).prod ≠ belowTop := by
  intro hprod
  have h := Permutation.arbitrarySwapCount_le_length_swaps belowTop swaps hprod
  have hc : Permutation.arbitrarySwapCount belowTop = 1 := by decide
  omega

-- A cycle containing the top and a separate cycle contribute separately.
example : Permutation.swapCount
    (Equiv.swap (0 : Fin 5) 4 * Equiv.swap 1 2) 4 = 4 := by decide
example : Permutation.arbitrarySwapCount
    (Equiv.swap (0 : Fin 5) 4 * Equiv.swap 1 2) = 2 := by decide

-- A cycle with three positions below a fixed top costs four top swaps or two arbitrary swaps.
example : Permutation.swapCount
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) 3 = 4 := by decide
example : Permutation.arbitrarySwapCount
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 2 := by decide

private def source : Stack := [.Var ⟨0⟩, .Var ⟨1⟩, .Var ⟨2⟩]

private def runSummary (source : Stack) (perm : Permutation source) : Option (Stack × ℕ) :=
  match permute ∅ source perm with
  | .ok ⟨res, trace⟩ => some (res, trace.swapCount)
  | .error _ => none

-- Evaluate the production algorithm, including the result and its emitted count.
example : runSummary source belowTop =
    some ([.Var ⟨1⟩, .Var ⟨0⟩, .Var ⟨2⟩], 3) := by native_decide

example {res : Stack} {trace : Trace ∅ source res}
    (hresult : permute ∅ source belowTop = .ok ⟨res, trace⟩) :
    IsLeast {n | ∃ swaps : List (Fin 3),
      (swaps.map (Equiv.swap 2)).prod = belowTop ∧ swaps.length = n} trace.swapCount :=
  permute_swapCount_optimal ∅ source belowTop (by decide) hresult

example {res : Stack} {trace : Trace ∅ source res}
    (hresult : permute ∅ source belowTop = .ok ⟨res, trace⟩) :
    trace.swapCount ≤ 3 * [(0, 1)].length := by
  apply permute_swapCount_le_three_mul_length_swaps ∅ source belowTop hresult
    ([(0, 1)] : List (Fin 3 × Fin 3))
  exact mul_one belowTop

-- A duplicate value can make the final stack unchanged despite a position permutation.
example : runSummary [.Var ⟨0⟩, .Var ⟨0⟩, .Var ⟨0⟩] belowTop =
    some ([.Var ⟨0⟩, .Var ⟨0⟩, .Var ⟨0⟩], 3) := by native_decide

-- The upper bound also applies to a successful run on the empty stack.
example : (Trace.Lit (spills := ∅) []).swapCount ≤
    3 * Permutation.arbitrarySwapCount (1 : Permutation []) :=
  permute_swapCount_le_three_mul_arbitrarySwapCount ∅ [] 1 rfl

-- A permutation that moves an unreachable position remains blocked.
example : (match permute ∅ (List.replicate 18 (.Var ⟨0⟩))
    (Equiv.swap (0 : Fin 18) (17 : Fin 18)) with
    | .error (.Blocked depth) => depth == 1
    | .ok _ => false) = true := by native_decide

end PermuteTests
