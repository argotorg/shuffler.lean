import Shuffler.Optimality.BirthPlacement.FixedWord.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourceEntry

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def c : Value := .Var ⟨44⟩
private def source : Stack := [a, b, c]
private def births : Stack := [b, c]
private def target : Stack := [b, c, c, a, b]
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push0)

private def candidate : List Op := [.swap 1, .swap 2, .swap 1, .dup 3, .dup 2, .swap 3, .swap 1]
private def comparison : List Op := [.dup 2, .swap 3, .dup 2, .swap 3]

private def facts (ops : List Op) : Option (Stack × Stack × Nat × Nat × Nat) := do
  let result ← replay ∅ source ops
  let trace := result.built.trace
  return (result.target, SwapRuns.births trace, trace.swapCount,
    (traceCost costs trace).gas, (traceCost costs trace).bytes)

-- Both instruction lists use the production Trace constructors at reach16.
#guard facts candidate = some (target, births, 5, 21, 7)
#guard facts comparison = some (target, births, 2, 12, 4)
#guard baseline costs .gasOnly ∅ source (births : Multiset Value) = 6
#guard baseline costs .bytesOnly ∅ source (births : Multiset Value) = 2
#guard 21 - 6 > 2 * (12 - 6)
#guard 7 - 2 > 2 * (4 - 2)

-- Every equal-copy assignment moves at least these four positions.
private theorem four_moved (assignment : Equiv.Perm (Fin target.length))
    (hword : birthWord target assignment = source ++ births) : 4 ≤ assignment.support.card := by
  let required : Finset (Fin target.length) :=
    {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩}
  have hs : required ⊆ assignment.support := by
    intro index hi
    simp only [required, Finset.mem_insert, Finset.mem_singleton] at hi
    apply Equiv.Perm.mem_support.mpr
    intro he
    have hv := congrArg (fun values : Stack => values[index.val]?) hword
    simp only [birthWord, List.getElem?_ofFn, dite_eq_left index.isLt, he] at hv
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp [source, target, births, a, b, c] at hv
  have hc := Finset.card_le_card hs
  have hr : required.card = 4 := by decide
  omega

-- The two-SWAP comparison attains the lower bound for this fixed word.
theorem two_le_swapCount (trace : Trace ∅ source target) (hpop : trace.noPop)
    (hword : SwapRuns.births trace = births) : 2 ≤ trace.swapCount := by
  have hw := traceAssignment_birthWord trace hpop
  rw [hword] at hw
  have hlo := four_moved (traceAssignment trace hpop) hw
  have hhi := traceAssignment_moved_le trace hpop
  omega

end Tests.OptimalitySourceEntry
