import Shuffler.Optimality.BirthPlacement.Global.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGlobalCertificate

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 10
private def b : Value := .Lit 11
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push ⟨31, by decide⟩)

private def direct : Plan ∅ [a, b] where
  assignment := 1
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private def reversed : Plan ∅ [a, b] where
  assignment := Equiv.swap 0 1
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private theorem directMinimum : direct.GloballyMinimal costs .gasOnly :=
  direct.globallyMinimal_of_baseline costs .gasOnly (by decide)

#guard direct.jointObjective costs .gasOnly = 12
#guard reversed.jointObjective costs .gasOnly = 18
#guard birthWord [a, b] direct.assignment ≠ birthWord [a, b] reversed.assignment
#guard flatten (realize direct).built.trace = [.push a, .push b]
#guard flatten (realize reversed).built.trace = [.push b, .push a, .swap 1]

-- The lower objective from another birth word rejects this certificate.
example : ¬reversed.GloballyMinimal costs .gasOnly := by
  intro h
  have hn : ¬reversed.jointObjective costs .gasOnly ≤ direct.jointObjective costs .gasOnly := by decide
  exact hn (h direct)

example : direct.MinimizesWords costs .gasOnly :=
  (direct.globallyMinimal_iff_minimizesWords costs .gasOnly).mp directMinimum

-- The comparison ranges over all words; these particular words are unequal.
example : (traceCost costs (realize direct).built.trace).score .gasOnly -
      baseline costs .gasOnly ∅ [] ([a, b] : Multiset Value) ≤
    2 * ((traceCost costs (realize reversed).built.trace).score .gasOnly -
      baseline costs .gasOnly ∅ [] ([a, b] : Multiset Value)) :=
  direct.minimum_surplus_le_twice costs .gasOnly directMinimum
    (realize reversed).built.trace (realize reversed).built.noPop

private def empty : Plan ∅ [] where
  assignment := 1
  method := fun _ => .direct
  deadlines := by intro index; exact Fin.elim0 index
  available := by intro index; exact Fin.elim0 index

example : empty.GloballyMinimal costs .bytesOnly :=
  empty.globallyMinimal_of_baseline costs .bytesOnly (by decide)

end Tests.OptimalityGlobalCertificate
