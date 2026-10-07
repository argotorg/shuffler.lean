import Shuffler.Optimality.BirthPlacement.Dual.Pairwise

namespace Tests.OptimalityPairwiseDual

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

private def a : Value := .Var ⟨42⟩
private def b : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def target : Stack := a :: List.replicate 16 b ++ [a]
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)

private def assignment : Equiv.Perm (Fin target.length) :=
  Equiv.swap ⟨16, by decide⟩ ⟨17, by decide⟩

-- The input plan has only direct births. The theorem selects its cheaper
-- legal methods and proves the global result from finite assignment data.
private def plan : Plan spills target where
  assignment := assignment
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private def certificate (swap reward : Nat) : Certificate target.length target.length where
  scale := 1
  row index := if index.val = 17 then -(swap : Int) else 0
  column index := if index.val = 0 then reward + swap else if index.val = 17 then reward else swap
  quotaWeight index := if index.val = 0 then reward else 0
  capWeight := fun _ => 0

private theorem allFree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index] := by
  decide

private theorem bytesMinimum : (plan.cheapest costs .bytesOnly).GloballyMinimal costs .bytesOnly :=
  (certificate 1 66).pairwise_globallyMinimal costs .bytesOnly (by decide) (by decide)
    (by decide) plan allFree (by decide)

example : PairwisePremiums costs .bytesOnly spills target := by decide
example : (plan.cheapest costs .bytesOnly).method ⟨16, by decide⟩ = .dup := by decide
example : (plan.cheapest costs .bytesOnly).jointObjective costs .bytesOnly = 104 := by decide

example : (certificate 1 66).lowerNumerator (targetGap costs .bytesOnly spills target)
    (directTotal costs .bytesOnly spills target) (costs.swap.score .bytesOnly) =
      (plan.cheapest costs .bytesOnly).jointObjective costs .bytesOnly := by
  exact (certificate 1 66).pairwise_attains costs .bytesOnly (by decide) (by decide)
    plan allFree (by decide)

example (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize (plan.cheapest costs .bytesOnly)).built.trace).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value)) :=
  (plan.cheapest costs .bytesOnly).minimum_surplus_le_twice costs .bytesOnly bytesMinimum other hpop

-- Gas-only weights and mixed weights use the same theorem and assignment.
example : (plan.cheapest costs .gasOnly).GloballyMinimal costs .gasOnly :=
  (certificate 3 6).pairwise_globallyMinimal costs .gasOnly (by decide) (by decide)
    (by decide) plan allFree (by decide)

private def mixed : Weights := ⟨2, 3, by decide⟩

example : (plan.cheapest costs mixed).GloballyMinimal costs mixed :=
  (certificate 9 210).pairwise_globallyMinimal costs mixed (by decide) (by decide)
    (by decide) plan allFree (by decide)

example : (plan.cheapest costs mixed).jointObjective costs mixed = 488 := by decide

-- DUP and SWAP prices need not be equal.
private def unequal : PrimitiveCosts where
  swap := ⟨0, 3⟩
  dup := ⟨0, 2⟩
  pop := ⟨0, 0⟩
  push := fun _ => ⟨0, 1⟩
  load := fun _ => ⟨0, 7⟩

example : (plan.cheapest unequal .bytesOnly).GloballyMinimal unequal .bytesOnly :=
  (certificate 3 10).pairwise_globallyMinimal unequal .bytesOnly (by decide) (by decide)
    (by decide) plan allFree (by decide)

-- A third premium copy violates the restricted condition and can give
-- more than one spare copy at an early gap.
example : ¬PairwisePremiums costs .bytesOnly spills [a, a, a] := by decide
example : prefixCount [a, a, a] (targetGap costs .bytesOnly spills [a, a, a] ⟨0, by decide⟩) 1 = 3 := by
  decide
example : (targetGap costs .bytesOnly spills [a, a, a] ⟨0, by decide⟩).required = 1 := by decide

-- The original small-price certificate is not a full-price certificate.
example : ¬(certificate 1 2).FullPrices (targetGap costs .bytesOnly spills target) := by decide
example : ¬(certificate 1 66).TightFor (targetGap costs .bytesOnly spills target)
    (costs.swap.score .bytesOnly) 1 := by decide

private def emptyPlan : Plan spills [] where
  assignment := 1
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private def emptyCertificate : Certificate 0 0 where
  scale := 1
  row := Fin.elim0
  column := Fin.elim0
  quotaWeight := Fin.elim0
  capWeight := Fin.elim0

example : (emptyPlan.cheapest costs mixed).GloballyMinimal costs mixed :=
  Certificate.pairwise_globallyMinimal (target := []) emptyCertificate costs mixed (by decide) (by decide)
    (by decide) emptyPlan (by decide) (by decide)

#print axioms birth_prefix_surplus_le
#print axioms cheapest_generation_discount_eq
#print axioms Certificate.pairwise_attains
#print axioms pairwise_cheapest_surplus_le_twice

end Tests.OptimalityPairwiseDual
