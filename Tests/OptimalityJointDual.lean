import Shuffler.Optimality.BirthPlacement.Dual.Theorems

namespace Tests.OptimalityJointDual

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

private def a : Value := .Lit 10
private def b : Value := .Lit 11
private def target : Stack := [a, b, a]

-- This tests the finite quota theorem. The cut is supplied data; the
-- target-gap construction and its birth-cost bridge are separate facts.
private def gaps : Fin 1 → Gap := fun _ => ⟨a, 1, 1, 66⟩
private def certificate : Certificate target.length 1 where
  scale := 1
  row := ![2, 1, 0]
  column := ![1, 0, 1]
  quotaWeight := fun _ => 2
  capWeight := fun _ => 64

example : certificate.Valid (target := target) gaps 1 := by decide
example : certificate.lowerNumerator gaps 102 1 = 140 := by decide
example : ¬({ certificate with scale := 0 }).Valid (target := target) gaps 1 := by decide
example : ¬({ certificate with capWeight := fun _ => 63 }).Valid
    (target := target) gaps 1 := by decide
example : ¬({ certificate with row := ![1, 1, 0] }).Valid
    (target := target) gaps 1 := by unfold Certificate.Valid Certificate.ValidOn; decide

private def assignment : Equiv.Perm (Fin target.length) :=
  Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩
private def reuse : Fin 1 → Nat := fun _ => 1

example : certificate.lowerNumerator gaps 102 1 ≤
    certificate.scale * (2 * 69 + 1 * assignment.support.card : Nat) :=
  certificate.lower_le (target := target) (gaps := gaps) (swap := 1)
    (direct := 102) (generation := 69) (by decide) assignment (by decide) reuse (by decide)
    (by decide) (by decide)

-- The identity assignment cannot satisfy the selected reuse quota.
example : ¬(∀ gap, (gaps gap).required + reuse gap ≤ prefixCount target (gaps gap) 1) := by decide

private def scaled : Certificate target.length 1 where
  scale := 3
  row := ![7, 4, 1]
  column := ![2, -1, 2]
  quotaWeight := fun _ => 6
  capWeight := fun _ => 192

example : scaled.Valid (target := target) gaps 1 := by decide
example : scaled.lowerNumerator gaps 102 1 = 420 := by decide

end Tests.OptimalityJointDual
