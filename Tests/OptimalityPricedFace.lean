import Shuffler.Optimality.BirthPlacement.Dual.Face

namespace Tests.OptimalityPricedFace

open Shuffler.Optimality.BirthPlacement.Dual

private abbrev target : Stack := [.Lit 0, .Lit 0, .Lit 1, .Lit 1, .Lit 1, .Lit 1, .Lit 0, .Lit 0]
private def gaps : Fin 1 → Gap := fun _ => ⟨.Lit 0, 3, 2, 0⟩
private def cert : Certificate target.length 1 where
  scale := 1
  row index := if index.val < 4 then 0 else if index.val < 6 then -1 else -2
  column index := if index.val < 2 then 4 else if index.val < 4 then 1 else if index.val < 6 then 2 else 3
  quotaWeight := fun _ => 3
  capWeight := fun _ => 0
private def onePrefetch : Equiv.Perm (Fin target.length) := List.formPerm [3, 6, 4]

private theorem valid : cert.ValidOn gaps 1 (fun birth output => birth.val ≤ output.val + 2) := by decide
private theorem tight : ∀ birth, cert.EdgeTight gaps 1 birth (onePrefetch birth) := by decide
private theorem legal : ∀ birth, birth.val ≤ (onePrefetch birth).val + 2 := by decide

-- Row4 can keep its identity or use the earlier b column3 at one lower level.
example : cert.column 4 = cert.column 3 + (cert.scale * 1 : Nat) :=
  cert.pin_bridge gaps 4 3 (by decide) (by decide) (by decide) (by decide)
example : (onePrefetch 4).val < 4 ∧ 4 < (onePrefetch⁻¹ 4).val :=
  cert.value_correct_backward gaps valid (by decide) onePrefetch legal tight 4 (by decide) (by decide)

-- The early a column has a higher level than the later a column, so it is pinned.
example (assignment : Equiv.Perm (Fin target.length))
    (hlegal : ∀ birth, birth.val ≤ (assignment birth).val + 2)
    (htight : ∀ birth, cert.EdgeTight gaps 1 birth (assignment birth)) :
    assignment 0 = 0 :=
  cert.column_drop_fixed gaps valid assignment hlegal htight 0 6 (by decide) (by decide) (by decide)

example : cert.column 7 = cert.column 6 ∧ (2 : Fin target.length) ≠ 6 ∧
    (3 : Fin target.length) ≠ 7 ∧ cert.EdgeTight gaps 1 2 6 ∧ cert.EdgeTight gaps 1 3 7 :=
  cert.generic_uncross gaps valid (by decide) 2 3 7 6 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- These hypotheses matter: an identity is not a generic tight edge, and
-- the high-priced source column is not interchangeable with a later one.
example : ¬cert.EdgeTight gaps 1 4 0 := by decide
example : ¬cert.column 0 ≤ cert.column 6 := by decide

#print axioms Certificate.generic_column_min
#print axioms Certificate.pin_bridge
#print axioms Certificate.generic_levels_mono
#print axioms Certificate.column_drop_fixed
#print axioms Certificate.generic_uncross
#print axioms Certificate.value_correct_backward

end Tests.OptimalityPricedFace
