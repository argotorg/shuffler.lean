import Shuffler.Optimality.BirthPlacement.Endpoint.Theorems

namespace Tests.OptimalityBirthHall

open Shuffler.Optimality.BirthPlacement

-- Reservation intervals include the start and exclude the end.
#guard Reservations.Covers 2 3 3
#guard Reservations.Covers 2 3 4
#guard ¬Reservations.Covers 2 3 5
#guard ¬Reservations.Covers 0 3 3
#guard Reservations.select 2 (fun _ => 0) [0, 1, 2] = ∅
#guard Reservations.select 2 (fun _ => 1) [0, 1, 2, 3] = {0, 2}
#guard Reservations.select 2 (fun cut => if cut = 1 then 0 else 1) [0, 1, 2] = {2}
#guard Reservations.select 0 (fun _ => 0) [0, 1, 2] = {0, 1, 2}
#guard Reservations.select 2 (fun _ => 1) [] = ∅

-- Before the reach is attained, output zero is not due.
#guard Hall.due 2 {0, 1} 1 = ∅
#guard Hall.due 2 {0, 1} 2 = {0}
#guard Hall.fixed 2 ∅ ∅ = ∅

-- For word b,a,b,a and target a,a,b,b, a occurs at the same position 1.
-- This copy must move: the other a is born too late for output zero.
#guard Hall.fixed 2 {1, 3} {0, 1} = ∅
#guard Hall.fixed 2 {0, 2} {2, 3} = {2}
#guard Hall.slack 2 {1, 3} {0, 1} 1 = 1
#guard Hall.slack 2 {1, 3} {0, 1} 2 = 0
#guard (Endpoint.optimal 2 {1, 3} {0, 1} (by decide) ⟨1, by decide⟩).val = 0
#guard (Endpoint.optimal 2 {1, 3} {0, 1} (by decide) ⟨3, by decide⟩).val = 1
#guard (Endpoint.optimal 2 {0, 2} {2, 3} (by decide) ⟨0, by decide⟩).val = 3
#guard (Endpoint.optimal 2 {0, 2} {2, 3} (by decide) ⟨2, by decide⟩).val = 2
#guard Endpoint.fixed (Endpoint.optimal 2 {0, 2} {2, 3} (by decide)) = {2}

-- With zero reach, equal endpoint sets can all stay fixed.
#guard Endpoint.fixed (Endpoint.optimal 0 {0, 2} {0, 2} (by decide)) = {0, 2}

-- Check the actual selector against all feasible subsets on a small grid.
private def checkSmall (reach : Nat) (capacity : Nat → Nat) : Bool :=
  let candidates := Finset.range 5
  let chosen := Reservations.select reach capacity (candidates.sort (· ≤ ·))
  (List.range 32).all fun mask =>
    let selected := candidates.filter fun index => mask.testBit index
    if (List.range (5 + reach)).all (fun cut =>
      Reservations.load reach selected cut ≤ capacity cut)
    then selected.card ≤ chosen.card else true

#guard (List.range 4).all fun reach =>
  (List.range 32).all fun bits =>
    checkSmall reach (fun cut => (bits / 2 ^ (cut % 5)) % 2)

example (reach : Nat) (births outputs : Finset Nat) (hcard : births.card = outputs.card) :
    Hall.Condition reach births outputs ↔
      ∀ position : births,
        position.val ≤ (Hall.ordered births outputs hcard position).val + reach :=
  Hall.condition_iff_ordered_deadline hcard

end Tests.OptimalityBirthHall
