import Shuffler.Optimality.Collective.DeadlineCounts

namespace Tests.OptimalityDeadlines

open Shuffler.Optimality.Collective

private def a : Value := .Lit 1
private def b : Value := .Lit 2
private def source : Stack := [a, a, b]
private def target : Stack := [a, b, a, a, b]
private def paid : Finset (Interval target) := Finset.univ.filter (Interval.Paid source)

-- Source copies pay for the first two a outputs and the first b output.
#guard (newPositions source target).card = 2
#guard (newPositions source target).image Fin.val = {3, 4}
#guard (newBefore source target 3).card = 0
#guard (newBefore source target 4).card = 1
#guard (newBefore source target 5).card = 2
#guard (newBefore source target 10).card = 2

-- Both jobs move before their own output positions to preserve a copy.
#guard deadlineOrigin paid ⟨3, by decide⟩ = 2
#guard deadlineOrigin paid ⟨4, by decide⟩ = 1
#guard birthDeadline 3 source.length paid ⟨3, by decide⟩ = 3
#guard birthDeadline 3 source.length paid ⟨4, by decide⟩ = 2
#guard (dueBefore source target paid 2).card = 1
#guard (dueBefore source target paid 3).card = 2
#guard (dueBefore source target paid 4).card = 2

example : (dueBefore source target paid 3).card + source.length =
    3 + (mandatory source target 3).card +
      (paid.filter fun gap => gap.Crosses 3).card := by
  apply dueBefore_card_balance source target paid _ 3 (by decide)
  intro gap hg
  exact (Finset.mem_filter.mp hg).2

example : ((dueBefore source target paid 3).card : Int) ≤
      (3 : Int) + 3 - source.length ↔
    (mandatory source target 3).card +
      (paid.filter fun gap => gap.Crosses 3).card ≤ 3 := by
  apply deadline_capacity_iff source target paid _ 3 3 (by decide)
  intro gap hg
  exact (Finset.mem_filter.mp hg).2

-- A fresh first output at source size reach+1 has deadline zero.
private def fullSource : Stack := List.replicate 17 a
private def blockedTarget : Stack := b :: fullSource

#guard birthDeadline 16 fullSource.length (∅ : Finset (Interval blockedTarget))
  ⟨0, by decide⟩ = 0
#guard (dueBefore fullSource blockedTarget ∅ 1).card = 1
#guard ¬((dueBefore fullSource blockedTarget ∅ 1).card : Int) ≤
  (1 : Int) + 16 - fullSource.length
#guard ¬(mandatory fullSource blockedTarget 1).card ≤ 16

-- A first old output releases one slot and passes that same boundary.
private def allowedTarget : Stack := fullSource ++ [b]

#guard birthDeadline 16 fullSource.length (∅ : Finset (Interval allowedTarget))
  ⟨17, by decide⟩ = 17
#guard (dueBefore fullSource allowedTarget ∅ 1).card = 0
#guard ((dueBefore fullSource allowedTarget ∅ 1).card : Int) ≤
  (1 : Int) + 16 - fullSource.length
#guard (mandatory fullSource allowedTarget 1).card = 16

-- An unpaid interval ends at an old copy and is not a birth job.
private def oldPair : Stack := [a, a]
#guard (newPositions oldPair oldPair).card = 0
#guard (dueBefore oldPair oldPair Finset.univ 1).card = 0
#guard ((Finset.univ : Finset (Interval oldPair)).filter fun gap => gap.Crosses 1).card = 1

#guard (newPositions [] []).card = 0
#guard (newPositions [a, a] []).card = 0
#guard (newPositions [] [a, a]).card = 2
#guard (newPositions [a] [b]).card = 1

end Tests.OptimalityDeadlines
