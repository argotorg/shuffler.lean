import Shuffler.Optimality.Collective.Retention
import Shuffler.Placement.Build

namespace Tests.OptimalityInventory

open Shuffler.Placement Shuffler.Optimality.Collective

private def a : Value := .Lit 1
private def b : Value := .Lit 2
private def source : Stack := [a, a, b]
private def target : Stack := [a, b, a, a, b]
private def missing : Multiset Value := {a, b}
private def result := buildOfReserve ∅ source target missing (by decide)
private def sample : Trace ∅ source target := result.trace
private def paid : Finset (Interval target) := Finset.univ.filter (Interval.Paid source)

-- Repeated source values leave the mandatory inventory one output at a time.
#guard (mandatory source target 0).card = 3
#guard (mandatory source target 1).card = 2
#guard (mandatory source target 2).card = 1
#guard (mandatory source target 3).card = 0
#guard capacity source target 2 = 15
#guard (Finset.univ : Finset (Interval target)).card = 3
#guard paid.card = 2
#guard (paid.filter fun gap => gap.Crosses 2).card = 1
#guard (paid.filter fun gap => gap.Crosses 3).card = 2
#guard (paid.filter fun gap => gap.Crosses 4).card = 1
#guard (paid.filter fun gap => gap.Crosses 5).card = 0
#guard (residual 2 sample).count a = 2
#guard (residual 3 sample).count a = 1

example : (mandatory source target 3).card +
    (paid.filter fun gap => gap.Crosses 3).card ≤ 16 := by
  apply paid_crossing_capacity sample result.noPop (by decide) (by decide)
  · intro gap hg
    exact (Finset.mem_filter.mp hg).2
  · simp only [residual, takeHeight_whole sample (show target.length ≤ 3 + 16 by decide),
      TracePrefix.whole]
    decide

-- Between the first and second b outputs, at least one b stays in the residual.
example : b ∈ residual 4 sample :=
  residual_mem_of_mem sample result.noPop (show 2 ≤ 4 by decide) b
    (by decide) (by
      simp only [residual, takeHeight_whole sample (show target.length ≤ 2 + 16 by decide),
        TracePrefix.whole]
      decide)

example : (takeHeight 19 sample).takePacked 17 = (takeHeight 17 sample).packed :=
  takeHeight_nested sample (by decide)

-- At height seventeen a fresh first output leaves seventeen mandatory copies.
-- Nat subtraction alone cannot express this failed capacity constraint.
#guard (mandatory (List.replicate 17 a) (b :: List.replicate 17 a) 1).card = 17
#guard capacity (List.replicate 17 a) (b :: List.replicate 17 a) 1 = 0
#guard ¬(mandatory (List.replicate 17 a) (b :: List.replicate 17 a) 1).card ≤ 16
#guard (mandatory [] [] 0).card = 0

private def lateSource : Stack := List.replicate 17 a
private def late : Trace ∅ lateSource (lateSource ++ [b]) := .Push b (by decide) (.Lit _)

#guard directBefore b 1 late = 0
#guard Shuffler.Optimality.Lineage.directCount b late = 1

example : directBefore b 1 late < Shuffler.Optimality.Lineage.directCount b late :=
  directBefore_lt_of_absent late (by trivial) b 1 (by decide) (by decide)

-- At cut two the final b is still outside the fixed output prefix.
example : directBefore b 1 late ≤ directBefore b 2 late :=
  directBefore_mono late b (by decide)

#guard (retained sample).card = 2

example : (mandatory source target 3).card +
    ((retained sample).filter fun gap => gap.Crosses 3).card ≤ 16 :=
  retained_capacity sample result.noPop (by decide) (by decide)

private def old : Stack := List.replicate 15 a
private def fresh : Stack := [b, .Lit 3, b, .Lit 3]
private def collective := buildOfReserve ∅ old (fresh ++ old) (fresh : Multiset Value) (by decide)

#guard ((Finset.univ : Finset (Interval (fresh ++ old))).filter (Interval.Paid old)).card = 2
#guard (retained collective.trace).card = 0

example (gap : Interval (fresh ++ old)) (hp : gap.Paid old)
    (hn : gap ∉ retained collective.trace) :
    directBefore gap.value (gap.start.val + 1) collective.trace <
      directBefore gap.value (gap.stop.val + 1) collective.trace :=
  unretained_direct_increase collective.trace collective.noPop gap hp hn

end Tests.OptimalityInventory
