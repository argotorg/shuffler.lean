import Skel.Test.DiscoverSite

/-! A loop for the tests of the linear measures (`Skel/Test/DiscoverLin.lean`): two counters. While `a` is above zero, `a` falls
by one and `b` rises by one. Then `b` falls to zero, and the sum `w` counts those steps. No feature of the state falls at each
step. The sum `2 * a + b` falls by one at each step. It is a module of its own, so that the generated files of the tests import
it without the other tests. -/

namespace DiscoverLinSiteTests

/-- The state of the two counters and the sum. -/
structure Two where
  a : Nat
  b : Nat
  w : Nat
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/-- The loop. It terminates in `2 * a + b + 1` steps: `a` steps up, `a + b` steps down, and the exit. -/
def twoCount : Nat → Two → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if s.a = 0 then
      (if s.b = 0 then some s.w else twoCount n { s with b := s.b - 1, w := s.w + 1 })
    else twoCount n { s with a := s.a - 1, b := s.b + 1 }

example : twoCount 4 ⟨1, 1, 0⟩ = some 2 := by decide
example : twoCount 3 ⟨1, 1, 0⟩ = none := by decide

/-- The site of `twoCount`, as `siteOf?` gives it. -/
def twoCountJson : String := site_json% DiscoverLinSiteTests.twoCount

end DiscoverLinSiteTests
