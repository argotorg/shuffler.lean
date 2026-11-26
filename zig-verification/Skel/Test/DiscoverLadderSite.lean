import Skel.Test.DiscoverSite

/-! A loop for the tests of the discovery ladder (`Skel/Test/DiscoverLadder.lean`): the count-down of
`Skel/Test/DiscoverSite.lean` with a mutated step. The counter never falls, so no measure falls on its runs. It is a module of
its own, so that the generated files of the tests import it without the other tests. -/

namespace DiscoverLadderSiteTests

open DiscoverSiteTests

/-- The count-down with the step of the counter removed. -/
def stuckDown : Nat → Cnt → Option Nat
  | 0, _ => none
  | n + 1, s => if s.k = 0 then some s.acc else stuckDown n { s with acc := s.acc + 2 }

/-- The site of `stuckDown`, as `siteOf?` gives it. -/
def stuckJson : String := site_json% DiscoverLadderSiteTests.stuckDown

end DiscoverLadderSiteTests
