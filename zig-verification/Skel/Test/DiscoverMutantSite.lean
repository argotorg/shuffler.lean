import Skel.Discover.Mutants
import Skel.Test.DiscoverSite

/-! The loops and the mutants of the negative controls of the discovery (`Skel/Test/DiscoverMutants.lean`). It is a module of
its own, so that the generated files of the tests import it without the other tests.

The mutants are made by `mutate%` (`Skel/Discover/Mutants.lean`) on the functions of `Skel/Test/DiscoverSite.lean` and on
`gapLoop`. Each `example` is the ground truth of a mutant, checked by the kernel when this module is built: at the fuel of the
bound the mutant gives the value that the fuel gives out (`none`), where the original gives an exit value. So the claim of
the goals (`fuel_enough`) is false for each of these mutants, and no run of the discovery may close it. -/

namespace DiscoverMutantSiteTests

open DiscoverSiteTests Skel.Discover.Mutants

/-- The state of the gap loop: a counter `lo` that goes up to `hi`, and a sum. -/
structure Gap where
  lo : Nat
  hi : Nat
  w : Nat
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/-- The counter goes up by one until it is `hi`. It terminates from a state with `lo ≤ hi`: the fuel is `hi - lo + 1`. -/
def gapLoop : Nat → Gap → Option Nat
  | 0, _ => none
  | n + 1, s => if s.lo = s.hi then some s.w else gapLoop n { s with lo := s.lo + 1, w := s.w + 3 }

/-- A count-down with two recursive calls in two branches: an even counter falls by one, an odd counter falls by one and
adds to the sum. -/
def twoArm : Nat → Cnt → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if s.k = 0 then some s.acc
    else if s.k % 2 = 0 then twoArm n { s with k := s.k - 1 }
    else twoArm n { s with k := s.k - 1, acc := s.acc + 1 }

/-! ## The mutants -/

-- The count-down whose counter does not fall.
mutate% DiscoverSiteTests.countDown noFall 0 as cntNoFall
-- The count-down that calls itself with the entry state.
mutate% DiscoverSiteTests.countDown stall 0 as cntStall
-- The count-down with the branches of its test swapped.
mutate% DiscoverSiteTests.countDown wrongExit 0 as cntSwap
-- The count-down with `k + 1 = 0` as its test.
mutate% DiscoverSiteTests.countDown wrongExit 1 as cntOff
-- The two-arm loop whose even branch calls itself with the entry state: a partial stall, so the reader still has a site.
mutate% DiscoverMutantSiteTests.twoArm stall 0 as armStall
-- The gap loop with the counter going up by two.
mutate% DiscoverMutantSiteTests.gapLoop brokenInv 0 as gapSkip

/-! ## The ground truth: the claim is false for each mutant -/

/-- The original count-down, at the fuel `st.k + 1`, exits. -/
example : countDown 4 ⟨3, 0⟩ = some 6 := by decide
example : gapLoop 2 ⟨0, 1, 0⟩ = some 3 := by decide
example : twoArm 3 ⟨2, 0⟩ = some 1 := by decide

/-- No fuel is enough from `k = 3`, and from `k = 0` for the swapped test. -/
example : cntNoFall 4 ⟨3, 0⟩ = none := by decide
example : cntStall 4 ⟨3, 0⟩ = none := by decide
example : cntSwap 1 ⟨0, 0⟩ = none := by decide
example : cntOff 4 ⟨3, 0⟩ = none := by decide
example : gapSkip 2 ⟨0, 1, 0⟩ = none := by decide
example : armStall 3 ⟨2, 0⟩ = none := by decide
/-- The fuel `st.k + 1 - 1` is too small for the original function. -/
example : countDown 3 ⟨3, 0⟩ = none := by decide

/-! ## The sites -/

def cntNoFallJson : String := site_json% DiscoverMutantSiteTests.cntNoFall
def cntStallJson : String := site_json% DiscoverMutantSiteTests.cntStall
def cntSwapJson : String := site_json% DiscoverMutantSiteTests.cntSwap
def cntOffJson : String := site_json% DiscoverMutantSiteTests.cntOff
def twoArmJson : String := site_json% DiscoverMutantSiteTests.twoArm
def armStallJson : String := site_json% DiscoverMutantSiteTests.armStall
def gapLoopJson : String := site_json% DiscoverMutantSiteTests.gapLoop
def gapSkipJson : String := site_json% DiscoverMutantSiteTests.gapSkip

/-! ## The counts, computed when this module is built -/

def countNoFall : String := mutant_result% DiscoverSiteTests.countDown noFall
def countStall : String := mutant_result% DiscoverSiteTests.countDown stall
def countBroken : String := mutant_result% DiscoverSiteTests.countDown brokenInv
def countExit : String := mutant_result% DiscoverSiteTests.countDown wrongExit
def countSmall : String := mutant_result% DiscoverSiteTests.countDown smallFuel
def countArmStall : String := mutant_result% DiscoverMutantSiteTests.twoArm stall
def countGapBroken : String := mutant_result% DiscoverMutantSiteTests.gapLoop brokenInv
def countVecStall : String := mutant_result% DiscoverSiteTests.vecLoop stall
def countVecNoFall : String := mutant_result% DiscoverSiteTests.vecLoop noFall
def countBranchStall : String := mutant_result% DiscoverSiteTests.branchLoop stall
def countTwoCalls : String := mutant_result% DiscoverSiteTests.twoCalls stall
def countNotLoop : String := mutant_result% DiscoverSiteTests.notLoop noFall

end DiscoverMutantSiteTests
