import Shuffler.Optimality.BirthPlacement.FixedWord.Sharpness.Theorems

namespace Tests.OptimalityFixedWordSharpness

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement
open Shuffler.Optimality.BirthPlacement.Sharpness

-- These checks execute the production parser, optimizer, realizer, and
-- SWAP-run normalizer. They check the complete emitted instruction list.
#guard (List.range 15).all fun offset =>
  check (offset + 2) .gasOnly && check (offset + 2) .bytesOnly
#guard check 32 .gasOnly && check 32 .bytesOnly
#guard check 64 .gasOnly && check 64 .bytesOnly

-- (candidate SWAPs, optimum SWAPs, normalized candidate SWAPs,
--  candidate surplus, optimum surplus, generation baseline).
#guard facts 2 .gasOnly = some (3, 2, 3, 9, 6, 21)
#guard facts 3 .gasOnly = some (5, 3, 5, 15, 9, 30)
#guard facts 8 .gasOnly = some (15, 8, 15, 45, 24, 75)
#guard facts 16 .gasOnly = some (31, 16, 31, 93, 48, 147)
#guard facts 32 .gasOnly = some (63, 32, 63, 189, 96, 291)
#guard facts 64 .gasOnly = some (127, 64, 127, 381, 192, 579)
#guard facts 2 .bytesOnly = some (3, 2, 3, 3, 2, 10)
#guard facts 3 .bytesOnly = some (5, 3, 5, 5, 3, 14)
#guard facts 8 .bytesOnly = some (15, 8, 15, 15, 8, 34)
#guard facts 64 .bytesOnly = some (127, 64, 127, 127, 64, 258)

private def reference8 := (replay (spills 8) [] (comparisonOps 8)).get (by decide)

-- The reference facts below are kernel proofs, not only execution checks.
example : reference8.target = target 8 := by decide
example : SwapRuns.births reference8.built.trace = word 8 := by decide
example : reference8.built.trace.swapCount = 8 := by decide
example : (traceCost costs reference8.built.trace).gas = 99 := by decide
example : (traceCost costs reference8.built.trace).bytes = 42 := by decide

theorem reference8_swaps_optimal (other : Trace (spills 8) [] (target 8))
    (hpop : other.noPop) (hword : SwapRuns.births other = word 8) :
    reference8.built.trace.swapCount ≤ other.swapCount := by
  have hlo := swaps_lower_bound 8 (by decide) other hpop hword
  have href : reference8.built.trace.swapCount = 8 := by decide
  omega

theorem reference8_gas_optimal (other : Trace (spills 8) [] (target 8))
    (hpop : other.noPop) (hword : SwapRuns.births other = word 8) :
    (traceCost costs reference8.built.trace).gas ≤ (traceCost costs other).gas := by
  have hlo := gas_lower_bound 8 (by decide) other hpop hword
  have hb : baseline costs .gasOnly (spills 8) [] (target 8 : Multiset Value) = 75 := by decide
  have href : (traceCost costs reference8.built.trace).gas = 99 := by decide
  omega

theorem reference8_bytes_optimal (other : Trace (spills 8) [] (target 8))
    (hpop : other.noPop) (hword : SwapRuns.births other = word 8) :
    (traceCost costs reference8.built.trace).bytes ≤ (traceCost costs other).bytes := by
  have hlo := bytes_lower_bound 8 (by decide) other hpop hword
  have hb : baseline costs .bytesOnly (spills 8) [] (target 8 : Multiset Value) = 34 := by decide
  have href : (traceCost costs reference8.built.trace).bytes = 42 := by decide
  omega

-- The general lower bound has no limit on count and permits every
-- direct/DUP choice and every equal-copy occurrence assignment.
example (count : Nat) (hk : 2 ≤ count)
    (trace : Trace activeSpills [] (target count)) (hpop : trace.noPop)
    (hword : SwapRuns.births trace = word count) : count ≤ trace.swapCount :=
  swaps_lower_bound count hk trace hpop hword

end Tests.OptimalityFixedWordSharpness
