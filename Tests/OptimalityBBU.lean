import Shuffler.BuildMapping
import Shuffler.BuildBottomUp.Optimality.Theorems
import Tests.BuildBottomUpObservations

open Shuffler Shuffler.Optimality Shuffler.BuildBottomUp BuildBottomUpTestSupport

namespace OptimalityBBUTests

private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)

-- Use the production mapping builder and the production BBU call. A failed
-- call keeps its Error value so it cannot appear to have zero operations.
private def initial (source target : Stack) : State source target ∅ :=
  let mapping := (MappingBuilder.buildMapping source target
    (List.replicate source.length 0) .Leave (by simp)).mapping
  {
    planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := target.length - source.length
  }

private def run (source target : Stack) : Except Error (List Operation) :=
  (runIfValid (initial source target)).map fun result =>
    operations result.2

private def swaps (ops : List Operation) : Nat :=
  (ops.filter fun op => match op with | .swap _ => true | _ => false).length

#guard run [zero] [zero,zero] = .ok [.dup 1]
#guard run [zero,zero] [zero,zero] = .ok []

-- Final Permute needs three swaps for each of eight disjoint lower pairs.
private def distinct17 : Stack := (List.range 17).map (fun i => .Var ⟨i⟩)
private def paired17 : Stack :=
  (List.range 17).map (fun i => .Var ⟨if i = 16 then i else i ^^^ 1⟩)

#guard (run distinct17 paired17).map swaps = .ok 24

-- This includes the final Permute and refutes the proposed 2k+24 bound.
private def rotated18 : Stack := distinct17.drop 1 ++ [.Lit 99, .Var ⟨0⟩]

#guard (run distinct17 rotated18).map swaps = .ok 31
#guard (run distinct17 rotated18).map List.length = .ok 32

-- The first DUP puts the old wide literal outside DUP reach.
private def wideSource : Stack := [wide] ++ List.replicate 15 zero

#guard run wideSource (wideSource ++ [zero,wide]) = .ok [.dup 1,.push wide]

-- Changed values below SWAP reach cause an explicit error.
private def blockedSource : Stack := [.Var ⟨0⟩] ++ List.replicate 17 zero
private def blockedTarget : Stack := List.replicate 17 zero ++ [.Var ⟨0⟩]

#guard match run blockedSource blockedTarget with
  | .error (.blocked _) => true
  | _ => false

-- The live budget: swaps ≤ 2 * live 0 + 2 * k for the new suffix.
private def live0 (source target : Stack) : Nat :=
  Shuffler.Optimality.BBU.live 0 (initial source target)

private def budget (source target : Stack) : Nat :=
  2 * live0 source target + 2 * (target.length - source.length)

-- The window budget: swaps ≤ 2 * (min n 17 - 1) + 2 * k.
private def window (source target : Stack) : Nat :=
  2 * (min source.length 17 - 1) + 2 * (target.length - source.length)

-- F1: target[0] = v(n-1), target[j] = v(j-1), and k distinct literal holes.
private def rotation (n k : Nat) : Stack :=
  (List.range (n + k)).map fun j =>
    if j = 0 then .Var ⟨n - 1⟩ else if j < n then .Var ⟨j - 1⟩ else .Lit (Fin.ofNat _ (1000 + j))

private def distinct (n : Nat) : Stack := (List.range n).map (fun i => .Var ⟨i⟩)

-- At n = 17 no slot holds its destination. The 16 window slots below the top are live.
#guard live0 (distinct 17) (rotation 17 5) = 16
#guard (run (distinct 17) (rotation 17 5)).map swaps = .ok (2 * 5 + 16)
#guard budget (distinct 17) (rotation 17 5) = 2 * 16 + 2 * 5
#guard window (distinct 17) (rotation 17 5) = 2 * 16 + 2 * 5
#guard (run (distinct 17) (rotation 17 0)).map swaps = .ok 16
#guard (run (distinct 17) (rotation 17 1)).map swaps = .ok 18

-- Only the top 17 of 20 slots are inside SWAP reach, and the top is not live.
#guard live0 (distinct 20) (rotation 20 0) = 16
#guard live0 (distinct 20) (distinct 20) = 0
#guard window (distinct 20) (rotation 20 0) = 32

-- n = 0: there is no live slot and generation emits no swap.
#guard live0 [] [] = 0
#guard run [] [] = .ok []
#guard window [] [] = 0
#guard live0 [] [zero, .Lit 1] = 0
#guard (run [] [zero, .Lit 1]).map swaps = .ok 0
#guard budget [] [zero, .Lit 1] = 4

-- k = 0: the eight lower transpositions use 24 of the 32 budget swaps.
#guard live0 distinct17 paired17 = 16
#guard budget distinct17 paired17 = 32
#guard window distinct17 paired17 = 32
#guard (run distinct17 paired17).map swaps = .ok 24

-- n = 1: the single slot is the top and is not live.
#guard live0 [zero] [zero] = 0
#guard (run [zero] [zero]).map swaps = .ok 0
#guard live0 [zero] [zero, zero] = 0
#guard (run [zero] [zero, zero]).map swaps = .ok 0
-- The generated literal goes below the top with one swap; the budget is 2.
#guard live0 [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] = 0
#guard (run [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩]).map swaps = .ok 1
#guard budget [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] = 2

-- The 17-value rotation uses 31 of 34 budget swaps.
#guard budget distinct17 rotated18 = 34

-- With pending coefficient 1 the bound fails: 56 > 2 * 16 + 20.
#guard (run (distinct 17) (rotation 17 20)).map swaps = .ok 56
#guard 2 * live0 (distinct 17) (rotation 17 20) + 20 < 56
#guard 56 ≤ budget (distinct 17) (rotation 17 20)

-- A budget 2 smaller fails at n = 1: one swap, budget 2.
#guard budget [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] - 2 < 1
#guard window [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] - 2 < 1

-- At n = 17 these targets need 2k + 30 swaps for k = 1, 2, 3: 2 below the window budget.
-- A window budget 4 smaller fails on each of them.
private def code (c : Nat) : Value :=
  if c % 3 = 1 then .Lit (Fin.ofNat _ (c / 3)) else .Var ⟨c / 3 - 1⟩

private def tight1 : Stack :=
  [48, 51, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 46, 42, 45].map code
private def tight2 : Stack :=
  [45, 51, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 48, 52, 51].map code
private def tight3 : Stack :=
  [48, 51, 6, 3, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 52, 55, 51].map code

#guard distinct17 = (List.range 17).map fun i => code (3 + 3 * i)
#guard (run distinct17 tight1).map swaps = .ok (2 * 1 + 30)
#guard (run distinct17 tight2).map swaps = .ok (2 * 2 + 30)
#guard (run distinct17 tight3).map swaps = .ok (2 * 3 + 30)
#guard live0 distinct17 tight1 = 16 ∧ live0 distinct17 tight2 = 16 ∧ live0 distinct17 tight3 = 16
#guard window distinct17 tight1 = 2 * 1 + 32
#guard window distinct17 tight3 = 2 * 3 + 32
#guard window distinct17 tight1 - 4 < 2 * 1 + 30
#guard window distinct17 tight2 - 4 < 2 * 2 + 30
#guard window distinct17 tight3 - 4 < 2 * 3 + 30

-- The bound of SharpBound.lean: swaps ≤ 2 * (min n 17 - 1) + 2k - 2 for k ≥ 1 and n ≥ 3.
-- tight1..3 meet it with equality.
#guard (run distinct17 tight1).map swaps = .ok (window distinct17 tight1 - 2)
#guard (run distinct17 tight2).map swaps = .ok (window distinct17 tight2 - 2)
#guard (run distinct17 tight3).map swaps = .ok (window distinct17 tight3 - 2)
-- n = 3, k = 1 meets it with equality: 4 swaps.
private def small3 : Stack := [.Var ⟨1⟩, .Var ⟨2⟩, .Var ⟨0⟩, .Var ⟨0⟩]
#guard (run (distinct 3) small3).map swaps = .ok 4
#guard window (distinct 3) small3 - 2 = 4
-- k = 0 is outside it: a lower transposition at n = 3 uses 3 > 4 - 2 swaps.
private def swapped3 : Stack := [.Var ⟨1⟩, .Var ⟨0⟩, .Var ⟨2⟩]
#guard (run (distinct 3) swapped3).map swaps = .ok 3
#guard window (distinct 3) swapped3 - 2 < 3
-- n ≤ 2 with k = 1 is outside it. There swaps + 1 = 2 * live 0 + 2k.
private def small2 : Stack := [.Var ⟨1⟩, .Var ⟨0⟩, .Var ⟨0⟩]
#guard (run (distinct 2) small2).map swaps = .ok 3
#guard window (distinct 2) small2 - 2 < 3
#guard budget (distinct 2) small2 = 3 + 1
#guard (run [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩]).map swaps = .ok 1
#guard window [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] - 2 < 1
#guard budget [.Var ⟨0⟩] [.Lit 1, .Var ⟨0⟩] = 1 + 1
-- n = 2, k = 2 meets it with equality: 4 swaps.
private def small2k2 : Stack := [.Lit 5, .Var ⟨0⟩, .Var ⟨1⟩, .Var ⟨0⟩]
#guard (run (distinct 2) small2k2).map swaps = .ok 4
#guard window (distinct 2) small2k2 - 2 = 4

-- k = 4: two DUP16 births put the last two targets above the hole at 18.
private def tight4 : Stack :=
  [48, 51, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 52, 55, 51, 6].map code

#guard (run distinct17 tight4).map swaps = .ok (2 * 4 + 30)
#guard live0 distinct17 tight4 = 16
#guard window distinct17 tight4 = 2 * 4 + 32

-- k ≥ 5: births at 17 .. k + 13 are literals and the last two are DUP16 copies of v(k-4)
-- and v(k-3). The literal hole at k + 14 is born last, at the cursor.
private def tightK (k : Nat) : Stack :=
  (List.range (17 + k)).map fun j =>
    if j = 0 then .Var ⟨15⟩ else if j = 1 then .Var ⟨16⟩ else if j ≤ 16 then .Var ⟨j - 2⟩
    else if j = k + 15 then .Var ⟨k - 4⟩ else if j = k + 16 then .Var ⟨k - 3⟩
    else .Lit (Fin.ofNat _ j)

#guard tightK 5 = [48, 51, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45,
  52, 55, 58, 6, 9].map code

-- `lift b` puts b values below the stack that are already at their destination.
private def lift (b : Nat) (stack : Stack) : Stack :=
  (List.range b).map (fun i => .Var ⟨i⟩) ++ stack.map fun
    | .Var ⟨i⟩ => .Var ⟨i + b⟩
    | value => value

private def tight (k : Nat) : Stack :=
  match k with
  | 0 => paired17 | 1 => tight1 | 2 => tight2 | 3 => tight3 | 4 => tight4 | k => tightK k

-- For n = 17 .. 20 and k = 1 .. 8 these reach 2k + 30, 2 below the window budget.
-- For k = 0 the lifted pairs reach 24.
#guard (List.range 4).all fun b => (List.range 9).all fun k =>
  let source := distinct (17 + b)
  let target := lift b (tight k)
  (run source target).map swaps == .ok (if k = 0 then 24 else 2 * k + 30) &&
    live0 source target == 16 && window source target == 2 * k + 32
#guard (run (distinct 17) (tightK 17)).map swaps = .ok (2 * 17 + 30)

-- F1 with spilled holes, as proved in GenerationLowerBound.lean: 2k + 16 swaps.
section
open Shuffler.Optimality.BBU

private def f1Swaps (k : Nat) : Except Error Nat :=
  (Shuffler.BuildBottomUp.buildBottomUp (f1State k) (f1_valid k)).map (·.2.swapCount)

#guard f1Source = (List.range 16).map (fun i => .Var ⟨i + 1⟩) ++ [.Var ⟨0⟩]
#guard f1Target 2 = (List.range 19).map fun j => .Var ⟨j⟩
#guard f1Swaps 0 = .ok 16
#guard f1Swaps 1 = .ok 18
#guard f1Swaps 2 = .ok 20
#guard f1Swaps 10 = .ok 36
#guard f1Swaps 100 = .ok 216
-- The count is exact, not a bound. The window budget 2k + 32 is 16 above it.
#guard f1Swaps 10 = .ok (2 * (17 - 1) + 2 * 10 - 16)
#guard f1Swaps 10 ≠ .ok 35 ∧ f1Swaps 10 ≠ .ok 37
-- Coefficient 1 on k fails at k = 100: 216 > 2 * 17 + 100.
#guard match f1Swaps 100 with | .ok s => 2 * 17 + 100 < s | .error _ => false
end

-- F1 cost under the C++ estimate.
-- Every birth is a LOAD, so gas is 12k + 48. A 32-byte address gives 36k + 16 bytes.
section
open Shuffler.Optimality.BBU

private def wideAddress : VarId → PushEncoding := fun _ => 32

private def f1Cost (address : VarId → PushEncoding) (k : Nat) : Except Error Cost :=
  (Shuffler.BuildBottomUp.buildBottomUp (f1State k) (f1_valid k)).map fun result =>
    traceCost (PrimitiveCosts.cppEstimate address) result.2

private def f1Births (k : Nat) : Except Error (Nat × Nat × Nat) :=
  (Shuffler.BuildBottomUp.buildBottomUp (f1State k) (f1_valid k)).map fun result =>
    (dupCount result.2, pushCount result.2, loadCount result.2)

#guard f1Births 0 = .ok (0, 0, 0)
#guard f1Births 10 = .ok (0, 0, 10)
#guard f1Cost wideAddress 0 = .ok ⟨48, 16⟩
#guard f1Cost wideAddress 1 = .ok ⟨60, 52⟩
#guard f1Cost wideAddress 10 = .ok ⟨168, 376⟩
-- A PUSH0 address changes bytes only: 2k + 16 + 2k.
#guard f1Cost (fun _ => 0) 10 = .ok ⟨168, 56⟩
-- The window cost bound is 12k + 96 gas and 36k + 32 bytes; F1 is 48 and 16 below it.
#guard f1Cost wideAddress 10 = .ok ⟨12 * 10 + 96 - 48, 36 * 10 + 32 - 16⟩
-- Gas coefficient 11 on k fails at k = 60: 768 > 11 * 60 + 96.
#guard match f1Cost wideAddress 60 with | .ok c => 11 * 60 + 96 < c.gas | .error _ => false
end

-- A trace with a POP needs more births than the length change.
section
open Shuffler.Optimality.BBU

private def popped : Trace ∅ [zero] [zero, zero] :=
  .Push zero (by decide) (.Pop (by decide) (.Push (.Lit 1) (by decide) (.Lit [zero])))

#guard popped.additions.card = 2
#guard [zero].length + popped.additions.card - 1 = [zero, zero].length
end

-- Excess over the generation baseline B, as proved in Excess.lean and F1Excess.lean.
section
open Shuffler.Optimality.BBU

private def cpp : PrimitiveCosts := PrimitiveCosts.cppEstimate wideAddress

-- Score and B of the BBU trace. Each state below starts from `.Lit source`.
private def scored (weights : Weights) {source target : Stack} {spills : SpillSet} (state : State source target spills) :
    Except Error (Nat × Nat) :=
  (runIfValid state).map fun result =>
    ((traceCost cpp result.2).score weights, baseline cpp weights spills source result.2.additions)

-- The excess bound with the window budget in place of bbuSwapBound, minus `freshExcess`.
private def bound (weights : Weights) {source target : Stack} {spills : SpillSet} (state : State source target spills) :
    Except Error Nat :=
  (runIfValid state).map fun result =>
    baseline cpp weights spills source result.2.additions +
      cpp.swap.score weights * (2 * (min source.length 17 - 1) + 2 * state.pending_generations) +
      (result.2.additions.map (excessPrice cpp weights spills)).sum -
      freshExcess cpp weights spills source result.2.additions

private def holds (weights : Weights) {source target : Stack} {spills : SpillSet} (state : State source target spills) :
    Bool :=
  match scored weights state, bound weights state with
  | .ok (score, _), .ok limit => score ≤ limit
  | _, _ => false

private def gas := Weights.gasOnly
private def bytes := Weights.bytesOnly

-- Excess prices: PUSH0 against DUP, LOAD against DUP, and PUSH32 against DUP.
#guard excessPrice cpp gas ∅ zero = 1
#guard excessPrice cpp gas {⟨0⟩} (.Var ⟨0⟩) = 3
#guard excessPrice cpp gas ∅ (.Var ⟨0⟩) = 0
#guard excessPrice cpp gas ∅ wide = 0
#guard excessPrice cpp bytes ∅ wide = 32

#guard [gas, bytes].all fun w =>
  holds w (initial (distinct 17) (rotation 17 5)) && holds w (initial distinct17 tight1) &&
  holds w (initial distinct17 paired17) && holds w (initial [zero] [zero, zero]) &&
  holds w (initial wideSource (wideSource ++ [zero, wide])) &&
  holds w (initial [] [zero, .Lit 1]) && holds w (f1State 10)

-- F1: the BBU excess is 3 (2k + 16) gas. B is 6k gas, one LOAD per target.
#guard scored gas (f1State 0) = .ok (48, 0)
#guard scored gas (f1State 10) = .ok (168, 60)
#guard (List.range 12).all fun k => scored gas (f1State k) == .ok (12 * k + 48, 6 * k)
-- k = 8c exceeds c times the permute-first excess 48: here c = 1 and c = 4.
#guard match scored gas (f1State 8) with | .ok (s, b) => 1 * 48 < s - b | .error _ => false
#guard match scored gas (f1State 32) with | .ok (s, b) => 4 * 48 < s - b | .error _ => false
#guard match scored gas (f1State 7) with | .ok (s, b) => s - b = 1 * 48 + 3 * 14 | .error _ => false

-- The right side of `score_le_baseline_add` minus `freshExcess`, with the real SWAP count.
private def traceBound (weights : Weights) {source target : Stack} {spills : SpillSet}
    (state : State source target spills) : Except Error Nat :=
  (runIfValid state).map fun result =>
    baseline cpp weights spills source result.2.additions +
      cpp.swap.score weights * result.2.swapCount +
      (result.2.additions.map (excessPrice cpp weights spills)).sum -
      freshExcess cpp weights spills source result.2.additions

-- [0] → [0, 0]: BBU emits DUP1 and B is one PUSH0. The trace bound is attained.
#guard scored gas (initial [zero] [zero, zero]) = .ok (3, 2)
#guard traceBound gas (initial [zero] [zero, zero]) = .ok 3
#guard bound gas (initial [zero] [zero, zero]) = .ok (2 + 3 * 2 + 1)
#guard freshExcess cpp gas ∅ [zero] {zero} = 0 ∧ freshExcess cpp gas ∅ [] {zero} = 1
-- One DUP and one PUSH32 in bytes: B = 2 and the excess price is 32. The trace bound is attained.
#guard scored bytes (initial wideSource (wideSource ++ [zero, wide])) = .ok (34, 2)
#guard traceBound bytes (initial wideSource (wideSource ++ [zero, wide])) = .ok 34
-- F1 has only SWAPs and first LOADs, so the trace bound is attained in gas.
#guard (List.range 12).all fun k => traceBound gas (f1State k) == .ok (12 * k + 48)
#guard (List.range 12).all fun k => bound gas (f1State k) == .ok (12 * k + 96)
-- A bound without the SWAP term fails on F1: 168 > 60 + 3 * 10.
#guard match scored gas (f1State 10) with | .ok (s, b) => b + 3 * 10 < s | .error _ => false
end

end OptimalityBBUTests
