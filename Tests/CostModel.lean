import Shuffler.CostModel
import Shuffler.BuildBottomUp.Theorems.Feasibility.Defs

open Shuffler

set_option maxRecDepth 16384

namespace CostModelTests

private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)
private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def c : Value := .Var ⟨44⟩
private def spills : SpillSet := {⟨42⟩, ⟨44⟩}

private def costs (addressWidth : PushEncoding) : PrimitiveCosts :=
  PrimitiveCosts.evm (fun _ => addressWidth)

-- A literal uses the fewest bytes that hold it. Junk uses PUSH0.
example : (Value.Lit 0).pushWidth = 0 := by decide
example : (Value.Lit 1).pushWidth = 1 := by decide
example : (Value.Lit 255).pushWidth = 1 := by decide
example : (Value.Lit 256).pushWidth = 2 := by decide
example : (Value.Lit (2 ^ 248 - 1)).pushWidth = 31 := by decide
example : (Value.Lit (2 ^ 248)).pushWidth = 32 := by decide
example : (Value.Lit (2 ^ 256 - 1)).pushWidth = 32 := by decide
example : Value.Wildcard.pushWidth = 0 := by decide
-- At each byte boundary: 2^(8k) - 1 needs k bytes, and 2^(8k) needs k + 1.
#guard (List.range 33).all fun k => (Value.Lit (2 ^ (8 * k) - 1)).pushWidth.val = k
#guard (List.range 32).all fun k => (Value.Lit (2 ^ (8 * k))).pushWidth.val = k + 1

-- PUSHn costs n + 1 bytes. PUSH0 costs 2 gas, and PUSH1 to PUSH32 cost 3 gas.
example : (0 : PushEncoding).cost = ⟨2, 1⟩ := rfl
example : (1 : PushEncoding).cost = ⟨3, 2⟩ := rfl
example : (32 : PushEncoding).cost = ⟨3, 33⟩ := rfl
example : ∀ width : PushEncoding, width.cost.bytes = width.val + 1 := by decide
example : ∀ width : PushEncoding, width ≠ 0 → width.cost.gas = 3 := by decide

private def appendZeros (spills : SpillSet) (source : Stack) : (n : Nat) →
    Trace spills source (source ++ List.replicate n zero)
  | 0 => by simpa using (Trace.Lit (spills := spills) source)
  | n + 1 => by
    simpa only [List.replicate_succ', List.append_assoc] using
      (Trace.Push zero (by decide) (appendZeros spills source n))

-- One SWAP can avoid a wide PUSH, although it costs more gas.
private def shortSource : Stack := [wide] ++ List.replicate 15 zero
private def shortTarget : Stack := [wide] ++ List.replicate 16 zero ++ [wide]
private def shortCopy : Trace ∅ shortSource (shortSource ++ [wide]) :=
  .Dup 16 (by decide) (by decide) (by decide) (.Lit _)
private def shortZero : Trace ∅ shortSource (shortSource ++ [wide, zero]) :=
  .Push zero (by decide) shortCopy
private def shortBytes : Trace ∅ shortSource shortTarget :=
  .Swap 1 (by decide) (by decide) (by decide) shortZero
private def shortPushZero : Trace ∅ shortSource (shortSource ++ [zero]) :=
  .Push zero (by decide) (.Lit _)
private def shortGas : Trace ∅ shortSource shortTarget :=
  .Push wide (by decide) shortPushZero

example : shortBytes.noPop := trivial
example : shortGas.noPop := trivial
example : shortBytes.additions = shortGas.additions := by decide
example : Eligible {wide, zero} shortBytes := ⟨trivial, by decide⟩
example : ¬Eligible {zero} shortBytes := by
  intro h
  have hc := congrArg Multiset.card h.2
  change 2 = 1 at hc
  omega
#guard traceCost (costs 1) shortGas = { gas := 5, bytes := 34 }
#guard traceCost (costs 1) shortBytes = { gas := 8, bytes := 3 }

-- The required copy must cross seventeen new positions if PUSH32 is avoided.
private def longTarget : Stack := [wide] ++ List.replicate 32 zero ++ [wide]
private def longGasZeros : Trace ∅ shortSource (shortSource ++ List.replicate 17 zero) :=
  appendZeros ∅ shortSource 17
private def longGas : Trace ∅ shortSource longTarget :=
  .Push wide (by decide) longGasZeros
private def longBytesZeros : Trace ∅ shortSource
    (shortSource ++ [wide] ++ List.replicate 16 zero) :=
  shortCopy.concat (appendZeros ∅ (shortSource ++ [wide]) 16)
private def longCarry : Trace ∅ shortSource ([wide] ++ List.replicate 31 zero ++ [wide]) :=
  .Swap 16 (by decide) (by decide) (by decide) longBytesZeros
private def longLastZero : Trace ∅ shortSource ([wide] ++ List.replicate 31 zero ++ [wide, zero]) :=
  .Push zero (by decide) longCarry
private def longBytes : Trace ∅ shortSource longTarget :=
  .Swap 1 (by decide) (by decide) (by decide) longLastZero

example : longBytes.noPop := trivial
example : longGas.noPop := trivial
example : longBytes.additions = longGas.additions := by decide
#guard traceCost (costs 1) longGas = { gas := 37, bytes := 50 }
#guard traceCost (costs 1) longBytes = { gas := 43, bytes := 20 }
#guard (traceCost (costs 1) longGas).score Weights.gasOnly <
    (traceCost (costs 1) longBytes).score Weights.gasOnly
#guard (traceCost (costs 1) longBytes).score Weights.bytesOnly <
    (traceCost (costs 1) longGas).score Weights.bytesOnly
#guard (traceCost (costs 1) longGas).score ⟨5, 1, by decide⟩ =
    (traceCost (costs 1) longBytes).score ⟨5, 1, by decide⟩
#guard (traceCost (costs 1) longBytes).score ⟨4, 1, by decide⟩ <
    (traceCost (costs 1) longGas).score ⟨4, 1, by decide⟩
#guard (traceCost (costs 1) longGas).score ⟨6, 1, by decide⟩ <
    (traceCost (costs 1) longBytes).score ⟨6, 1, by decide⟩
#guard decide (¬(traceCost (costs 1) longGas).Dominates (traceCost (costs 1) longBytes))
#guard decide (¬(traceCost (costs 1) longBytes).Dominates (traceCost (costs 1) longGas))

-- Two SWAPs and one LOAD cost less than one SWAP and three LOADs.
private def loadSource : Stack := [a, b] ++ List.replicate 14 zero
private def loadTarget : Stack := [a, a] ++ List.replicate 14 zero ++ [c, b, a]
private def firstCopy : Trace spills loadSource (loadSource ++ [a]) :=
  .Dup 16 (by decide) (by decide) (by decide) (.Lit _)
private def secondCopy : Trace spills loadSource (loadSource ++ [a, a]) :=
  .Dup 1 (by decide) (by decide) (by decide) firstCopy
private def copiesPlaced : Trace spills loadSource
    ([a, a] ++ List.replicate 14 zero ++ [a, b]) :=
  .Swap 16 (by decide) (by decide) (by decide) secondCopy
private def loadedC : Trace spills loadSource
    ([a, a] ++ List.replicate 14 zero ++ [a, b, c]) :=
  .Load ⟨44⟩ (by decide) copiesPlaced
private def fewerLoads : Trace spills loadSource loadTarget :=
  .Swap 2 (by decide) (by decide) (by decide) loadedC
private def firstLoad : Trace spills loadSource (loadSource ++ [c]) :=
  .Load ⟨44⟩ (by decide) (.Lit _)
private def secondLoad : Trace spills loadSource (loadSource ++ [c, a]) :=
  .Load ⟨42⟩ (by decide) firstLoad
private def loadPlaced : Trace spills loadSource
    ([a, a] ++ List.replicate 14 zero ++ [c, b]) :=
  .Swap 16 (by decide) (by decide) (by decide) secondLoad
private def fewerSwaps : Trace spills loadSource loadTarget :=
  .Load ⟨42⟩ (by decide) loadPlaced

example : fewerLoads.noPop := trivial
example : fewerSwaps.noPop := trivial
example : fewerLoads.additions = fewerSwaps.additions := by decide
#guard traceCost (costs 1) fewerLoads = { gas := 18, bytes := 7 }
#guard traceCost (costs 1) fewerSwaps = { gas := 21, bytes := 10 }
#guard traceCost (costs 32) fewerLoads = { gas := 18, bytes := 38 }
#guard traceCost (costs 32) fewerSwaps = { gas := 21, bytes := 103 }
#guard ((List.finRange 32).map Fin.succ).all fun width =>
    decide (traceCost (costs width) fewerLoads = { gas := 18, bytes := width.val + 6 })
#guard ((List.finRange 32).map Fin.succ).all fun width =>
    decide (traceCost (costs width) fewerSwaps = { gas := 21, bytes := 3 * width.val + 7 })
#guard decide ((traceCost (costs 1) fewerLoads).Dominates (traceCost (costs 1) fewerSwaps))
#guard decide (¬(traceCost (costs 1) fewerLoads).Dominates (traceCost (costs 1) fewerLoads))

-- C++ prices LOAD as six gas, including an address encoded with PUSH0.
private def loadOnly : Trace spills [] [a] := .Load ⟨42⟩ (by decide) (.Lit [])
#guard traceCost (PrimitiveCosts.evm (fun _ => 0)) loadOnly =
    { gas := 5, bytes := 2 }
#guard traceCost (PrimitiveCosts.cppEstimate (fun _ => 0)) loadOnly =
    { gas := 6, bytes := 2 }

private def popped : Trace ∅ [zero] [] := .Pop (by decide) (.Lit [zero])
example : ¬Eligible 0 popped := by simp [Eligible, popped, Trace.noPop]
#guard traceCost (costs 1) popped = { gas := 2, bytes := 1 }

-- Restricting to no POP can exclude a trace with less gas at the same endpoints.
private def popSource : Stack := [.Lit 1, .Lit 2, zero]
private def popTarget : Stack := [.Lit 2, .Lit 1, zero]
private def pureFirst : Trace ∅ popSource [.Lit 1, zero, .Lit 2] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit _)
private def pureSecond : Trace ∅ popSource [.Lit 2, zero, .Lit 1] :=
  .Swap 2 (by decide) (by decide) (by decide) pureFirst
private def pureTrace : Trace ∅ popSource popTarget :=
  .Swap 1 (by decide) (by decide) (by decide) pureSecond
private def removedTop : Trace ∅ popSource [.Lit 1, .Lit 2] :=
  .Pop (by decide) (.Lit _)
private def swappedBelow : Trace ∅ popSource [.Lit 2, .Lit 1] :=
  .Swap 1 (by decide) (by decide) (by decide) removedTop
private def restoredTop : Trace ∅ popSource popTarget :=
  .Push zero (by decide) swappedBelow

example : Shuffler.Placement.Reserve ∅ popSource popTarget 0 := by
  unfold Shuffler.Placement.Reserve
  decide
example : Eligible 0 pureTrace := ⟨trivial, rfl⟩
example : restoredTop.additions = {zero} := rfl
example : ¬Eligible 0 restoredTop := by
  simp [Eligible, restoredTop, swappedBelow, removedTop, Trace.noPop]
#guard traceCost (costs 1) pureTrace = { gas := 9, bytes := 3 }
#guard traceCost (costs 1) restoredTop = { gas := 7, bytes := 3 }

-- Generation may keep the original output order; placement fixes its target.
example : ¬GenerationWeightedOptimal (costs 1) Weights.gasOnly 0 pureTrace := by
  intro h
  have hle := h.2 popSource (Trace.Lit popSource) ⟨trivial, rfl⟩
  change 9 ≤ 0 at hle
  omega

example : ¬GenerationParetoOptimal (costs 1) 0 pureTrace := by
  intro h
  have hno := h.2 popSource (Trace.Lit popSource) ⟨trivial, rfl⟩
  exact hno ⟨⟨by decide, by decide⟩, Or.inl (by decide)⟩

-- The C++ bound is 3 gas and 1 byte per SWAP and 6 gas and 34 bytes per addition.
private def wideAddress : VarId → PushEncoding := fun _ => 32

example : (traceCost (PrimitiveCosts.cppEstimate wideAddress) fewerSwaps).gas ≤
      3 * fewerSwaps.swapCount + 6 * fewerSwaps.additions.card ∧
    (traceCost (PrimitiveCosts.cppEstimate wideAddress) fewerSwaps).bytes ≤
      fewerSwaps.swapCount + 34 * fewerSwaps.additions.card :=
  cpp_noPop_cost_bound wideAddress fewerSwaps trivial

-- A LOAD of a 32-byte address and a SWAP meet the bound.
#guard traceCost (PrimitiveCosts.cppEstimate wideAddress) loadOnly =
    { gas := 6, bytes := 34 }
#guard traceCost (PrimitiveCosts.cppEstimate wideAddress) pureFirst =
    { gas := 3, bytes := 1 }

-- The bound does not hold with POP.
#guard popped.swapCount = 0 ∧ popped.additions = 0
#guard (traceCost (PrimitiveCosts.cppEstimate wideAddress) popped).gas = 2

end CostModelTests
