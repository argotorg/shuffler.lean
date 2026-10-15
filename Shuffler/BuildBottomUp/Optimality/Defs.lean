import Shuffler.BuildBottomUp.Defs
import Shuffler.Optimality.Baseline

/-! Definitions used in the statements of `BBU.Theorems`. -/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

--- SWAP bounds ------------------------------------------------------------------------------------

-- A successful run moves the top and at most `reach` slots below it.
-- It emits at most reach + reach / 2 swaps.
def permuteSwapBound (length : Nat) : Nat :=
  let reach := min length (MAX_SWAP_DEPTH + 1) - 1
  reach + reach / 2

-- The maximum count of new SWAPs for n ≤ 1 initial values and k pending generations.
def smallSwapBound (n k : ℕ) : ℕ := if n = 0 then 0 else (k + 15) / 16

-- The new SWAP counts of successful calls from Valid states with n slots and k pending.
def swapCounts (n k : Nat) : Set Nat :=
  {count | ∃ (source target : Stack) (spills : SpillSet)
      (initial : State source target spills) (hvalid : initial.Valid) (result : Stack)
      (trace : Trace spills source result),
      initial.pending_generations = k ∧ initial.stack.length = n ∧
      buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧
      trace.swapCount = initial.trace.swapCount + count}

/-! The window bound U = 2 (n - 1) + 2k - 2 for 3 ≤ n ≤ 17 is attained on these (n, k). -/

def WindowAttained (n k : Nat) : Prop :=
  k ≤ 2 ∨ (k = 3 ∧ 4 ≤ n) ∨ 16 ≤ n ∨ (n = 15 ∧ k % 16 ≠ 2 ∧ k % 16 ≠ 3)

instance (n k : Nat) : Decidable (WindowAttained n k) := by
  unfold WindowAttained
  infer_instance

-- The proved bound on new SWAPs for n slots and k pending generations. For n = 2
-- and k ≥ 1 it is the window bound; no smaller bound is proved there.
def bbuSwapBound (n k : Nat) : Nat :=
  if n ≤ 1 then smallSwapBound n k
  else if k = 0 then permuteSwapBound n
  else if n = 2 then 2 * k + 2
  else 2 * (min n (MAX_SWAP_DEPTH + 1) - 1) + 2 * k - 2

--- Excess -----------------------------------------------------------------------------------------

-- The price of the dearer of DUP and direct introduction above `unitPrice`.
def excessPrice (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (value : Value) : Nat :=
  max (costs.dup.score weights) (directPrice costs weights spills value) -
    unitPrice costs weights spills value

-- The excess price of each value absent from the source. Its first birth is
-- a PUSH or LOAD, and B already charges that price.
def freshExcess (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source : Stack) (missing : Multiset Value) : Nat :=
  missing.toFinset.sum fun value =>
    if value ∈ source then 0 else excessPrice costs weights spills value

--- Families ---------------------------------------------------------------------------------------

/-! Family F1: 17 source slots hold the cycle 0 → 1 → … → 16 → 0 and k targets are
pending. Target j holds the spilled variable j, so every generated slot is a LOAD. -/

-- The cycle t → t + 1 → … → t + w → t on slot labels.
def rot (t w i : Nat) : Nat := if t ≤ i ∧ i < t + w then i + 1 else if i = t + w then t else i

theorem rot_lt (h : t + w < len) (hi : i < len) : rot t w i < len := by
  unfold rot
  split_ifs <;> omega

def f1Source : Stack := List.ofFn fun i : Fin 17 => .Var ⟨rot 0 16 i.val⟩

def f1Target (k : Nat) : Stack := List.ofFn fun j : Fin (17 + k) => .Var ⟨j.val⟩

def f1Spills (k : Nat) : SpillSet := (Finset.range (17 + k)).image VarId.mk

@[simp] theorem f1Source_length : f1Source.length = 17 := by simp [f1Source]

@[simp] theorem f1Target_length : (f1Target k).length = 17 + k := by simp [f1Target]

-- Source slot i is bound to target rot 0 16 i.
def f1Mapping (k : Nat) : Mapping f1Source.length (f1Target k).length where
  toFun i := some ⟨rot 0 16 i.val, by
    have := i.isLt
    simp only [f1Source_length, f1Target_length] at *
    exact rot_lt (by omega) (by omega)⟩
  invFun j := if h : j.val < 17 then some ⟨if j.val = 0 then 16 else j.val - 1, by
    simp only [f1Source_length]
    split_ifs <;> omega⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    simp only [f1Source_length, f1Target_length] at *
    by_cases h : j.val < 17
    · simp only [h, ↓reduceDIte, Option.some.injEq, Fin.ext_iff, rot]
      split_ifs <;> omega
    · simp only [h, ↓reduceDIte, reduceCtorEq, false_iff, Option.some.injEq,
        Fin.ext_iff, rot]
      split_ifs <;> omega

def f1State (k : Nat) : State f1Source (f1Target k) (f1Spills k) where
  planned_mapping := f1Mapping k
  stack := f1Source
  trace := .Lit f1Source
  mapping := f1Mapping k
  pending_generations := k

def f1Costs (address : PushEncoding) : PrimitiveCosts :=
  PrimitiveCosts.cppEstimate fun _ => address

end Shuffler.Optimality.BBU
