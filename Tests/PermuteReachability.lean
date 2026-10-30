module

public meta import Shuffler.Permute.Defs
import Shuffler.Permute.Theorems
import Shuffler.Permute.Normalization
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Logic.Equiv.Fintype
public meta import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.VecNotation

namespace PermuteReachabilityTests

open Shuffler.Permute Shuffler.Emission

private instance {source : Stack} (perm : Permutation source) : Decidable (values_reachable perm) :=
  inferInstanceAs (Decidable (∀ i : Fin source.length,
    source[i] ≠ source[perm.symm i] → i.rev.val ≤ MAX_SWAP_DEPTH))

private def stateFor (stack : Stack) : State stack stack ∅ where
  planned_mapping := ⊥
  stack := stack
  trace := .Lit stack
  mapping := ⊥
  pending_generations := 0

private def check (stack : Stack) (perm : Permutation stack) : Bool :=
  match permute (stateFor stack) perm with
  | .error _ => false
  | .ok ⟨none, result⟩ => decide (values_reachable perm) &&
      decide (result.stack = apply_permutation stack perm)
  | .ok ⟨some blocked, _⟩ => !decide (values_reachable perm) &&
      decide (0 < blocked.excess)

private def boundaryPositions (n : ℕ) : Fin 4 ↪ Fin (n + 19) where
  toFun := fun i => match i.val with
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨n + 1, by omega⟩
    | 2 => ⟨n + 2, by omega⟩
    | _ => ⟨n + 18, by omega⟩
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private def positions18 : Fin 4 ↪ Fin 18 where
  toFun := ![0, 1, 16, 17]
  inj' := by decide

private def positions17 : Fin 4 ↪ Fin 17 where
  toFun := ![0, 1, 15, 16]
  inj' := by decide

private def checkLayout {n : ℕ} (positions : Fin 4 ↪ Fin n) (fill : ℕ)
    (a b c d : Fin 2) (perm : Equiv.Perm (Fin 4)) : Bool :=
  let active : Fin 4 → ℕ := ![a.val, b.val, c.val, d.val]
  let stack : Stack := List.ofFn fun i : Fin n =>
    .Var ⟨((List.finRange 4).find? (fun j => positions j = i)).map active |>.getD fill⟩
  check stack (by simpa [Permutation, stack] using perm.viaFintypeEmbedding positions)

-- All 24 permutations and all 16 binary assignments at five depth layouts,
-- with both equal and distinct filler values: 3,840 cases.
example : ∀ a b c d : Fin 2, ∀ perm : Equiv.Perm (Fin 4),
    ∀ fill : Fin 2,
    checkLayout positions17 (2 * fill.val) a b c d perm &&
    checkLayout positions18 (2 * fill.val) a b c d perm &&
    checkLayout (boundaryPositions 0) (2 * fill.val) a b c d perm &&
    checkLayout (boundaryPositions 1) (2 * fill.val) a b c d perm &&
    checkLayout (boundaryPositions 16) (2 * fill.val) a b c d perm = true := by
  native_decide

-- All 24 permutations of four slots drawn from two values. Every slot is within SWAP reach.
example : ∀ a b c d : Fin 2, ∀ perm : Equiv.Perm (Fin 4),
    check [.Var ⟨a.val⟩, .Var ⟨b.val⟩, .Var ⟨c.val⟩, .Var ⟨d.val⟩] perm = true := by
  native_decide

example : check [] 1 = true := by native_decide
example : check [.Var ⟨0⟩] 1 = true := by native_decide

end PermuteReachabilityTests
