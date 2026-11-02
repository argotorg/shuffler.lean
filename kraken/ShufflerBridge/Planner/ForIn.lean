module

public import ShufflerBridge.Planner.Loops
import all ShufflerBridge.Planner.Loops
public import Shuffler.Contracts
import all Shuffler.Contracts

@[expose] public section

/-!
The loops of the flat model and the `for` loops of PR31 over `List.finRange n`.

A flat loop is a function `F` of the offset `k` and the state, that does one step `st` for each
`k < n` and stops at the first step that does not return `.done`. A PR31 loop is `forIn` of a
body `f` that does not `break`. If each step of `F` and `f` agree (`StepCorr`), then the loops
agree (`LoopCorr`). `fold_corr` is the same for loops without a status, whose body cannot fail.
-/

namespace ShufflerBridge.Planner

open Shuffler FlatShuffler.Flat

-- A flat step and a PR31 step: both go on with related states, or both fail.
def StepCorr {σ β ε : Type} (R : σ → β → Prop) : EmissionOutcome × σ → Except ε (ForInStep β) → Prop
  | (.done, s), .ok (.yield b) => R s b
  | (.assertionExit, _), .error _ => True
  | _, _ => False

-- A flat loop and a PR31 loop: both end with related states, or both fail.
def LoopCorr {σ β ε : Type} (R : σ → β → Prop) : EmissionOutcome × σ → Except ε β → Prop
  | (.done, s), .ok b => R s b
  | (.assertionExit, _), .error _ => True
  | _, _ => False

theorem finRange_drop {n k : Nat} (h : k < n) :
    (List.finRange n).drop k = ⟨k, h⟩ :: (List.finRange n).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem loop_corr {σ β ε : Type} {n : Nat} (_hn : n ≤ FlatShuffler.maxStackSize)
    (F st : FlatShuffler.Word → σ → EmissionOutcome × σ)
    (hF : ∀ k s, k ≤ n → F (.ofNat 64 k) s =
      if k < n then
        (if (st (.ofNat 64 k) s).1 ≠ .done then st (.ofNat 64 k) s
         else F (.ofNat 64 (k + 1)) (st (.ofNat 64 k) s).2)
      else (.done, s))
    (R : σ → β → Prop) (f : Fin n → β → Except ε (ForInStep β))
    (hstep : ∀ k (h : k < n) s b, R s b → StepCorr R (st (.ofNat 64 k) s) (f ⟨k, h⟩ b))
    (s : σ) (b : β) (hR : R s b) : LoopCorr R (F 0 s) (forIn (List.finRange n) b f) := by
  suffices h : ∀ j k s b, k + j = n → R s b →
      LoopCorr R (F (.ofNat 64 k) s) (forIn ((List.finRange n).drop k) b f) by
    simpa using h n 0 s b (by omega) hR
  intro j
  induction j with
  | zero =>
    intro k s b hk hR
    rw [hF k s (by omega), ite_eq_right (by omega), List.drop_of_length_le (by simp; omega)]
    exact hR
  | succ j ih =>
    intro k s b hk hR
    rw [hF k s (by omega), ite_eq_left (by omega), finRange_drop (by omega), List.forIn_cons]
    have hs := hstep k (by omega) s b hR
    revert hs
    generalize st (.ofNat 64 k) s = r
    generalize f ⟨k, by omega⟩ b = x
    rcases r with ⟨(⟨_ | _⟩ | _), s'⟩ <;> rcases x with _ | (b' | b') <;>
      simp [StepCorr, LoopCorr, Bind.bind, Except.bind]
    exact ih (k + 1) s' b' (by omega)

theorem fold_corr {σ β ε : Type} {n : Nat} (_hn : n ≤ FlatShuffler.maxStackSize)
    (F : FlatShuffler.Word → σ → σ) (g : FlatShuffler.Word → σ → σ)
    (hF : ∀ k s, k ≤ n → F (.ofNat 64 k) s =
      if k < n then F (.ofNat 64 (k + 1)) (g (.ofNat 64 k) s) else s)
    (R : σ → β → Prop) (f : Fin n → β → Except ε (ForInStep β))
    (hstep : ∀ k (h : k < n) s b, R s b →
      ∃ b', f ⟨k, h⟩ b = .ok (.yield b') ∧ R (g (.ofNat 64 k) s) b')
    (s : σ) (b : β) (hR : R s b) :
    ∃ b', forIn (List.finRange n) b f = .ok b' ∧ R (F 0 s) b' := by
  suffices h : ∀ j k s b, k + j = n → R s b →
      ∃ b', forIn ((List.finRange n).drop k) b f = .ok b' ∧ R (F (.ofNat 64 k) s) b' by
    simpa using h n 0 s b (by omega) hR
  intro j
  induction j with
  | zero =>
    intro k s b hk hR
    rw [hF k s (by omega), ite_eq_right (by omega), List.drop_of_length_le (by simp; omega)]
    exact ⟨b, rfl, hR⟩
  | succ j ih =>
    intro k s b hk hR
    rw [hF k s (by omega), ite_eq_left (by omega), finRange_drop (by omega), List.forIn_cons]
    obtain ⟨b', hb, hR'⟩ := hstep k (by omega) s b hR
    rw [hb]
    exact ih (k + 1) _ b' (by omega) hR'

end ShufflerBridge.Planner
