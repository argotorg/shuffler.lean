/-
`permute` as a function of the swap count `k`. The compiled code keeps `k` in a
register, so the loop invariants of the proof refer to `state p k` and `trace p k`
and need no existential.
-/
import PermuteKraken.Model

namespace PermuteKraken

def Step.isSwap : Step → Bool
  | .swap _ _ => true
  | _ => false

theorem lastMisplaced_zero (l : List Nat) : lastMisplaced l 0 = none := rfl

theorem lastMisplaced_succ (l : List Nat) (i : Nat) :
    lastMisplaced l (i + 1) = if l[i]! ≠ i then some i else lastMisplaced l i := by
  simp only [lastMisplaced, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

namespace Perm

-- The permutation after `k` swaps.
def state (p : Perm) : Nat → Perm
  | 0 => p
  | k + 1 => p.advance.state k

-- The depth of the next swap, or 0 if `step` gives no swap.
def depth (p : Perm) : Nat :=
  match step p.toList with
  | .swap idx _ => idx
  | _ => 0

-- The depths of the first `k` swaps.
def trace (p : Perm) : Nat → List Nat
  | 0 => []
  | k + 1 => p.depth :: p.advance.trace k

theorem state_succ (p : Perm) (k : Nat) : p.state (k + 1) = (p.state k).advance := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => exact ih p.advance

theorem trace_succ (p : Perm) (k : Nat) : p.trace (k + 1) = p.trace k ++ [(p.state k).depth] := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    show p.depth :: p.advance.trace (k + 1) = _
    rw [ih p.advance]
    rfl

theorem length_trace (p : Perm) (k : Nat) : (p.trace k).length = k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [trace, ih]

theorem length_advance (p : Perm) : p.advance.toList.length = p.toList.length := by
  unfold advance
  split
  · exact p.length_swap ..
  · rfl

theorem length_state (p : Perm) (k : Nat) : (p.state k).toList.length = p.toList.length := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => exact (ih p.advance).trans p.length_advance

theorem advance_eq (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    p.advance.toList = swapEntries p.toList (p.toList.length - 1) pos := by
  unfold advance
  split
  · rename_i h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i hn
    exact absurd h (hn _ _)

theorem depth_eq (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) : p.depth = idx := by
  simp [depth, h]

theorem steps_eq_succ (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    steps p = steps p.advance + 1 := by
  rw [steps]
  split
  · rfl
  · rename_i hn
    exact absurd h (hn _ _)

theorem steps_eq_zero (p : Perm) (h : (step p.toList).isSwap = false) : steps p = 0 := by
  rw [steps]
  split
  · rename_i h'
    simp [h', Step.isSwap] at h
  · rfl

theorem isSwap_iff {s : Step} : s.isSwap = true ↔ ∃ idx pos, s = .swap idx pos := by
  cases s <;> simp [Step.isSwap]

theorem step_state_lt (p : Perm) : ∀ k < (steps p), (step (p.state k).toList).isSwap = true := by
  intro k hk
  induction k generalizing p with
  | zero =>
    cases h : (step p.toList).isSwap
    · rw [p.steps_eq_zero h] at hk; omega
    · exact h
  | succ k ih =>
    cases h : (step p.toList).isSwap
    · rw [p.steps_eq_zero h] at hk; omega
    · obtain ⟨idx, pos, h⟩ := isSwap_iff.mp h
      rw [p.steps_eq_succ h] at hk
      exact ih p.advance (by omega)

theorem step_state_steps (p : Perm) : (step (p.state (steps p)).toList).isSwap = false := by
  induction p using PermuteKraken.steps.induct with
  | case1 p idx pos h ih =>
    rw [p.steps_eq_succ h]
    exact ih
  | case2 p hn =>
    have h : (step p.toList).isSwap = false := by
      cases h : step p.toList <;> simp_all [Step.isSwap]
    rw [p.steps_eq_zero h]
    exact h

theorem permute_eq (p : Perm) : permute p =
    match step (p.state (steps p)).toList with
    | .blocked b => .error b
    | _ => .ok (p.trace (steps p)) := by
  induction p using PermuteKraken.steps.induct with
  | case1 p idx pos h ih =>
    rw [permute, p.steps_eq_succ h]
    split
    · rename_i h'; rw [h] at h'; cases h'
    · rename_i h'; rw [h] at h'; cases h'
    · rename_i h'
      rw [h] at h'
      cases h'
      show _ = match step (p.advance.state (steps p.advance)).toList with
        | .blocked b => Except.error b
        | _ => .ok (p.depth :: p.advance.trace (steps p.advance))
      rw [ih, p.depth_eq h]
      split <;> rfl
  | case2 p hn =>
    have h : (step p.toList).isSwap = false := by
      cases h : step p.toList <;> simp_all [Step.isSwap]
    rw [permute, p.steps_eq_zero h]
    show _ = match step p.toList with
      | .blocked b => Except.error b
      | _ => .ok []
    split
    · rename_i h'; rw [h'] at h ⊢
    · rename_i h'; rw [h'] at h ⊢
    · rename_i h'; simp [h', Step.isSwap] at h

theorem measure_le (l : List Nat) : measure l ≤ 2 * (l.length - 1) + 1 := by
  have := List.countP_le_length (p := fun i => decide (l[i]! ≠ i)) (l := List.range (l.length - 1))
  simp only [List.length_range] at this
  unfold measure
  split <;> omega

theorem steps_le_measure (p : Perm) : steps p ≤ measure p.toList := by
  induction p using PermuteKraken.steps.induct with
  | case1 p idx pos h ih =>
    rw [p.steps_eq_succ h]
    have := p.measure_advance h
    omega
  | case2 p hn =>
    have h : (step p.toList).isSwap = false := by
      cases h : step p.toList <;> simp_all [Step.isSwap]
    rw [p.steps_eq_zero h]
    omega

theorem steps_lt (p : Perm) (h : 0 < p.toList.length) : steps p < 2 * p.toList.length := by
  have := p.steps_le_measure
  have := measure_le p.toList
  omega

theorem steps_zero (p : Perm) (h : p.toList.length = 0) : steps p = 0 := by
  apply p.steps_eq_zero
  simp [step, h, Step.isSwap]

end Perm

end PermuteKraken
