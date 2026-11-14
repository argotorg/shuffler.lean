module

public import Shuffler.Permute.Defs
import Mathlib.Data.List.Nodup
import Shuffler.Emission.Lemmas

@[expose] public section

namespace Shuffler.Permute

open Emission

-- The permutation that `permute` hands to `go`.
abbrev normalize (stack : Stack) (perm : Permutation stack) : Permutation stack :=
  permute.minimizeCyclesWithoutTop stack (permute.minimizePermutationSupport stack perm 0)

def Assigns {n : ℕ} (value expected : Fin n → Value) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, value i = expected (p i)

-- Exchanging the destinations of two equal slots keeps every slot bound to an offset expecting its value.
theorem Assigns.mul_swap {n : ℕ} {value expected : Fin n → Value} {p : Equiv.Perm (Fin n)}
    (h : Assigns value expected p) (a b : Fin n) (hab : value a = value b) :
    Assigns value expected (p * Equiv.swap a b) := by
  intro i
  have hv : value (Equiv.swap a b i) = value i := by
    by_cases ha : i = a
    · subst i; simpa using hab.symm
    by_cases hb : i = b
    · subst i; simpa using hab
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  simpa [hv] using h (Equiv.swap a b i)

-- The first loop of `normalize`: once every slot before `position` stays or sends its value to an offset that
-- does not already hold it, every slot holding its expected value ends fixed.
theorem minimizePermutationSupport_spec (stack : Stack) (expected : Fin stack.length → Value) (p : Permutation stack)
    (position : ℕ) (hp : Assigns (fun i => stack[i]) expected p)
    (hvisited : ∀ i : Fin stack.length, i.val < position → p i = i ∨ stack[p i] ≠ stack[i]) :
    Assigns (fun i => stack[i]) expected (permute.minimizePermutationSupport stack p position) ∧
      ∀ i, stack[i] = expected i → permute.minimizePermutationSupport stack p position i = i := by
  fun_induction permute.minimizePermutationSupport stack p position with
  | case1 p position h destination hd ih =>
    refine ih (hp.mul_swap _ _ (by simpa using hd.2)) fun i hi => ?_
    by_cases hid : i = destination
    · left
      simp [hid, destination]
    · have hip : i ≠ ⟨position, h⟩ := by rintro rfl; exact absurd hi (lt_irrefl _)
      have heq : (p * Equiv.swap destination ⟨position, h⟩) i = p i := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hid hip]
      simpa only [heq] using hvisited i hi
  | case2 p position h destination hd ih =>
    refine ih hp fun i hi => ?_
    by_cases hip : i.val < position
    · exact hvisited i hip
    · obtain rfl : i = ⟨position, h⟩ := Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hip))
      by_cases he : destination = ⟨position, h⟩
      · exact Or.inl he
      · exact Or.inr fun hs => hd ⟨he, by simpa using hs⟩
  | case3 p position h =>
    refine ⟨hp, fun i he => ?_⟩
    have hs : stack[p.symm i] = expected i := by simpa using hp (p.symm i)
    have hlt := (p.symm i).isLt
    rcases hvisited (p.symm i) (by omega) with hf | hne
    · have hfix : p.symm i = i := by simpa using hf.symm
      simpa using (congrArg p hfix).symm
    · exact absurd (hs.trans he.symm).symm (by simpa using hne)

-- A property that every step of a loop keeps, including a step that breaks out of it, holds when the loop ends.
theorem forIn_invariant {α β : Type} (xs : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P init) (hf : ∀ a b, P b → P (f a b).run.value) :
    P (forIn xs init f).run := by
  induction xs generalizing init with
  | nil => exact h0
  | cons a xs ih =>
    have h := hf a init h0
    simp only [List.forIn_cons, Id.run_bind]
    cases hs : (f a init).run with
    | done b => rw [hs] at h; exact h
    | yield b => rw [hs] at h; exact ih b h

-- The second loop of `normalize` exchanges destinations only between equal slots, and never between a slot below
-- the top that stays in place and another one.
theorem minimizeCyclesWithoutTop_spec (stack : Stack) (expected : Fin stack.length → Value) (p : Permutation stack)
    (hp : Assigns (fun i => stack[i]) expected p) :
    Assigns (fun i => stack[i]) expected (permute.minimizeCyclesWithoutTop stack p) ∧
      ∀ i, i.val + 1 ≠ stack.length → p i = i → permute.minimizeCyclesWithoutTop stack p i = i := by
  unfold permute.minimizeCyclesWithoutTop
  simp only [bind_pure]
  apply forIn_invariant (P := fun q =>
    Assigns (fun i => stack[i]) expected q ∧ ∀ i, i.val + 1 ≠ stack.length → p i = i → q i = i)
  · exact ⟨hp, fun _ _ hi => hi⟩
  · intro a r hr
    split
    · rename_i ha
      simp only [Id.run_bind, Id.run_pure, ForInStep.value]
      apply forIn_invariant (P := fun q =>
        Assigns (fun i => stack[i]) expected q ∧ ∀ i, i.val + 1 ≠ stack.length → p i = i → q i = i)
      · exact hr
      · intro b s hs
        split
        · rename_i hc
          split
          · simp only [Id.run_pure, ForInStep.value]
            refine ⟨hs.1.mul_swap a b hc.1, fun i ht hi => ?_⟩
            have hia : i ≠ a := by rintro rfl; exact ha (hr.2 i ht hi)
            have hib : i ≠ b := by
              rintro rfl
              have := i.isLt
              exact hc.2.elim (fun hb => hb (hs.2 i ht hi)) (fun hb => ht (by omega))
            rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hib, hs.2 i ht hi]
          · exact hs
        · exact hs
    · exact hr

theorem normalize_assigns (stack : Stack) (p : Permutation stack)
    (expected : Fin stack.length → Value) (hp : Assigns (fun i => stack[i]) expected p) :
    Assigns (fun i => stack[i]) expected (normalize stack p) ∧
      (∀ i, i.val + 1 ≠ stack.length → stack[i] = expected i → normalize stack p i = i) := by
  obtain ⟨hfa, hff⟩ := minimizePermutationSupport_spec stack expected p 0 hp (fun _ hi => absurd hi (Nat.not_lt_zero _))
  obtain ⟨hma, hmf⟩ := minimizeCyclesWithoutTop_spec stack expected _ hfa
  exact ⟨hma, fun i hi he => hmf i hi (hff i he)⟩

theorem all_swaps_reachable.values {stack : Stack} {p : Permutation stack}
    (h : all_swaps_reachable p) : values_reachable p := by
  intro i hne
  apply h i
  apply Equiv.Perm.mem_support.mpr
  intro hfix
  apply hne
  have hi : p.symm i = i := by
    apply p.injective
    simpa using hfix.symm
  simp only [hi]

-- Only the top can move without being moved by `p`: it joins a cycle that holds its value.
theorem normalize_spec (stack : Stack) (p : Permutation stack) :
    apply_permutation stack (normalize stack p) = apply_permutation stack p ∧
      (∀ i ∈ (normalize stack p).support, i ∈ p.support ∨ i.val + 1 = stack.length) ∧
      (all_swaps_reachable (normalize stack p) ↔ values_reachable p) := by
  obtain ⟨ha, hc⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  generalize normalize stack p = q at *
  refine ⟨?_, ?_, ?_⟩
  · apply congrArg List.ofFn
    funext i
    simpa using ha (q.symm i)
  · intro i hi
    by_cases ht : i.val + 1 = stack.length
    · exact Or.inr ht
    · refine Or.inl (Equiv.Perm.mem_support.mpr fun hfix => Equiv.Perm.mem_support.mp hi (hc i ht ?_))
      have hs : p.symm i = i := by simpa using (congrArg p.symm hfix).symm
      simp only [hs]
  · constructor
    · intro hr i hne
      apply hr i
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      exact hne (by simpa [hfix] using ha i)
    · intro hr i hi
      by_cases he : stack[i] = stack[p.symm i]
      · by_cases ht : i.val + 1 = stack.length
        · simp only [Stack.isSwapReachable]; omega
        · exact ((Equiv.Perm.mem_support.mp hi) (hc i ht he)).elim
      · exact hr i he

theorem normalize_of_nodup (stack : Stack) (p : Permutation stack) (hn : stack.Nodup) :
    normalize stack p = p := by
  obtain ⟨ha, _⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  generalize normalize stack p = q at *
  have hsymm : q.symm = p.symm := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact hn.getElem_inj_iff.mp (by simpa using ha (q.symm i))
  simpa using congrArg Equiv.symm hsymm

theorem values_reachable_congr {stack : Stack} (p q : Permutation stack)
    (he : apply_permutation stack p = apply_permutation stack q) :
    values_reachable p ↔ values_reachable q := by
  have hv (i : Fin stack.length) : stack[p.symm i] = stack[q.symm i] := by
    simpa [apply_permutation] using congrArg (fun xs => xs[i.val]?) he
  simp only [values_reachable, hv]

theorem values_reachable_iff_deep (stack : Stack) (p : Permutation stack) :
    values_reachable p ↔ ∀ i, i < stack.length - (MAX_SWAP_DEPTH + 1) →
      stack[i]? = (apply_permutation stack p)[i]? := by
  constructor
  · intro hr i hi
    have hin : i < stack.length := by omega
    have he : stack[i] = stack[p.symm ⟨i, hin⟩] := by
      by_contra hne
      have hd := hr ⟨i, hin⟩ hne
      simp only [Stack.isSwapReachable] at hd
      omega
    simpa [apply_permutation, hin] using he
  · intro hr i hne
    by_contra hd
    have hi : i.val < stack.length - (MAX_SWAP_DEPTH + 1) := by
      simp only [Stack.isSwapReachable] at hd
      omega
    apply hne
    simpa [apply_permutation, i.isLt] using hr i.val hi

end Shuffler.Permute
