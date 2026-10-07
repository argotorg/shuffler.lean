import Shuffler.Optimality.BirthPlacement.SourcePrefix
import Shuffler.Optimality.BirthPlacement.Schedule.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourcePrefix

open Equiv.Perm Shuffler.Permute.Permutation

variable {size : Nat} {assignment first second : Equiv.Perm (Fin size)}

theorem WithinCycles.one (assignment : Equiv.Perm (Fin size)) : WithinCycles assignment 1 :=
  fun _ => SameCycle.rfl

theorem WithinCycles.self (assignment : Equiv.Perm (Fin size)) : WithinCycles assignment assignment :=
  fun _ => SameCycle.rfl.apply_right

theorem WithinCycles.mul (hfirst : WithinCycles assignment first)
    (hsecond : WithinCycles assignment second) : WithinCycles assignment (first * second) :=
  fun index => (hsecond index).trans (hfirst (second index))

theorem WithinCycles.swap {left right : Fin size} (h : assignment.SameCycle left right) :
    WithinCycles assignment (Equiv.swap left right) := by
  intro index
  by_cases hl : index = left
  · subst index
    simpa only [Equiv.swap_apply_left] using h
  · by_cases hr : index = right
    · subst index
      simpa only [Equiv.swap_apply_right] using h.symm
    · simpa only [Equiv.swap_apply_of_ne_of_ne hl hr] using
        (SameCycle.rfl : assignment.SameCycle index index)

theorem WithinCycles.of_swaps (assignment : Equiv.Perm (Fin size))
    (swaps : List (Fin size × Fin size))
    (h : ∀ pair ∈ swaps, assignment.SameCycle pair.1 pair.2) :
    WithinCycles assignment (swaps.map fun pair => Equiv.swap pair.1 pair.2).prod := by
  induction swaps with
  | nil => exact WithinCycles.one assignment
  | cons pair rest ih =>
      exact (WithinCycles.swap (h pair (List.mem_cons_self))).mul
        (ih (fun other ho => h other (List.mem_cons_of_mem _ ho)))

theorem WithinCycles.sameCycle (h : WithinCycles assignment first)
    {left right : Fin size} (hs : first.SameCycle left right) : assignment.SameCycle left right := by
  obtain ⟨power, rfl⟩ := hs.exists_nat_pow_eq
  clear hs
  induction power with
  | zero => exact SameCycle.rfl
  | succ power ih =>
      rw [pow_succ', mul_apply]
      exact ih.trans (h _)

theorem settleTop_within (state : Equiv.Perm (Fin size)) (top : Fin size)
    (hwithin : WithinCycles assignment state) :
    WithinCycles assignment (settleTop state top).permutation ∧
      ∀ pair ∈ (settleTop state top).swaps, assignment.SameCycle pair.1 pair.2 := by
  induction hn : arbitrarySwapCount state using Nat.strong_induction_on generalizing state with
  | h count ih =>
      rw [settleTop]
      split_ifs with hback
      · let next := state * Equiv.swap top (state top)
        have hdrop : arbitrarySwapCount next + 1 = arbitrarySwapCount state :=
          arbitrarySwapCount_place_top state top (ne_of_lt hback)
        obtain ⟨hs, hp⟩ := ih (arbitrarySwapCount next) (by omega) next
          (hwithin.mul (WithinCycles.swap (hwithin top))) rfl
        refine ⟨hs, ?_⟩
        intro pair hm
        rcases List.mem_cons.mp hm with he | hm
        · subst pair
          exact hwithin top
        · exact hp pair hm
      · exact ⟨hwithin, by simp⟩

theorem run_within (assignment : Equiv.Perm (Fin size)) (height : Nat) :
    WithinCycles assignment (run assignment height).permutation ∧
      ∀ pair ∈ (run assignment height).swaps, assignment.SameCycle pair.1 pair.2 := by
  induction height with
  | zero => exact ⟨WithinCycles.self assignment, by simp [run]⟩
  | succ height ih =>
      simp only [run]
      split_ifs with hheight
      · obtain ⟨hs, hp⟩ := settleTop_within (run assignment height).permutation ⟨height, hheight⟩ ih.1
        refine ⟨hs, ?_⟩
        intro pair hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ih.2 pair hm
        · exact hp pair hm
      · exact ih

theorem permutation_within (assignment : Equiv.Perm (Fin size)) (height : Nat) :
    WithinCycles assignment (permutation assignment height) :=
  WithinCycles.of_swaps assignment _ (run_within assignment height).2

theorem prefix_sameCycle (assignment : Equiv.Perm (Fin size)) (height : Nat)
    {left right : Fin size} (h : (permutation assignment height).SameCycle left right) :
    assignment.SameCycle left right :=
  (permutation_within assignment height).sameCycle h

theorem run_spec (assignment : Equiv.Perm (Fin size)) (height : Nat) (hh : height ≤ size) :
    ForwardBefore (run assignment height).permutation height ∧
    (∀ index : Fin size, height ≤ index.val →
      (run assignment height).permutation index = assignment index) ∧
    arbitrarySwapCount (run assignment height).permutation +
      (run assignment height).swaps.length = arbitrarySwapCount assignment ∧
    assignment * permutation assignment height = (run assignment height).permutation ∧
    (∀ pair ∈ (run assignment height).swaps,
      pair.2 < pair.1 ∧ pair.1.val < height) := by
  induction height with
  | zero => simp [run, permutation, ForwardBefore]
  | succ height ih =>
      have hlt : height < size := by omega
      obtain ⟨hf, ho, hc, hp, hr⟩ := ih (by omega)
      have hd : BirthDeadlines size (run assignment height).permutation :=
        fun index => by have := index.isLt; omega
      obtain ⟨hf', _, ho', hc', hp', hr'⟩ :=
        settleTop_spec (run assignment height).permutation ⟨height, hlt⟩ hf hd
      simp only [run, dite_eq_left hlt]
      refine ⟨hf', ?_, ?_, ?_, ?_⟩
      · intro index hi
        exact (ho' index (show height < index.val by omega)).trans (ho index (by omega))
      · simp only [List.length_append]
        omega
      · simp only [permutation, run, dite_eq_left hlt, List.map_append, List.prod_append,
          ← mul_assoc]
        exact (congrArg (fun p => p * ((settleTop (run assignment height).permutation
          ⟨height, hlt⟩).swaps.map fun pair => Equiv.swap pair.1 pair.2).prod) hp).trans hp'
      · intro pair hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ⟨(hr pair hm).1, by have := (hr pair hm).2; omega⟩
        · obtain ⟨he, hb, _⟩ := hr' pair hm
          exact ⟨by simpa only [he] using hb, by simp [he]⟩

theorem permutation_fixed_above (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (index : Fin size) (hi : height ≤ index.val) :
    permutation assignment height index = index := by
  obtain ⟨_, ho, _, hp, _⟩ := run_spec assignment height hh
  apply assignment.injective
  exact (congrArg (fun p => p index) hp).trans (ho index hi)

theorem WithinCycles.symm (h : WithinCycles assignment first) :
    WithinCycles assignment first.symm := by
  intro index
  simpa only [Equiv.apply_symm_apply] using (h (first.symm index)).symm

theorem WithinCycles.closed_fixed (hwithin : WithinCycles assignment first)
    (hforward : ForwardBefore first height) (index : Fin size)
    (hclosed : ∀ other, assignment.SameCycle index other → other.val < height) :
    first index = index := by
  induction hn : index.val using Nat.strong_induction_on generalizing index with
  | h value ih =>
      let earlier := first.symm index
      have he : first earlier = index := first.apply_symm_apply index
      have hs : assignment.SameCycle index earlier := hwithin.symm index
      have hf : earlier ≤ index := by
        simpa only [he] using hforward earlier (hclosed earlier hs)
      by_cases heq : earlier = index
      · simpa only [heq] using he
      · have hlt : earlier.val < index.val := by
          have hne := Fin.val_ne_of_ne heq
          omega
        have hfixed := ih earlier.val (by omega) earlier
          (fun other ho => hclosed other (hs.trans ho)) rfl
        exact False.elim (heq (hfixed.symm.trans he))

theorem run_closed_fixed (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (index : Fin size)
    (hclosed : ∀ other, assignment.SameCycle index other → other.val < height) :
    (run assignment height).permutation index = index :=
  (run_within assignment height).1.closed_fixed (run_spec assignment height hh).1 index hclosed

theorem permutation_closed (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (index : Fin size)
    (hclosed : ∀ other, assignment.SameCycle index other → other.val < height) :
    permutation assignment height index = assignment.symm index := by
  apply assignment.injective
  rw [Equiv.apply_symm_apply]
  exact (congrArg (fun p => p index) (run_spec assignment height hh).2.2.2.1).trans
    (run_closed_fixed assignment height hh index hclosed)

end Shuffler.Optimality.BirthPlacement.SourcePrefix
