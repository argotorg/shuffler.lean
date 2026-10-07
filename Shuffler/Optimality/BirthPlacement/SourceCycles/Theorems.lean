import Shuffler.Optimality.BirthPlacement.SourceCycles

namespace Shuffler.Optimality.BirthPlacement.SourceCycles

open Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

instance (position : ι) (pair : ι × ι) : Decidable (Avoids position pair) := by
  unfold Avoids
  infer_instance

def untouched (pairs : Finset (ι × ι)) (position : ι) : Finset (ι × ι) :=
  pairs.filter (Avoids position)

omit [Fintype ι] in
theorem untouched_eq_erase (permutation : Equiv.Perm ι) (pairs : Finset (ι × ι))
    (hcycles : ∀ pair ∈ pairs, IsPair permutation pair) (position : ι)
    (pair : ι × ι) (hpair : pair ∈ pairs)
    (htouch : position = pair.1 ∨ position = pair.2) :
    untouched pairs position = pairs.erase pair := by
  ext other
  simp only [untouched, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hm, ha⟩
    refine ⟨?_, hm⟩
    rintro rfl
    exact htouch.elim ha.1 ha.2
  · rintro ⟨hne, hm⟩
    refine ⟨hm, ?_, ?_⟩
    · intro he
      exact hne ((hcycles other hm).eq_of_shared (hcycles pair hpair) position (Or.inl he) htouch)
    · intro he
      exact hne ((hcycles other hm).eq_of_shared (hcycles pair hpair) position (Or.inr he) htouch)

omit [Fintype ι] in
theorem untouched_cycles (permutation : Equiv.Perm ι) (pairs : Finset (ι × ι))
    (hcycles : ∀ pair ∈ pairs, IsPair permutation pair) (top position : ι)
    (htop : ∀ pair ∈ pairs, Avoids top pair) :
    ∀ pair ∈ untouched pairs position, IsPair (permutation * Equiv.swap top position) pair := by
  intro pair hp
  obtain ⟨hm, ha⟩ := Finset.mem_filter.mp hp
  obtain ⟨horder, hfirst, hsecond⟩ := hcycles pair hm
  have ht := htop pair hm
  refine ⟨horder, ?_, ?_⟩
  · simpa only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ht.1) (Ne.symm ha.1)] using hfirst
  · simpa only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ht.2) (Ne.symm ha.2)] using hsecond

-- The statement concerns an explicit swap list. It does not assume or claim
-- a bridge from production source traces to the selected-pair hypotheses.
theorem selected_pairs_lower_bound (permutation : Equiv.Perm ι) (pairs : Finset (ι × ι))
    (hcycles : ∀ pair ∈ pairs, IsPair permutation pair) (swaps : List (ι × ι))
    (htops : ∀ step ∈ swaps, ∀ pair ∈ pairs, Avoids step.1 pair)
    (hfinish : permutation * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1) :
    arbitrarySwapCount permutation + 2 * pairs.card ≤ swaps.length := by
  induction swaps generalizing permutation pairs with
  | nil =>
    have hp : permutation = 1 := by simpa using hfinish
    subst permutation
    have he : pairs = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro pair hm
      obtain ⟨hlt, he, _⟩ := hcycles pair hm
      have he : pair.1 = pair.2 := he
      exact (ne_of_lt hlt) he
    simp [he]
  | cons step swaps ih =>
    let next := permutation * Equiv.swap step.1 step.2
    let remaining := untouched pairs step.2
    have htop : ∀ pair ∈ pairs, Avoids step.1 pair := htops step (by simp)
    have hr : arbitrarySwapCount next + 2 * remaining.card ≤ swaps.length := by
      apply ih next remaining (untouched_cycles permutation pairs hcycles step.1 step.2 htop)
      · intro other ho pair hp
        exact htops other (by simp [ho]) pair (Finset.mem_filter.mp hp).1
      · simpa only [next, List.map_cons, List.prod_cons, mul_assoc] using hfinish
    have hlocal : arbitrarySwapCount permutation + 2 * pairs.card ≤
        arbitrarySwapCount next + 2 * remaining.card + 1 := by
      by_cases hit : ∃ pair ∈ pairs, ¬Avoids step.2 pair
      · obtain ⟨pair, hp, hh⟩ := hit
        have ht := htop pair hp
        obtain ⟨hlt, hfirst, hsecond⟩ := hcycles pair hp
        have htouch : step.2 = pair.1 ∨ step.2 = pair.2 := by
          by_cases he : step.2 = pair.1
          · exact Or.inl he
          · exact Or.inr (by by_contra hn; exact hh ⟨he, hn⟩)
        have hc : remaining.card + 1 = pairs.card := by
          rw [show remaining = pairs.erase pair from
            untouched_eq_erase permutation pairs hcycles step.2 pair hp htouch]
          exact Finset.card_erase_add_one hp
        have hk : arbitrarySwapCount next = arbitrarySwapCount permutation + 1 := by
          rcases htouch with he | he
          · simpa only [next, he] using arbitrarySwapCount_touch_pair permutation step.1 pair.1 pair.2
              (ne_of_lt hlt) ht.1 ht.2 hfirst hsecond
          · simpa only [next, he] using arbitrarySwapCount_touch_pair permutation step.1 pair.2 pair.1
              (ne_of_gt hlt) ht.2 ht.1 hsecond hfirst
        omega
      · have he : remaining = pairs := by
          apply Finset.filter_eq_self.mpr
          intro pair hp
          by_contra hn
          exact hit ⟨pair, hp, hn⟩
        have hk := arbitrarySwapCount_le_mul_swap_add_one permutation step.1 step.2
        change arbitrarySwapCount permutation ≤ arbitrarySwapCount next + 1 at hk
        rw [he]
        omega
    simp only [List.length_cons]
    omega

end Shuffler.Optimality.BirthPlacement.SourceCycles
