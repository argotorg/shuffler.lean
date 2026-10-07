import Shuffler.Optimality.BirthPlacement.SourceLazy.Spec

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cycle_mem_mul_swap_iff (permutation cycle : Equiv.Perm ι) (top lower : ι)
    (htop : top ∉ cycle.support) (hlower : lower ∉ cycle.support) :
    cycle ∈ (permutation * Equiv.swap top lower).cycleFactorsFinset ↔
      cycle ∈ permutation.cycleFactorsFinset := by
  have hswap (index : ι) (hi : index ∈ cycle.support) : Equiv.swap top lower index = index := by
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl
      exact htop hi
    · rintro rfl
      exact hlower hi
  simp only [Equiv.Perm.mem_cycleFactorsFinset_iff, Equiv.Perm.mul_apply]
  constructor <;> rintro ⟨hc, he⟩ <;>
    exact ⟨hc, fun index hi => by simpa only [hswap index hi] using he index hi⟩

-- A SWAP from outside a nontrivial cycle into that cycle increases rank.
theorem arbitrarySwapCount_touch_cycle (permutation cycle : Equiv.Perm ι) (top lower : ι)
    (hcycle : cycle ∈ permutation.cycleFactorsFinset)
    (htop : top ∉ cycle.support) (hlower : lower ∈ cycle.support) :
    arbitrarySwapCount (permutation * Equiv.swap top lower) =
      arbitrarySwapCount permutation + 1 := by
  induction hn : arbitrarySwapCount permutation using Nat.strong_induction_on generalizing permutation with
  | h count ih =>
    have hne : top ≠ lower := by rintro rfl; exact htop hlower
    by_cases hfixed : permutation top = top
    · have hq : (permutation * Equiv.swap top lower) lower = top := by simp [hfixed]
      have hr := arbitrarySwapCount_place_top (permutation * Equiv.swap top lower) lower
        (by rw [hq]; exact hne)
      rw [hq, Equiv.swap_comm lower top, mul_assoc, Equiv.swap_mul_self, mul_one] at hr
      simpa only [hn] using hr.symm
    · let next := permutation * Equiv.swap top (permutation top)
      have hr := arbitrarySwapCount_place_top permutation top hfixed
      have hpt : permutation top ∉ cycle.support := by
        exact fun hm => htop ((Equiv.Perm.mem_cycleFactorsFinset_support hcycle top).mp hm)
      have hc : cycle ∈ next.cycleFactorsFinset :=
        (cycle_mem_mul_swap_iff permutation cycle top (permutation top) htop hpt).mpr hcycle
      have hrec := ih (arbitrarySwapCount next) (by dsimp only [next]; omega)
        next hc rfl
      have hpl : permutation top ≠ lower := by rintro he; exact hpt (he.symm ▸ hlower)
      have hq : (permutation * Equiv.swap top lower) lower = permutation top := by simp
      have hqr := arbitrarySwapCount_place_top (permutation * Equiv.swap top lower) lower
        (by rw [hq]; exact hpl)
      rw [hq] at hqr
      have he : permutation * Equiv.swap top lower * Equiv.swap lower (permutation top) =
          next * Equiv.swap top lower := by
        apply Equiv.ext
        intro index
        by_cases hit : index = top
        · subst index
          simp [next, Equiv.swap_apply_def, hne, Ne.symm hfixed, Ne.symm hne, Ne.symm hpl]
        by_cases hil : index = lower
        · subst index
          simp [next, Equiv.swap_apply_def, hfixed, hpl]
        by_cases hip : index = permutation top
        · subst index
          simp [next, Equiv.swap_apply_def, hfixed, hpl]
        · simp [next, Equiv.swap_apply_of_ne_of_ne hit hil,
            Equiv.swap_apply_of_ne_of_ne hit hip,
            Equiv.swap_apply_of_ne_of_ne hil hip]
      rw [he] at hqr
      dsimp only [next] at hrec hqr
      omega

def untouchedCycles (cycles : Finset (Equiv.Perm ι)) (position : ι) :
    Finset (Equiv.Perm ι) :=
  cycles.filter fun cycle => position ∉ cycle.support

theorem untouchedCycles_eq_erase (permutation : Equiv.Perm ι)
    (cycles : Finset (Equiv.Perm ι)) (hcycles : cycles ⊆ permutation.cycleFactorsFinset)
    (position : ι) (cycle : Equiv.Perm ι) (hc : cycle ∈ cycles)
    (hp : position ∈ cycle.support) :
    untouchedCycles cycles position = cycles.erase cycle := by
  have he := Equiv.Perm.cycle_is_cycleOf hp (hcycles hc)
  ext other
  simp only [untouchedCycles, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hm, ha⟩
    refine ⟨?_, hm⟩
    rintro rfl
    exact ha hp
  · rintro ⟨hne, hm⟩
    refine ⟨hm, ?_⟩
    intro ht
    exact hne ((Equiv.Perm.cycle_is_cycleOf ht (hcycles hm)).trans he.symm)

theorem untouchedCycles_subset (permutation : Equiv.Perm ι)
    (cycles : Finset (Equiv.Perm ι)) (hcycles : cycles ⊆ permutation.cycleFactorsFinset)
    (top lower : ι) (htop : ∀ cycle ∈ cycles, top ∉ cycle.support) :
    untouchedCycles cycles lower ⊆ (permutation * Equiv.swap top lower).cycleFactorsFinset := by
  intro cycle hc
  obtain ⟨hm, ha⟩ := Finset.mem_filter.mp hc
  exact (cycle_mem_mul_swap_iff permutation cycle top lower (htop cycle hm) ha).mpr (hcycles hm)

omit [Fintype ι] in
theorem swapProduct_fixes (swaps : List (ι × ι)) (position : ι)
    (havoid : ∀ step ∈ swaps, position ≠ step.1 ∧ position ≠ step.2) :
    ((swaps.map fun step => Equiv.swap step.1 step.2).prod) position = position := by
  induction swaps with
  | nil => rfl
  | cons step swaps ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ih (fun other ho => havoid other (List.mem_cons_of_mem _ ho))]
    exact Equiv.swap_apply_of_ne_of_ne (havoid step (by simp)).1 (havoid step (by simp)).2

-- If a forced cycle has remained intact, the next top cannot be in it.
-- Otherwise its old witness is already below every remaining SWAP window.
theorem forced_top_outside (permutation cycle : Equiv.Perm (Fin size)) (reach height : Nat)
    (hcycle : cycle ∈ permutation.cycleFactorsFinset) (hforced : Forced reach height cycle)
    (top : Fin size) (hheight : height - 1 ≤ top.val)
    (swaps : List (Fin size × Fin size))
    (hmin : ∀ step ∈ swaps, top.val ≤ step.1.val)
    (hreach : ∀ step ∈ swaps, step.1.val ≤ step.2.val + reach)
    (hfinish : permutation * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1) :
    top ∉ cycle.support := by
  intro ht
  obtain ⟨hexclude, before, hb, hbefore, hfuture⟩ := hforced
  have hnot := hexclude top ht
  have htop : height ≤ top.val := by omega
  have hlate := hfuture top ht htop
  have hfixed := swapProduct_fixes swaps before (by
    intro step hs
    have hm := hmin step hs
    have hr := hreach step hs
    constructor <;> intro he <;> have hev := congrArg Fin.val he <;> omega)
  have he := congrArg (fun p : Equiv.Perm (Fin size) => p before) hfinish
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hfixed] at he
  exact Equiv.Perm.mem_support.mp hb
    (((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2 before hb).trans he)

end Shuffler.Optimality.BirthPlacement.SourceLazy
