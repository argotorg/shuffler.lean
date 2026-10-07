import Shuffler.Optimality.Cost
import Shuffler.Permute.Defs

namespace Shuffler.Optimality

-- With no POP and no additions, every instruction is a SWAP. Record its
-- absolute position in a fixed Fin type. The product maps the final stack
-- back to the source because products compose right to left.
theorem noGrowth_swaps (trace : Trace spills source target)
    (hpop : trace.noPop) (hadd : trace.additions = 0) (hne : 0 < source.length) :
    ∃ (hlen : target.length = source.length) (swaps : List (Fin source.length)),
      trace.swapCount = swaps.length ∧
      Shuffler.Permute.apply_permutation' target
        (swaps.map (Equiv.swap ⟨source.length - 1, by omega⟩)).prod hlen = source := by
  induction trace with
  | Lit =>
      exact ⟨rfl, [], rfl, Shuffler.Permute.apply_permutation'_one source rfl⟩
  | @Swap previous depth hdepth hlo hhi trace ih =>
      obtain ⟨hlen, swaps, hc, hp⟩ := ih hpop hadd
      let top : Fin source.length := ⟨source.length - 1, by omega⟩
      let position : Fin source.length := ⟨previous.length - 1 - depth, by omega⟩
      refine ⟨by simpa using hlen, swaps ++ [position], ?_, ?_⟩
      · simp only [Trace.swapCount, List.length_append, List.length_singleton, hc]
      · have hs : previous.swap (previous.length - 1) (previous.length - 1 - depth) =
            previous.swap top.val position.val := by
          dsimp [top, position]
          rw [hlen]
        have he := Shuffler.Permute.apply_permutation'_swap previous
          (swaps.map (Equiv.swap top)).prod hlen top position
        simpa only [List.map_append, List.map_singleton, List.prod_append,
          List.prod_singleton, hs] using he.trans hp
  | @Dup previous index hlen hlo hhi trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega
  | Pop _ trace ih => exact False.elim hpop
  | Push value hfree trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega
  | Load id hspill trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega

theorem noGrowth_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hadd : trace.additions = 0) :
    (traceCost costs trace).score weights = trace.swapCount * costs.swap.score weights := by
  induction trace with
  | Lit => simp [traceCost, Trace.swapCount]
  | Swap depth hlen hlo hhi trace ih =>
      simp only [traceCost, Cost.score_add, ih hpop hadd, Trace.swapCount, Nat.add_mul, Nat.one_mul]
  | Dup index hlen hlo hhi trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega
  | Pop _ trace ih => exact False.elim hpop
  | Push value hfree trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega
  | Load id hspill trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
      omega

end Shuffler.Optimality
