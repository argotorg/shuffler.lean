import Shuffler.Optimality.BirthPlacement.SourceLazy.State
import Shuffler.Optimality.BirthPlacement.SourceLazy.Prefix
import Shuffler.Optimality.BirthPlacement.SourceLazy.Count

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Shuffler.Placement

variable {spills : SpillSet} {source target : Stack}
  {plan : SourcePlan spills source target}

def base (state : State plan source.length) : Result plan source.length state := by
  by_cases hz : source.length = 0
  · have he : state.remaining = 1 := by
      apply Equiv.ext
      intro index
      exact state.above index (by omega)
    have hs : source = [] := List.length_eq_zero_iff.mp hz
    have ht : state.values = source := by simp [State.values, prefixValues, hs]
    let built : BuiltTrace spills source source 0 := ⟨.Lit source, trivial, rfl⟩
    refine ⟨built.cast rfl ht.symm (by simp), ?_, ?_⟩
    · rw [built_cast_swapCount]
      simp [built, Trace.swapCount, swapBound, he, forcedCycles]
    · rw [built_cast_events]
      simp [built, traceEvents]
  · let result := permutePrefix spills target source plan.assignment state.remaining
      plan.source_length plan.source_values.symm state.above
      (by
        intro index hi
        by_contra hn
        exact (Equiv.Perm.mem_support.mp hi) (state.source_frozen index (by omega)))
      (by omega)
    refine ⟨result.val.cast rfl rfl (by simp), ?_, ?_⟩
    · rw [built_cast_swapCount, result.property]
      exact (swapBound_at_source state.remaining source.length (by omega)
        plan.source_length state.above).symm
    · rw [built_cast_events, traceEvents_empty result.val.trace result.val.additions]
      simp

end Shuffler.Optimality.BirthPlacement.SourceLazy
