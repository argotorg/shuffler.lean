import Shuffler.Optimality.BirthPlacement.SourceEntry.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceEntry

open Shuffler.Permute Shuffler.Permute.Permutation Shuffler.Placement

-- Run the existing permutation routine on the source domain only.
def build (plan : SourcePlan spills source target) : SourceEntry plan :=
  if hz : source.length = 0 then
    let built : BuiltTrace spills source source 0 := ⟨.Lit source, trivial, rfl⟩
    ⟨built.cast rfl (empty_values plan hz) rfl, by
      rw [built_cast_swapCount]
      simp only [built, Trace.swapCount, sourceEntryCost, dite_eq_left hz]⟩
  else
    let result := ValueGraph.permuteBuilt spills source
      (prefixValues target (SourcePrefix.run plan.assignment source.length).permutation
        source.length) (permutation plan)
    have hex : result.isSome := ValueGraph.permuteBuilt_complete _ _ _ _
      (permutation_reachable plan) (permutation_values plan)
    ⟨result.get hex, (ValueGraph.permuteBuilt_swapCount spills source _ (permutation plan)
      (by omega) (Option.some_get hex).symm).trans (permutation_swapCount plan hz)⟩

end Shuffler.Optimality.BirthPlacement.SourceEntry
