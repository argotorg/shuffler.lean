import Shuffler.Optimality.BirthPlacement.SourceEntry.Restriction
import Shuffler.Optimality.BirthPlacement.SourcePlan

namespace Shuffler.Optimality.BirthPlacement.SourceEntry

open Shuffler.Permute Shuffler.Permute.Permutation Shuffler.Placement

def permutation (plan : SourcePlan spills source target) : Equiv.Perm (Fin source.length) :=
  (restrict (SourcePrefix.permutation plan.assignment source.length) plan.source_length
    (SourcePrefix.permutation_fixed_above plan.assignment source.length plan.source_length)).symm


end Shuffler.Optimality.BirthPlacement.SourceEntry
