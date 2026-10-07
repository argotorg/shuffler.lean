import Shuffler.Placement.Defs

namespace Shuffler.Optimality.ForcedIntroduction

open Shuffler.Placement

-- A retained DUP source needs a copy separate from the first output that
-- growth freezes. A missing copy forces at least one PUSH or LOAD.
def Required (value : Value) (source target : Stack) (missing : Multiset Value) : Prop :=
  value ∈ missing ∧ ¬boundary source target missing + {value} ≤ (window source : Multiset Value)

instance (value : Value) (source target : Stack) (missing : Multiset Value) :
    Decidable (Required value source target missing) := by
  unfold Required
  infer_instance

end Shuffler.Optimality.ForcedIntroduction
