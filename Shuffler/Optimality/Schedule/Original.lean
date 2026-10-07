import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildMapping
import Shuffler.Optimality.Replay

namespace Shuffler.Optimality.Schedule

-- Run the original mapping builder and BBU without changing either one.
-- The checked replay rejects failed runs, a different concrete target,
-- different additions, and any POP in the operation list.
def originalState (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    State source target spills :=
  let mapping := (MappingBuilder.buildMapping source target
    (List.replicate source.length 0) .Leave (by simp)).mapping
  {
    planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := missing.card
  }

def originalCandidate (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (Shuffler.Placement.BuiltTrace spills source target missing) := do
  let result ← (Shuffler.BuildBottomUp.buildBottomUp
    (originalState spills source target missing)).toOption
  replayExact spills source target missing (flatten result.2)

end Shuffler.Optimality.Schedule
