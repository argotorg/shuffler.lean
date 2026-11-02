module

public import FlatShuffler.BinHost
import all FlatShuffler.BinHost

@[expose] public section

namespace FlatShuffler

-- An unresolved address cannot satisfy the exit contract.
example [Host] (unresolved : label "exit" = -1) : ¬ ExitBoundary := by
  intro boundary
  exact boundary.resolved unresolved

-- A host without an exit label cannot satisfy the exit contract.
example [Host] (missingExit : "exit" ∉ Program.labels Host.prog) : ¬ ExitBoundary := by
  intro boundary
  rcases Host.label_cases "exit" with unresolved | ⟨offset, atExit, _⟩
  · exact boundary.resolved unresolved
  · exact missingExit (Program.mem_labels.mpr (List.mem_of_getElem? atExit))

-- The recorded binary supplies a resolved exit address.
example : label "exit" ≠ -1 :=
  binBoundary.resolved

end FlatShuffler
