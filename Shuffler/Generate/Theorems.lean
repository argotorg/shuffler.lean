import Shuffler.Generate.Necessity
import Shuffler.Generate.Sufficiency
import Mathlib.Util.TermReduce

namespace Shuffler.Generate

-- Exact condition for adding the requested multiset with DUP, PUSH, and LOAD.
-- The order of additions is free. SWAP and POP are excluded.
theorem canGenerate_iff_ready (spills : SpillSet) (source missing : Stack) :
    delta% Shuffler.Feasibility.AppendOnlyGeneration spills source missing :=
  ⟨CanGenerate.ready, Ready.canGenerate⟩

end Shuffler.Generate
