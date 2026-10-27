import Shuffler.BuildMapping.Defs
import Shuffler.Trace

namespace Shuffler.Planner

-- The planner fields used by resolve. Source and target stay fixed between attempts.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:1005-1011.
structure State (source target : Stack) where
  spills : SpillSet
  spillingAllowed : Bool
  dropped : Vector BuildMapping.Byte source.length

end Shuffler.Planner
