import Shuffler.Planner.Defs

namespace Shuffler.Planner

variable {source target : Stack}

-- Returns the success flag and updated planner state.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:904.
def resolve (state : State source target)
    (mapping : Mapping source.length target.length)
    (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) : Bool × State source target := by
  sorry

end Shuffler.Planner
