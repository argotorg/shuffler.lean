import Shuffler

open Shuffler.BuildMapping

-- The theorems apply to the production function.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    (h : dropped.length = source.length) (reason : String) :
    buildMapping source target dropped strategy ≠ .error (.assertion reason) :=
  buildMapping_no_assertion source target dropped strategy h reason

namespace BuildMappingTests

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩

-- The destination of every source slot, and whether a copy in a wildcard slot was seen.
private def observe (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy := .Leave) :
    Option (List (Option ℕ) × Bool) :=
  match buildMapping source target dropped strategy with
  | .ok mb => some ((List.ofFn mb.mapping).map (·.map Fin.val), mb.sawWildcardCopy)
  | .error _ => none

-- A `dropped` list of the wrong length is an assertion error.
#guard observe [a, b] [a, b] [0] == none

-- Slots already in place stay there.
#guard observe [a, b] [a, b] [0, 0] == some ([some 0, some 1], false)

-- Each target offset takes the copy of its value.
#guard observe [a, b] [b, a] [0, 0] == some ([some 1, some 0], false)

-- A dropped slot is never mapped.
#guard observe [a] [a] [1] == some ([none], false)

-- A wildcard target keeps whatever sits there.
#guard observe [a, b] [.Wildcard, b] [0, 0] == some ([some 0, some 1], false)

-- A copy in a wildcard slot is left in place by `Leave`; the surplus `b` is not mapped.
#guard observe [a, b] [.Wildcard, a] [0, 0] (strategy := .Leave) == some ([some 0, none], true)

-- `Take` moves the copy out of the wildcard slot, which then absorbs the surplus `b`.
#guard observe [a, b] [.Wildcard, a] [0, 0] (strategy := .Take) == some ([some 1, some 0], true)

-- A function return label is always taken and does not count as a seen wildcard copy.
#guard observe [.FunctionReturnLabel, b] [.Wildcard, .FunctionReturnLabel] [0, 0] ==
  some ([some 1, some 0], false)

end BuildMappingTests
