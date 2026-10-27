import Shuffler

open Shuffler.BuildMapping

-- The theorems apply to the production function.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy) :
    (∃ result, buildMapping source target dropped strategy = .ok result) ↔
      dropped.length = source.length :=
  buildMapping_ok source target dropped strategy

example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    (h : dropped.length = source.length) (reason : String) :
    buildMapping source target dropped strategy ≠ .error (.assertion reason) :=
  buildMapping_no_assertion source target dropped strategy h reason

-- Every binding uses a source that is not dropped and matches its target.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (t : Fin target.length) (hbound : result.mapping s = some t) :
    dropped[s.val]? = some 0 ∧ SlotMatches source[s] target[t] :=
  buildMapping_valid_of_ok source target dropped strategy hrun s t hbound

-- A target that is not a wildcard requires the same value.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (t : Fin target.length) (hbound : result.mapping s = some t)
    (htarget : ¬ target[t].is_junk) : source[s] = target[t] :=
  (buildMapping_valid_of_ok source target dropped strategy hrun s t hbound).2.resolve_left htarget

-- A dropped source has no binding.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (hdrop : dropped[s.val]? ≠ some 0) : result.mapping s = none := by
  cases hbound : result.mapping s with
  | none => rfl
  | some t => exact (hdrop (buildMapping_valid_of_ok source target dropped strategy hrun s t hbound).1).elim

-- Later passes keep equal values at the same offset bound to each other.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy)
    {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (t : Fin target.length) (hpos : s.val = t.val)
    (hvalue : source[s] = target[t]) (hdrop : dropped[s.val]? = some 0) :
    result.mapping s = some t :=
  buildMapping_in_place_of_ok source target dropped strategy hrun s t hpos hvalue hdrop

namespace BuildMappingTests

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩

-- The destination of every source slot, and whether a copy in a wildcard slot was seen.
private def observe (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy := .Leave) :
    Option (List (Option ℕ) × Bool) :=
  match buildMapping source target dropped strategy with
  | .ok result => some ((List.ofFn result.mapping).map (·.map Fin.val), result.sawWildcardCopy)
  | .error _ => none

-- A `dropped` list of the wrong length is an assertion error.
#guard observe [a, b] [a, b] [0] == none
#guard observe [a] [a] [0, 0] == none
#guard observe [] [] [0] == none

-- Empty stacks and different source and target lengths can succeed.
#guard observe [] [] [] == some ([], false)
#guard observe [] [a] [] == some ([], false)
#guard observe [a] [] [0] == some ([none], false)

-- Slots already in place stay there.
#guard observe [a, b] [a, b] [0, 0] == some ([some 0, some 1], false)

-- Later passes use other copies without moving a slot that is already in place.
#guard observe [a, a, b] [a, b] [0, 0, 0] == some ([some 0, none, some 1], false)
#guard observe [a, b, a] [b, b, a, a] [0, 0, 0] == some ([some 3, some 1, some 2], false)
#guard observe [.Wildcard, a, b] [.Wildcard, b, a] [0, 0, 0] ==
  some ([some 0, some 2, some 1], false)
#guard observe [a, b, a, b] [.Wildcard, a, a, b] [0, 0, 0, 0] (strategy := .Leave) ==
  some ([some 0, none, some 2, some 3], true)
#guard observe [a, b, a, b] [.Wildcard, a, a, b] [0, 0, 0, 0] (strategy := .Take) ==
  some ([some 1, some 0, some 2, some 3], true)

-- Each target offset takes the copy of its value.
#guard observe [a, b] [b, a] [0, 0] == some ([some 1, some 0], false)

-- A dropped slot is never mapped.
#guard observe [a] [a] [1] == some ([none], false)
#guard observe [a] [a] [255] == some ([none], false)
#guard observe [a, a] [a, a] [1, 0] == some ([none, some 1], false)

-- A dropped source cannot fill a wildcard target either.
#guard observe [a] [.Wildcard] [255] == some ([none], false)

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
