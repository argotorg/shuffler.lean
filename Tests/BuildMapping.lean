import Shuffler

open Shuffler.BuildMapping

-- The new entry point returns the same result, including errors and the copy flag.
example (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy) :
    buildMapping_new source target dropped strategy = buildMapping source target dropped strategy :=
  buildMapping_new_eq_buildMapping source target dropped strategy

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

-- Both strategies report the same copy flag.
example (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take) :
    leave.sawWildcardCopy = take.sawWildcardCopy :=
  buildMapping_sawWildcardCopy_eq source target dropped hleave htake

-- The copy flag states exactly when the strategies produce different mappings.
example (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take) :
    leave.mapping = take.mapping ↔ leave.sawWildcardCopy = false :=
  buildMapping_mapping_eq_iff source target dropped hleave htake

-- The witness from a true flag rules out equality of the mappings.
example (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take)
    (hflag : leave.sawWildcardCopy = true) : leave.mapping ≠ take.mapping := by
  obtain ⟨t, s, _, _, hfree, hbound⟩ :=
    buildMapping_differs_of_sawWildcardCopy source target dropped hleave htake hflag
  intro heq
  rw [heq, hbound] at hfree
  cases hfree

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
#guard observe [.FunctionReturnLabel, b] [.Wildcard, .FunctionReturnLabel] [0, 0] (strategy := .Take) ==
  some ([some 1, some 0], false)

-- An assigned target does not request another copy from its wildcard slot.
#guard observe [a, a] [.Wildcard, a] [0, 0] (strategy := .Leave) ==
  some ([some 0, some 1], false)
#guard observe [a, a] [.Wildcard, a] [0, 0] (strategy := .Take) ==
  some ([some 0, some 1], false)

-- A dropped copy does not set the flag; the other source fills the wildcard.
#guard observe [a, b] [.Wildcard, a] [255, 0] (strategy := .Leave) ==
  some ([none, some 0], false)
#guard observe [a, b] [.Wildcard, a] [255, 0] (strategy := .Take) ==
  some ([none, some 0], false)

private def listsOfLength (values : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => values.flatMap fun value => (listsOfLength values n).map (value :: ·)

private def smallStacks : List Stack :=
  (List.range 4).flatMap (listsOfLength [a, b, .Wildcard, .FunctionReturnLabel])

-- Check both production runs for every stack pair up to length three and every
-- dropped list over 0, 1, and 255. Errors count as failures; no case is filtered.
-- The report counts cases, execution errors, flag differences, and failures of
-- the equivalence between equal mappings and a false flag.
private def strategyReport : ℕ × ℕ × ℕ × ℕ :=
  smallStacks.foldl (fun report source =>
    smallStacks.foldl (fun report target =>
      (listsOfLength ([0, 1, 255] : List Byte) source.length).foldl
        (fun (tested, errors, flagErrors, mappingErrors) dropped =>
          match observe source target dropped .Leave, observe source target dropped .Take with
          | some (leaveMapping, leaveFlag), some (takeMapping, takeFlag) =>
            (tested + 1, errors,
              flagErrors + if leaveFlag == takeFlag then 0 else 1,
              mappingErrors + if (leaveMapping == takeMapping) == !leaveFlag then 0 else 1)
          | _, _ => (tested + 1, errors + 1, flagErrors, mappingErrors)) report) report)
    (0, 0, 0, 0)

-- There are 85 target stacks and 1885 source/drop pairs: 85 * 1885 = 160225.
example : strategyReport = (160225, 0, 0, 0) := by native_decide

end BuildMappingTests
