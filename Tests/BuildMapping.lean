import Shuffler.BuildMapping.Defs

open Shuffler.BuildMapping

namespace BuildMappingTests

-- The destination of every source slot, and whether a copy in a wildcard slot was seen.
private def observe (source target : Stack) (dropped : List Byte) (strategy : WildcardSlotsStrategy) :
    Option (List (Option ℕ) × Bool) :=
  match buildMapping source target dropped strategy with
  | .ok result => some ((List.ofFn result.mapping).map (·.map Fin.val), result.sawWildcardCopy)
  | .error _ => none

private def smallStacks : List Stack :=
  (List.range 4).flatMap fun n =>
    (List.replicate n [.Var ⟨0⟩, .Var ⟨1⟩, .Wildcard, .FunctionReturnLabel]).sections

-- Check both production runs for every stack pair up to length three and every
-- dropped list over 0, 1, and 255. Errors count as failures; no case is filtered.
-- The report counts cases, execution errors, flag differences, and failures of
-- the equivalence between equal mappings and a false flag.
private def strategyReport : ℕ × ℕ × ℕ × ℕ :=
  let outcomes := smallStacks.flatMap fun source => smallStacks.flatMap fun target =>
    (List.replicate source.length ([0, 1, 255] : List Byte)).sections.map fun dropped =>
      (observe source target dropped .Leave, observe source target dropped .Take)
  (outcomes.length,
    outcomes.countP fun
      | (some _, some _) => false
      | _ => true,
    outcomes.countP fun
      | (some (_, leaveFlag), some (_, takeFlag)) => leaveFlag != takeFlag
      | _ => false,
    outcomes.countP fun
      | (some (leave, leaveFlag), some (take, _)) => (leave == take) != !leaveFlag
      | _ => false)

-- There are 85 target stacks and 1885 source/drop pairs: 85 * 1885 = 160225.
example : strategyReport = (160225, 0, 0, 0) := by native_decide

end BuildMappingTests
