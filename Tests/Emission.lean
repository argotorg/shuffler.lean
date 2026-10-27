import Shuffler.Emission.Defs

open Shuffler.Emission

namespace EmissionTests

private def state : State (List.replicate 18 (.Lit 0)) [] ∅ where
  planned_mapping := ⊥
  stack := List.replicate 18 (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

-- Block preserves the offset and positive excess; zero excess is an assertion error.
example : state.block ⟨5, by decide⟩ 3 = .ok (.Blocked ⟨5, 3⟩) := rfl
example : state.block ⟨5, by decide⟩ 0 =
    .error (.assertion "blocked excess must be positive") := rfl

-- At depth 17, SWAP is one slot out of reach; at depth 16, it is in reach.
example : state.blockSwapUnreachable ⟨0, by decide⟩ = .ok (.Blocked ⟨0, 1⟩) := rfl
example : state.blockSwapUnreachable ⟨1, by decide⟩ =
    .error (.assertion "blocked excess must be positive") := rfl

-- DUP has a different limit: depths 17 and 16 block, and depth 15 is in reach.
example : state.blockDupUnreachable ⟨0, by decide⟩ = .ok (.Blocked ⟨0, 2⟩) := rfl
example : state.blockDupUnreachable ⟨1, by decide⟩ = .ok (.Blocked ⟨1, 1⟩) := rfl
example : state.blockDupUnreachable ⟨2, by decide⟩ =
    .error (.assertion "blocked excess must be positive") := rfl

-- The top gives zero excess after subtraction for both helpers.
example : state.blockSwapUnreachable ⟨17, by decide⟩ =
    .error (.assertion "blocked excess must be positive") := rfl
example : state.blockDupUnreachable ⟨17, by decide⟩ =
    .error (.assertion "blocked excess must be positive") := rfl

-- The caller throws the blocked result, or propagates the helper's assertion.
example : (do throw (← state.blockDupUnreachable ⟨1, by decide⟩) : Except ShuffleErr Unit) =
    .error (.Blocked ⟨1, 1⟩) := rfl
example : (do throw (← state.blockDupUnreachable ⟨2, by decide⟩) : Except ShuffleErr Unit) =
    .error (.assertion "blocked excess must be positive") := rfl

end EmissionTests
