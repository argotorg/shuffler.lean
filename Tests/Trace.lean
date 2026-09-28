import Shuffler.Defs

namespace TraceTests

-- A spill can be loaded even when the variable is absent from the stack.
example (spills : SpillSet) (id : VarId) (hspilled : id ∈ spills) (source : Stack) :
    Trace spills source (source ++ [.Var id]) :=
  .Load id hspilled (.Lit source)

def spills : SpillSet := {⟨0⟩, ⟨37⟩}

def loaded : Trace spills [] [.Var ⟨0⟩, .Var ⟨37⟩] :=
  .Load ⟨37⟩ (by decide) (.Load ⟨0⟩ (by decide) (.Lit []))

def swapped : Trace spills [.Var ⟨0⟩, .Var ⟨37⟩] [.Var ⟨37⟩, .Var ⟨0⟩] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit _)

def reloaded : Trace spills [.Var ⟨37⟩, .Var ⟨0⟩] [.Var ⟨37⟩, .Var ⟨0⟩, .Var ⟨37⟩] :=
  .Load ⟨37⟩ (by decide) (.Lit _)

-- Loads on both sides of a swap compose without adding to the swap count.
example : (loaded.concat (swapped.concat reloaded)).swapCount = 1 := rfl

-- An empty spill set and an absent ID cannot supply permission to load.
#check_failure (Trace.Load (spills := ∅) ⟨0⟩ (by decide) (.Lit []))
#check_failure (Trace.Load (spills := spills) ⟨1⟩ (by decide) (.Lit []))

-- Only variable IDs can be loaded, and concatenation preserves the spill set.
#check_failure (Trace.Load (spills := spills) (Value.Lit 0) (by decide) (.Lit []))
#check_failure (loaded.concat (Trace.Lit (spills := ∅) [.Var ⟨0⟩, .Var ⟨37⟩]))

end TraceTests
