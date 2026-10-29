import Shuffler.Trace

-- Adding a variable preserves the existing spills and includes its ID.
example (spills : SpillSet) (id : VarId) (h : id ∉ spills) :
    spills.add (.Var id) = .ok (insert id spills) := by
  simp only [SpillSet.add, Shuffler.requires, dite_eq_left h]
  rfl

-- An existing ID cannot be added again.
example (spills : SpillSet) (id : VarId) (h : id ∈ spills) :
    spills.add (.Var id) = .error (.assertion "value already spilled") := by
  simp only [SpillSet.add, Shuffler.requires, dite_eq_right (not_not_intro h)]
  rfl

-- Only variable slots can be spilled.
example (spills : SpillSet) (word : Word) :
    spills.add (.Lit word) =
      .error (.assertion "spill candidate must be a variable") := by
  rfl

example (spills : SpillSet) :
    spills.add .Wildcard =
      .error (.assertion "spill candidate must be a variable") := by
  rfl

example (spills : SpillSet) :
    spills.add .FunctionReturnLabel =
      .error (.assertion "spill candidate must be a variable") := by
  rfl

-- Add two IDs, including zero, to an empty set.
example : (do
    let spills ← (∅ : SpillSet).add (.Var ⟨0⟩)
    spills.add (.Var ⟨1⟩)) = .ok ({⟨0⟩, ⟨1⟩} : SpillSet) := by
  native_decide

-- A second addition of the same ID fails.
example : (do
    let spills ← (∅ : SpillSet).add (.Var ⟨0⟩)
    spills.add (.Var ⟨0⟩)) = .error (.assertion "value already spilled") := by
  native_decide
