import Shuffler.Generate.Theorems

def State.missingValues (state : State source target spills) : Stack :=
  ((List.finRange target.length).filter fun dest => (state.mapping.symm dest).isNone).map
    (fun dest => target[dest])

theorem State.mem_missingValues (state : State source target spills) (value : Value) :
    value ∈ state.missingValues ↔
      ∃ dest, state.mapping.symm dest = none ∧ target[dest] = value := by
  simp [State.missingValues, List.mem_filter]

namespace Shuffler.BuildBottomUp

-- This concerns the values of all unbound destinations. It does not place them.
-- State.Valid is not required.
theorem canGenerate_missing_iff_reachable (state : State source target spills) :
    Generate.CanGenerate spills state.stack state.missingValues ↔ Reachable state := by
  rw [Generate.canGenerate_iff_ready]
  constructor
  · intro h dest hd
    exact h target[dest] ((state.mem_missingValues _).mpr ⟨dest, hd, rfl⟩)
  · intro h value hv
    obtain ⟨dest, hd, rfl⟩ := (state.mem_missingValues _).mp hv
    exact h dest hd

end Shuffler.BuildBottomUp
