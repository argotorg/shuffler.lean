import Shuffler.Optimality.BirthPlacement.SourceRealize.BirthTheorems

namespace Shuffler.Optimality.BirthPlacement

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

def SourceBuildState.birth (state : SourceBuildState plan height) (hh : height < target.length) :
    SourceBirth state hh :=
  let birth := appendBirth spills state.current (state.value hh) (state.method hh) (state.physical hh)
  let trace := state.growth hh ▸ birth.val
  { built := ⟨trace, (Trace.noPop_cast _ _).mpr birth.property.1,
      (Trace.additions_cast _ _).trans birth.property.2.1⟩
    count := (swapCount_cast _ _).trans birth.property.2.2.1
    events := (traceEvents_cast _ _).trans birth.property.2.2.2 }

end Shuffler.Optimality.BirthPlacement
