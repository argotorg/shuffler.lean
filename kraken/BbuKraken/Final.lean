module

public import BbuKraken.Unit.Loop
import all BbuKraken.Unit.Loop
public import BbuKraken.Unit.Push
import all BbuKraken.Unit.Push
public import BbuKraken.Unit.Dup
import all BbuKraken.Unit.Dup
public import BbuKraken.Unit.SwapWith
import all BbuKraken.Unit.SwapWith
public import BbuKraken.Unit.Produce
import all BbuKraken.Unit.Produce
public import BbuKraken.Unit.Generate
import all BbuKraken.Unit.Generate
public import BbuKraken.Unit.Permute
import all BbuKraken.Unit.Permute
public import BbuKraken.Unit.IsSpilled
import all BbuKraken.Unit.IsSpilled
public import BbuKraken.Unit.ShallowestCopy
import all BbuKraken.Unit.ShallowestCopy
public import BbuKraken.Link
import all BbuKraken.Link

@[expose] public section

namespace Bbu

/-- The contract of `Emission::buildBottomUp`. -/
theorem buildBottomUp_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.decls
    Unit.UnitThmWithExit loopAsm Unit.loopA 2068 Unit.loopQ Unit.loopX := by
  letI := L.decls
  have hexit := L.exit_decl X
  have hspill := Sep.spec_of_body L.isSpilled_decl Unit.isSpilled_unit
  have hcopy := Sep.spec_of_body L.shallowestCopy_decl Unit.shallowestCopy_unit
  have hpush := Sep.specWithExit_of_body L.push_decl (X.returnDistinct _)
    (Unit.push_unit hexit (X.outside push_at))
  have hdup := Sep.specWithExit_of_body L.dup_decl (X.returnDistinct _)
    (Unit.dup_unit hexit (X.outside dup_at))
  have hswap := Sep.specWithExit_of_body L.swapWith_decl (X.returnDistinct _)
    (Unit.swapWith_unit hexit (X.outside swapWith_at))
  have hprod := Sep.specWithExit_of_body L.produce_decl (X.returnDistinct _)
    (Unit.produce_unit hexit (X.outside produce_at) hcopy hspill hpush hdup)
  have hgen := Sep.specWithExit_of_body L.generate_decl (X.returnDistinct _)
    (Unit.generate_unit hexit (X.outside generate_at) hprod hswap)
  have hperm := fun p => Sep.specWithExit_of_bodyW L.finish_decl (X.returnDistinct _)
    (Unit.permute_unit hexit (X.outside finish_at) hcopy p)
  exact Unit.loop_unit hexit (X.outside loop_at) hperm hspill hcopy hgen hswap

end Bbu
