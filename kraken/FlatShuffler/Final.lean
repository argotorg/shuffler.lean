module

public import FlatShuffler.Unit.Loop
import all FlatShuffler.Unit.Loop
public import FlatShuffler.Unit.Push
import all FlatShuffler.Unit.Push
public import FlatShuffler.Unit.Dup
import all FlatShuffler.Unit.Dup
public import FlatShuffler.Unit.SwapWith
import all FlatShuffler.Unit.SwapWith
public import FlatShuffler.Unit.Produce
import all FlatShuffler.Unit.Produce
public import FlatShuffler.Unit.Generate
import all FlatShuffler.Unit.Generate
public import FlatShuffler.Unit.Permute
import all FlatShuffler.Unit.Permute
public import FlatShuffler.Unit.IsSpilled
import all FlatShuffler.Unit.IsSpilled
public import FlatShuffler.Unit.ShallowestCopy
import all FlatShuffler.Unit.ShallowestCopy
public import FlatShuffler.Link
import all FlatShuffler.Link

@[expose] public section

namespace FlatShuffler

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

end FlatShuffler
