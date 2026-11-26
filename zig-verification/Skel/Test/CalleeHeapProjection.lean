import Skel.Test.GenUpperCall
import Lift.Sem.CallArmBytes

/-! A callee exports its input type into a caller namespace. A different
parent input type has the same name. Use the field of the exported type. -/

namespace CalleeHeapProjectionTests

open Skel Skel.Gen

def file (bytes : Bool) (withShape : Bool := true) : Except GenError String := do
  let sF ← GenUpperCallTests.summaryF
  let sG ← GenUpperCallTests.summaryG
  let pF := { (← GenUpperCallTests.planF) with call := if bytes then .callB else .call }
  let pG := { (← GenUpperCallTests.planG) with call := if bytes then .callB else .call }
  let tF ← GenUpperCallTests.textsOf GenUpperCallTests.calleeTarget sF pF 0
  let tG ← GenUpperCallTests.textsOf GenUpperCallTests.target sG pG 16
  let rF ← refinesProof GenUpperCallTests.calleeTarget sF pF
  let rG ← refinesProof GenUpperCallTests.target sG pG
  let shape ← shapeProof sF pF
  let fBody := tF ++ s!"\n\ntheorem refines_l2p : {(refinesL2Row pF).statement} := by\n{rF}" ++
    s!"\n\ntheorem shape : {shapeStatementFor bytes} := by\n{shape}"
  let names := (declNames fBody).filter (fun n => withShape || n != "shape")
  pure ("\n".intercalate ((GenUpperCallTests.imports ++ ["Lift.Sem.CallArmBytes"]).map ("import " ++ ·)) ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++
    "\nnamespace HeapProjection\nnamespace Actual.F\n" ++ fBody ++ "\nend Actual.F\n" ++
    "namespace F\nstructure In2p where\n  heap : Heap\nend F\n" ++
    "namespace Caller\nnamespace F\n" ++
    s!"export HeapProjection.Actual.F ({" ".intercalate names})\nend F\n" ++ tG ++
    s!"\n\ntheorem refines_l2p : {(refinesL2Row pG).statement} := by\n{rG}" ++
    "\nend Caller\nend HeapProjection\n#print axioms HeapProjection.Caller.refines_l2p\n")

def check (bytes withShape : Bool) : IO Unit := do
  let .ok text := file bytes withShape | throw (IO.userError "fixture generation failed")
  let dir ← Skel.tempDir "callee-heap-projection"
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (result, _) ← Skel.Io.checkFile .bvDecide path "HeapProjection.Caller.refines_l2p" 120000
  let good := if withShape then
      match result with
      | .accepted axioms => axioms.all ["propext", "Classical.choice", "Quot.sound"].contains
      | _ => false
    else
      match result with
      | .failed errors => errors.any (fun error => (error.splitOn "shape").length > 1)
      | _ => false
  unless good do throw (IO.userError s!"projection fixture (bytes={bytes}, shape={withShape}): {repr result}; {path}")

#eval check false true
#eval check true true
#eval check false false
#eval check true false

end CalleeHeapProjectionTests
