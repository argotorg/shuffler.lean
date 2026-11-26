import Skel.Gen.GenerateUpper

/-! The L2+ definitions that a full module exports for callers. They use the code and ABI metadata.
They state no theorem and require no L3 statement. -/

namespace Skel.Full

open Skel.Gen

/-- The generic L2+ model and its relations to L2, in the namespace of the function's L2 model. -/
def interfaceText (t : Target) (code : Executable) (src : BlockSource) (fn : String) : Except GenError String := do
  let bs ← blocksFrom code src fn
  let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨fn, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩
  let p := calleePlan s
  pure ((← upperModelText t s p) ++ "\n\n" ++ upperSimText p)

end Skel.Full
