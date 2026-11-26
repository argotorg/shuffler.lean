import Skel.Toy.Held
import Skel.Test.ChainSumSpec

/-! A synthetic chain sum for the suite `genloop` (task AF2-C): the code of `toyWalk` (`Lift/Toys/data/toy.zig`) with
`addq (%rdi), %rax` in place of `incq %rax`:

    var s: u64 = 0;
    var p = head;
    while (p) |q| : (p = q.next) s +%= q.val;
    return s;

The instruction has the size of the one it replaces (3 bytes), so the sizes of `Lift.Toys.Code` hold. The function keeps the name
`toyWalk`, so that the model text has the constants of `Lift.Toys.L1`. The nodes, the statement and the hint are those of
`toyWalk`; the L3 `run` is `Skel.Test.ChainSumSpec.run`. -/

namespace ChainSumFixture

open Skel Skel.Gen Skel.Toy.Held

/-- The one directive of the assembly line `s`. -/
def directive? (s : String) : Option Directive :=
  match Kraken.X64.Parser.parse s with
  | .ok [d] => some d
  | _ => none

/-- The program `p` where the first directive `old` after the label `entry` is `new`. -/
def replaceAfter (entry : String) (old new : Directive) :
    List (Kraken.Sized Directive) → Bool → List (Kraken.Sized Directive)
  | [], _ => []
  | s :: rest, seen =>
    let seen' := seen || s.directive.label? == some entry
    if seen' && s.directive == old then { s with directive := new } :: rest
    else s :: replaceAfter entry old new rest seen'

/-- The code of the chain sum. -/
def code : Option Executable := do
  let inc ← directive? " incq\t%rax"
  let add ← directive? " addq\t(%rdi), %rax"
  let c := Lift.Toys.Code.code
  pure ⟨c.startAddr, replaceAfter "toyWalk" inc add c.program false⟩

/-- The statement shape of `toyWalk` with the specification of the chain sum. -/
def shape : Option StmtShape := do
  let text ← shapeJson "toyWalk"
  let j ← (Lean.Json.parse (text.replace "Lift.Toys.WalkSpec" "Skel.Test.ChainSumSpec")).toOption
  (Shape.parse j).toOption

/-- The blocks, the plan and the shape of the chain sum, and its generation. -/
def build : Except GenError (List Block × UpperPlan × StmtShape × Upper) := do
  let some c := code | throw (.noFunction "code")
  let some sh := shape | throw (.noFunction "shape")
  let some h := hintOf "toyWalk" | throw (.noFunction "hint")
  let bs ← blocksFrom c .table "toyWalk"
  let ff ← frameFacts ((targetOf "toyWalk").callees.map fun c => (c.name, c.room)) bs
  let p ← upperPlan ⟨"toyWalk", bs, vars bs, ff, none⟩ sh h
  let u ← generateUpper (targetOf "toyWalk") .storeChain c .table "Lift.Toys.Code.code" "toyWalk" sh h (samplerModel (targetOf "toyWalk") sh)
  pure (bs, p, sh, u)

/-- The upper chain of the chain sum with the value offsets of its ghosts (`valueLoads`): the templates and the slot lines
of `loopTemplates` and `loopSlots` with them. -/
def upper : Except GenError (UpperPlan × Upper) := do
  let (bs, p, sh, u) ← build
  let vals := valueLoads bs p
  pure (p, { u with templates := loopTemplates p sh vals, slots := loopSlots p sh vals })

/-- The header of the check files: that of `toyWalk`, with the module of the specification of the chain sum. -/
def header : Header :=
  let h := upperHeader "toyWalk"
  { h with imports := h.imports ++ ["Skel.Test.ChainSumSpec"], namespace_ := "Skel.Gen.Held.chainSum" }

end ChainSumFixture
