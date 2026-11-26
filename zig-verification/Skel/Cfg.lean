import Lift.P2.Gen.Asm
import Lift.Spike.Code

/-! The `Cfg` of one function of the program of `Lift.Spike.Code` (`docs/one-way-lift-skeleton-plan-20261118.md`, 5.4).
The slice of a function is its directives from its label up to the first `.Lfunc_end<k>` label after it (that label is
not included). -/

namespace Skel.Cfg

open Kraken.X64

/-- Is the directive the label of the end of a function (`.Lfunc_end<k>`)? -/
def isFuncEnd (d : Directive) : Bool := d.label?.any (·.startsWith ".Lfunc_end")

/-- The directives of the function `name`: from its label up to the end label after it (not included).
An unknown name, or a name with no end label after it, is an error. -/
def sliceFunction (p : Program) (name : String) : Except String Program :=
  match p.dropWhile (fun d => d.label? != some name) with
  | [] => .error s!"no label {name}"
  | start :: body =>
    let (fn, rest) := body.span (fun d => !isFuncEnd d)
    if rest.isEmpty then .error s!"no end label after {name}" else .ok (start :: fn)

/-- The `Cfg` of the function `name` of `Lift.Spike.Code.program`. -/
def ofFunction (name : String) : Except String Lift.P2.Gen.Cfg := do
  Lift.P2.Gen.Cfg.ofProgram (← sliceFunction Lift.Spike.Code.program name)

end Skel.Cfg
