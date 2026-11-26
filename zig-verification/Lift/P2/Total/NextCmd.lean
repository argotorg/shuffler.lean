module

public import Lift.P2.Total.Next
public import Lift.P2.Total.Normalize
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

public meta section

open Lean Elab Command

namespace Lift.P2.Total

/-- Check a proposed set of completed next PCs without enumerating register states. -/
elab "#p2_next " step:ident " at " pc:num " successors " "[" successors:num,* "]"
    " as " output:ident : command => do
  let site := mkIdent (output.getId ++ `site)
  let all := mkIdent (output.getId ++ `all)
  let state := mkIdent `state
  let mut predicate ← `(False)
  for next in successors.getElems.reverse do
    predicate ← `(($state).pc = ($next : Int64) ∨ $predicate)
  let equation ← `(#p2_step_eq $step at $pc as $site)
  let siteRule ← `(Lean.Parser.Tactic.rwRule| $site:ident)
  let theoremCommand ← `(theorem $all (data : MachineData) :
      Lift.P2.Total.AllNext (fun $state : MachineState => $predicate)
        ($step { data := data, pc := $pc }) := by
    rw [$siteRule]
    simp only [Lift.P2.Total.AllNext]
    repeat' (first | apply Lift.P2.Total.AllNext.load |
      apply Lift.P2.Total.AllNext.store | (intro) | (split)) <;>
      simp_all [Lift.P2.Total.AllNext])
  let currentNamespace ← getCurrNamespace
  generateChecked #[equation, theoremCommand]
    #[currentNamespace ++ site.getId, currentNamespace ++ all.getId]

end Lift.P2.Total
