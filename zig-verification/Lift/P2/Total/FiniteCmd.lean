module

public import Lift.P2.Total.Normalize
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

public meta section

open Lean Elab Command

namespace Lift.P2.Total

declare_syntax_cat p2FiniteSource
syntax "source_closed" ident : p2FiniteSource

declare_syntax_cat p2FinitePart
syntax "only" ident : p2FinitePart

/-- Parse the same four correspondence obligations for both proof methods. -/
def finitePartIndex (part : Option (TSyntax `p2FinitePart)) : CommandElabM (Option Nat) :=
  match part with
  | none => pure none
  | some part =>
    let selected := part.raw[1].getId
    match #[`leftClosed, `rightClosed, `summary, `exit].idxOf? selected with
    | some index => pure (some index)
    | none => throwError "unknown finite obligation {selected}"

/-- Generate the site equations and the four finite correspondence obligations.
Every obligation must close. A failed normalization prevents module acceptance. -/
elab "#p2_finite " asm:ident " step " step:ident " exact " exactProof:ident
    " using " "(" boundary:ident "," contract:ident "," model:ident ")"
    sourceClosed:(p2FiniteSource)?
    " depths " "(" sourceDepth:num "," targetDepth:num ")"
    " sites " "[" sites:num,* "]" " unfold " "[" extra:ident,* "]" " as " output:ident
    part:(p2FinitePart)? : command => do
  let partIndex? ← finitePartIndex part
  let mut rules := extra.getElems
  let mut commands : Array (TSyntax `command) := #[]
  let mut audit : Array Name := #[]
  let currentNamespace ← getCurrNamespace
  for pc in sites.getElems, index in [:sites.getElems.size] do
    let name := mkIdent (output.getId ++ Name.mkSimple s!"site{index}")
    commands := commands.push (← `(#p2_step_eq $step at $pc as $name))
    rules := rules.push name
    audit := audit.push (currentNamespace ++ name.getId)
  let leftName := mkIdent (output.getId ++ `leftClosed)
  let rightName := mkIdent (output.getId ++ `rightClosed)
  let summaryName := mkIdent (output.getId ++ `summary)
  let exitName := mkIdent (output.getId ++ `exit)
  let theoremName := mkIdent (output.getId ++ `spec)
  let sourceTerm : TSyntax `term := ⟨sourceDepth.raw⟩
  let targetTerm : TSyntax `term := ⟨targetDepth.raw⟩
  -- Each obligation has a separate elaboration budget. The batch remains atomic.
  if let some sourceClosed := sourceClosed then
    let sourceClosed : TSyntax `ident := ⟨sourceClosed.raw[1]⟩
    commands := commands.push (← `(theorem $leftName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
        ∀ initial, ($contract policy word) initial → ∀ t,
          ¬ Lift.P2.Total.unroll
            (Lift.P2.Total.cpuSystem $step policy (($boundary word).returned initial)
              (($boundary word).visible initial)) $sourceTerm initial (.pending t) := by
      exact $sourceClosed policy word))
  else
    commands := commands.push (← `(theorem $leftName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
        ∀ initial, ($contract policy word) initial → ∀ t,
          ¬ Lift.P2.Total.unroll
            (Lift.P2.Total.cpuSystem $step policy (($boundary word).returned initial)
              (($boundary word).visible initial)) $sourceTerm initial (.pending t) := by
      intro initial valid
      rcases initial with ⟨data, pc⟩
      cases valid
      p2_nf [$rules,*]))
  commands := commands.push (← `(theorem $rightName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
      ∀ initial, ($contract policy word) initial → ∀ t,
        ¬ Lift.P2.Total.unroll ($model policy).system $targetTerm
          (($model policy).entry initial) (.pending t) := by
    intro initial valid
    rcases initial with ⟨data, pc⟩
    cases valid
    p2_nf [$rules,*]))
  commands := commands.push (← `(theorem $summaryName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
      ∀ initial, ($contract policy word) initial → ∀ out,
        Lift.P2.Total.unroll
          (Lift.P2.Total.cpuSystem $step policy (($boundary word).returned initial)
            (($boundary word).visible initial)) $sourceTerm initial (.finished out) ↔
        Lift.P2.Total.unroll ($model policy).system $targetTerm
          (($model policy).entry initial) (.finished out) := by
    intro initial valid
    rcases initial with ⟨data, pc⟩
    cases valid
    p2_nf [$rules,*]))
  commands := commands.push (← `(theorem $exitName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
      ∀ initial, ($contract policy word) initial → ∀ final value,
        Lift.P2.Total.visits
          (Lift.P2.Total.cpuSystem $step policy (($boundary word).returned initial)
            (($boundary word).visible initial)) $sourceTerm initial final →
        ($boundary word).returned initial final = some value →
        Lift.P2.Total.AbiRestored initial final := by
    intro initial valid
    rcases initial with ⟨data, pc⟩
    cases valid
    p2_nf [$rules,*]))
  commands := commands.push (← `(theorem $theoremName (policy : Lift.P2.Total.CpuPolicy) (word : Int) :
      Lift.P2.Total.CallSpec $asm policy ($boundary word) ($contract policy word) ($model policy) := by
    exact Lift.P2.Total.CallSpec.of_finite _ _ $exactProof _ _ _ _ $sourceTerm $targetTerm
      ($leftName policy word) ($rightName policy word) ($summaryName policy word) ($exitName policy word)))
  for name in #[leftName, rightName, summaryName, exitName, theoremName] do
    audit := audit.push (currentNamespace ++ name.getId)
  if let some index := partIndex? then
    let siteCount := sites.getElems.size
    commands := commands.extract 0 siteCount |>.push commands[siteCount + index]!
    audit := audit.extract 0 siteCount |>.push audit[siteCount + index]!
  generateChecked commands audit

end Lift.P2.Total
