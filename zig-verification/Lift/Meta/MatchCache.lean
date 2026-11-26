module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Match.MatchEqs

@[expose] public section

namespace Lift

open Lean Elab Command

/-- Realize the current module's matcher congruence equations once. Dependent
modules then import the same checked equations and their helper declarations. -/
syntax (name := realizeMatchCongruences) "#realize_match_congruences" : command

elab_rules : command
  | `(#realize_match_congruences) => liftTermElabM do
    let env ← getEnv
    let names := env.constants.fold (init := []) fun names name _ =>
      if !env.isImportedConst name && Lean.Meta.isMatcherCore env name then name :: names else names
    let names := names.toArray.qsort Name.quickLt
    for name in names do
      discard (Lean.Meta.Match.genMatchCongrEqns name)

end Lift
