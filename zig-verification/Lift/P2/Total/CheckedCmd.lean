module

public meta import Lean

public meta section

open Lean Elab Command

namespace Lift.P2.Total

/-- Check every generated command and audit the result before retaining any of
its declarations. Failed attempts leave no theorem or placeholder in scope. -/
def generateChecked (commands : Array (TSyntax `command)) (audit : Array Name) :
    CommandElabM Unit := do
  let saved ← get
  try
    for command in commands, index in [:commands.size] do
      let messages ← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages command
      if messages.hasErrors then
        let errors := messages.toList.filter (·.severity == .error) |>.map (·.data)
        throwError m!"P2 certificate rejected at generated command {index + 1}:\n{MessageData.joinSep errors m!"\n"}"
      modify fun state => { state with messages }
    for name in audit do
      for axiomName in ← liftCoreM (Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "P2 certificate rejected: {name} uses {axiomName}"
  catch error =>
    set saved
    throw error

end Lift.P2.Total
