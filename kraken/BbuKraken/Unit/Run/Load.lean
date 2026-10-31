import ProofKit.SymExec

open Lean Meta Elab Tactic

namespace Bbu.Unit.RunU

-- Match the memory, address, and byte count before `exact` can unfold memory.
private def loadKey? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (_, lhs, _) ← e.consumeMData.eq?
  if !lhs.isAppOfArity ``Option.isSome 2 then none
  else
    let call := lhs.appArg!.consumeMData
    if !call.isAppOf ``Mem.loadInt then none
    else
      let args := call.getAppArgs
      if args.size < 3 then none
      else some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)

elab "run_loads" "[" hs:ident,* "]" : tactic => withMainContext do
  let some key := loadKey? (← instantiateMVars (← getMainTarget))
    | throwError "run_loads: expected a memory load goal"
  for h in hs.getElems do
    let e ← elabTerm h none
    if let some other := loadKey? (← instantiateMVars (← inferType e)) then
      if key == other then
        evalTactic (← `(tactic| exact $h))
        return
  for h in hs.getElems do
    let e ← elabTerm h none
    if let some other := loadKey? (← instantiateMVars (← inferType e)) then
      let sameAddress ← withReducible <| isDefEq key.2.1 other.2.1
      if sameAddress then
        let sameLength ← withReducible <| isDefEq key.2.2 other.2.2
        if sameLength then
          let sameMemory ← withReducible <| isDefEq key.1 other.1
          if sameMemory then
            evalTactic (← `(tactic| exact $h))
            return
  throwError "run_loads: no hypothesis has the same memory, address, and byte count"

end Bbu.Unit.RunU
