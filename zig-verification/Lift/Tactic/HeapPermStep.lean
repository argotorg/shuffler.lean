module
public import Lean
public import Lift.Sem.HeapBytesPerm
public import Lift.Sem.HeapBytesStoreSound
public import Lift.Tactic.ResStep
@[expose] public section
namespace Lift.Tactic
open Lean Meta Elab Tactic Lift.Sem

/-- Match current heap facts without changing unrelated proof state. -/
private meta def heapFacts (heap : Expr) : TacticM (Array (Expr × Expr)) := do
  let mut relations := #[]
  let mut held := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      if type.isAppOfArity ``List.Perm 3 then
        if ← isDefEq type.getAppArgs[1]! heap then
          relations := relations.push (mkFVar decl.fvarId)
        else if ← isDefEq type.getAppArgs[2]! heap then
          relations := relations.push (← mkAppM ``List.Perm.symm #[mkFVar decl.fvarId])
      if type.isAppOfArity ``Heap.Holds 3 then
        if ← isDefEq type.getAppArgs[1]! heap then
          held := held.push (mkFVar decl.fvarId)
  return relations.flatMap fun hp => held.map fun hh => (hp, hh)

/-- Replay the next successful heap operation in the permuted target heap.
Each store supplies the relation and memory witness for the next step. -/
elab "heap_perm_step " hyp:ident : tactic => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let proof ← Term.elabTerm hyp none
      unless proof.isFVar do throwError "heap_perm_step: expected a local execution equation"
      let type ← instantiateMVars (← inferType proof)
      let some (_, lhs, rhs) := type.eq? | throwError "heap_perm_step: expected an execution equation"
      unless rhs.isAppOfArity ``Res.ok 2 do throwError "heap_perm_step: expected a successful execution"
      let some matcher ← matchMatcherApp? lhs.consumeMData (alsoCasesOn := true) |
        throwError "heap_perm_step: expose the next result match"
      unless matcher.discrs.size == 1 && matcher.getNumDiscrEqs == 0 do
        throwError "heap_perm_step: expected one result discriminator"
      let operation := matcher.discrs[0]!
      let isLoad := operation.isAppOfArity ``Heap.loadB 3
      let isStore := operation.isAppOfArity ``Heap.storeB 4
      unless isLoad || isStore do throwError "heap_perm_step: expected a byte heap load or store"
      let args := operation.getAppArgs
      let candidates ← heapFacts args[0]!
      for (hp, hh) in candidates do
        let attempt ← saveState
        try
          let hp ← Term.exprToSyntax hp
          let hh ← Term.exprToSyntax hh
          let value := mkIdent (← mkFreshUserName `permValue)
          let sourceEq := mkIdent (← mkFreshUserName `permSourceEq)
          let targetEq := mkIdent (← mkFreshUserName `permTargetEq)
          evalTactic (← `(tactic| res_step $hyp:ident with $value:ident $sourceEq:ident))
          if isLoad then
            let addr ← Term.exprToSyntax args[1]!
            let width ← Term.exprToSyntax args[2]!
            evalTactic (← `(tactic| have $targetEq:ident :=
              (Heap.loadB_perm_of_holds $hh:term $hp:term $addr:term $width:term).symm.trans $sourceEq:ident))
          else
            let target := mkIdent (← mkFreshUserName `permTarget)
            let relation := mkIdent (← mkFreshUserName `permRelation)
            let memory := mkIdent (← mkFreshUserName `permMemory)
            let holds := mkIdent (← mkFreshUserName `permHolds)
            evalTactic (← `(tactic| obtain ⟨$target:ident, $targetEq:ident, $relation:ident⟩ :=
              Heap.storeB_perm $hp:term $sourceEq:ident))
            evalTactic (← `(tactic| obtain ⟨$memory:ident, $holds:ident⟩ :=
              Heap.storeB_holds $hh:term $sourceEq:ident))
          -- A relation is selected only if its target operation occurs here.
          evalTactic (← `(tactic| rw [$targetEq:ident]))
          evalTactic (← `(tactic| dsimp only))
          return
        catch _ => attempt.restore
      throwError "heap_perm_step: no matching held/permuted heap facts for the target operation"
  catch error =>
    saved.restore
    throw error
end Lift.Tactic
