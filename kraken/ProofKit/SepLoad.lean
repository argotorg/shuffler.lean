module

public import Kraken.MProp
import all Kraken.MProp
public import Lean.Elab.Tactic
import all Lean.Elab.Tactic

@[expose] public meta section

/-!
`sep_load [l₁, …, lₙ]` closes a load VC (`(m.loadInt a n).isSome = true`, or a value of a load)
from a separation hypothesis `h : (P ∗ F).get m` of the local context. For each such `h`, and for
each lemma `l`, it tries `with_reducible apply l h`, then closes all side goals with `assumption`.
The first pair that closes the goal wins. Untrusted: it only selects a lemma.

The order of the hypotheses: first the hypotheses at the memory term `m` of the first
`Mem.loadInt m a n` in the goal, then all other hypotheses, each group in the order of the context.
A hypothesis at another memory term can fit after a reducible unfold, so it stays in the search.
In a chain of stores, each store gives one hypothesis. In `dup_unit` (14 such hypotheses, 20 load
goals), this order decreases the heartbeats of the theorem from 112260 to 83564.

Two traps that this tactic avoids:
* In a tactic block, `apply l h` with an `h` that does not fit `l` logs an error, changes `l h` to
  `sorry` and closes the goal. A tactic that tries lemmas must not take this as a success.
  `Term.withoutErrToSorry` makes the error an exception. (In a test, this `elab` with no
  `Term.withoutErrToSorry` also skipped the lemma. The guard stays, because the prototype tactic saw
  the logged error.)
* A lemma for one atom on a hypothesis with another atom first makes `isDefEq` unfold both atoms.
  This can take a `whnf` timeout, which no `try` catches. `with_reducible` stops the unfold.
-/

open Lean Meta Elab Tactic

namespace ProofKit

/-- Try `with_reducible apply l h` and close the side goals with `assumption`. -/
def trySepLoad (l : Term) (h : Expr) : TacticM Bool := do
  let s ← saveState
  try
    let hs ← Term.exprToSyntax h
    Term.withoutErrToSorry <| evalTactic (← `(tactic|
      focus ((with_reducible apply $l $hs) <;> assumption) <;> done))
    return true
  catch _ =>
    s.restore
    return false

/-- The memory `m` of the first `Mem.loadInt m a n` in `e`. -/
def loadMem? (e : Expr) : Option Expr :=
  (e.find? (·.isAppOfArity ``Mem.loadInt 4)).map (·.getArg! 1)

elab "sep_load " "[" ls:term,* "]" : tactic => withMainContext do
  let m? := loadMem? (← instantiateMVars (← getMainTarget))
  let mut same := #[]
  let mut rest := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    unless t.isAppOf ``MProp.get do continue
    if m? == some t.appArg! then same := same.push d.toExpr else rest := rest.push d.toExpr
  for h in same ++ rest do
    for l in ls.getElems do
      if ← trySepLoad l h then return
  throwError "sep_load: no sep hyp gives this load"

end ProofKit
