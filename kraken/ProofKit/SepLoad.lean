import Kraken.MProp
import Lean.Elab.Tactic

/-!
`sep_load [l₁, …, lₙ]` closes a load VC (`(m.loadInt a n).isSome = true`, or a value of a load)
from a separation hypothesis `h : (P ∗ F).get m` of the local context. For each such `h`, and for
each lemma `l`, it tries `with_reducible apply l h`, then closes all side goals with `assumption`.
The first pair that closes the goal wins. Untrusted: it only selects a lemma.

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
private def trySepLoad (l : Term) (h : Expr) : TacticM Bool := do
  let s ← saveState
  try
    let hs ← Term.exprToSyntax h
    Term.withoutErrToSorry <| evalTactic (← `(tactic|
      focus ((with_reducible apply $l $hs) <;> assumption) <;> done))
    return true
  catch _ =>
    s.restore
    return false

elab "sep_load " "[" ls:term,* "]" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).consumeMData.isAppOf ``MProp.get do continue
    for l in ls.getElems do
      if ← trySepLoad l d.toExpr then return
  throwError "sep_load: no sep hyp gives this load"

end ProofKit
