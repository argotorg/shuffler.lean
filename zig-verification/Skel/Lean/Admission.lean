import Lean

/-! Executable decisions for the premises of generated samplers. A contract can be an ordinary
definition with no `Decidable` instance of its own. Unfold proposition aliases before instance
search. Leave data terms unchanged. No classical decision is added. -/

namespace Skel.Admission

open Lean Meta Elab Term

/-- Prefer a list bound over enumeration of the element type, only for this decision. -/
private def withListDecisions {α : Type} (action : MetaM α) : MetaM α :=
  withoutModifyingEnv do
    addInstance ``List.decidableBAll .local (eval_prio high)
    resetSynthInstanceCache
    try action finally resetSynthInstanceCache

/-- Unfold proposition heads and visit their logical parts, without reducing data subterms. -/
private def unfoldPropositions (p : Expr) : MetaM Expr :=
  Meta.transform p (pre := fun e => do
    if ← isProp e then
      if (← synthInstance? (mkApp (mkConst ``Decidable) e)).isSome then
        return .done e
      if let some unfolded ← withTransparency .default (unfoldDefinition? e) then
        return .visit unfolded
      return .continue
    else
      match e with
      | .lam .. | .forallE .. => return .continue
      | _ => return .done e)

/-- An executable decision. An unsupported or noncomputable premise remains an error. -/
elab "skel_decide% " premise:term : term => do
  let p ← elabTermEnsuringType premise (mkSort .zero)
  let p ← instantiateMVars p
  let inst ← withListDecisions do
    match ← synthInstance? (mkApp (mkConst ``Decidable) p) with
    | some inst => pure inst
    | none => do
      let unfolded ← unfoldPropositions p
      synthInstance (mkApp (mkConst ``Decidable) unfolded)
  return mkApp2 (mkConst ``decide) p inst

end Skel.Admission
