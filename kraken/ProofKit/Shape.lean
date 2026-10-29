import Kraken.StateCfg
import Kraken.KVCGen

/-!
VC shapes. `vcKind` reads the target of a goal that `kvcgen64` leaves and
gives its kind. The kind depends only on the head of the target, not on the
case name (`vc6`) that `vcgen` gives, so a new compile that adds or removes an
instruction does not change it. Untrusted: it only selects a tactic.
-/

open Lean Meta Elab Tactic

namespace ProofKit

/-- The kind of a VC. -/
inductive VcKind where
  /-- `(Mem.loadInt m a n).isSome = true`: a load or store is in mapped memory. -/
  | load
  /-- `t.retAddr.isSome = true`: `ret` can read its address. -/
  | retAddr
  /-- `Program.Intercept ls s₀ I' E (label l) t` with `l ∈ ls`: a jump to a label of the cfg. -/
  | goto (l : String)
  /-- `Program.Intercept ... t.retAddr.get! t'`: the return. -/
  | ret
  /-- `Program.Intercept` to another address: a jump out of the cfg. -/
  | jumpOut
  /-- `I' b j () t` after a fall-through: the invariant of the next block, and the variant. -/
  | fall
  /-- A closed proposition (no free variables): `decide` can close it. -/
  | closed
  /-- Other: flags, the post of the caller. -/
  | other
  deriving Repr, BEq, Inhabited

def VcKind.name : VcKind → String
  | .load => "load" | .retAddr => "retAddr" | .goto l => s!"goto {l}" | .ret => "ret"
  | .jumpOut => "jumpOut" | .fall => "fall" | .closed => "closed" | .other => "other"

/-- A string literal, also under `String.ofList`/`OfNat` noise. -/
def strLit? (e : Expr) : MetaM (Option String) := do
  if let .lit (.strVal s) := e then return some s
  let e ← whnfR e
  if let .lit (.strVal s) := e then return some s
  return none

/-- The kind of the target of `g`. -/
def vcKind (g : MVarId) : MetaM VcKind := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  -- `p.isSome = true`
  if let some (_, lhs, rhs) := t.eq? then
    if rhs.isConstOf ``Bool.true then
      if lhs.isAppOfArity ``Option.isSome 2 then
        let h := lhs.appArg!.getAppFn
        if h.isConstOf ``Mem.loadInt then return .load
        if h.isConstOf ``MachineData.retAddr then return .retAddr
  match_expr t with
  | Program.Intercept _ ls _ _ _ a _ =>
    match_expr a with
    | Labels.label _ l =>
      let some s ← strLit? l | return .jumpOut
      -- a label that is not in `ls` is outside the cfg
      if let some (_, es) := ls.listLit? then
        unless (← es.mapM strLit?).contains (some s) do return .jumpOut
      return .goto s
    | Option.get! _ _ x =>
      if x.isAppOfArity ``MachineData.retAddr 1 then return .ret else return .jumpOut
    | _ => return .jumpOut
  | And _ _ =>
    -- `I b s ∧ Program.Decreases ...` as `Program.WP.cfg` gives it for a fall-through
    if (← instantiateMVars t).find? (fun e => e.isAppOf ``Program.Decreases) |>.isSome then
      return .fall
    if t.hasFVar || t.hasMVar then return .other
    return .closed
  | _ =>
    if !t.hasFVar && !t.hasMVar then return .closed
    return .other

/-- Print the kind of each goal, one line each. -/
elab "vc_shapes" : tactic => do
  for g in ← getGoals do
    let k ← vcKind g
    let tag := (← g.getTag).toString
    let fmt ← g.withContext do ppExpr (← instantiateMVars (← g.getType))
    let s := (toString fmt).replace "\n" " "
    let s := if s.length > 90 then (s.take 90).toString ++ " …" else s
    logInfo m!"{tag}: {k.name} | {s}"

end ProofKit
