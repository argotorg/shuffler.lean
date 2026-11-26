import Lean

/-! `#contract_bounds C`: the constant bounds of the inputs of a contract `C` (task DISC-BOUND). The command reads the value
and the type of `C`, not their text.

The sources:
* `contract`: each conjunct `e ≤ K`, `e < K`, `K ≥ e` or `K > e` of the body of `C` (through `∧`), with `K` a term that reduces
  to a literal of `Nat` (`1024`, `2 ^ 64`) and `e` a term of the inputs. A loop register that holds `e`, or that starts at `e` and
  moves down, is below `K` at each head visit.
* `size`: the length `N` of each `Vector α N` that is an input of `C` or a field of a structure input: an index into the object
  is at most `N`.

A list input gives no bound: `n ≤ 2 ^ 61` for a list of `n` words holds, but the loop row has no hypothesis that gives it at the
entry (DISC-BOUND: with the atom `rcx ≤ 2 ^ 61` the goal `entry` of a sum that counts down stays open; without it the goal closes).

Each line of the output is one JSON object: `source`, `bound` (the number `K` or `N`) and `strict` (`true` for
`<`). No bound gives no line. -/

namespace Skel.BoundProbe

open Lean Meta Elab Command

/-- The value of `e` as a literal of `Nat`, after reduction. -/
def natValue? (e : Expr) : MetaM (Option Nat) := do
  let t ← inferType e
  unless ← isDefEq t (mkConst ``Nat) do return none
  let r ← reduce e
  pure (r.rawNatLit? <|> r.nat?)

/-- The conjuncts of `p`, through `∧`. -/
partial def conjuncts (p : Expr) : List Expr :=
  let p := p.consumeMData
  match p.getAppFnArgs with
  | (``And, #[a, b]) => conjuncts a ++ conjuncts b
  | _ => [p]

/-- The bound of one conjunct: `(K, strict)` for `e ≤ K`, `e < K`, `K ≥ e`, `K > e`. -/
def boundOf? (p : Expr) : MetaM (Option (Nat × Bool)) := do
  let side? (k : Expr) (strict : Bool) : MetaM (Option (Nat × Bool)) := do
    pure ((← natValue? k).map (·, strict))
  match p.getAppFnArgs with
  | (``LE.le, #[_, _, _, k]) => side? k false
  | (``LT.lt, #[_, _, _, k]) => side? k true
  | (``GE.ge, #[_, _, k, _]) => side? k false
  | (``GT.gt, #[_, _, k, _]) => side? k true
  | _ => pure none

/-- The bound of the object size of an input of the type `ty`: `size N` for `Vector α N`. -/
def sizeOf? (ty : Expr) : MetaM (Option (String × Nat)) := do
  let ty ← whnfR ty
  match ty.getAppFnArgs with
  | (``Vector, #[_, n]) => pure ((← natValue? n).map ("size", ·))
  | _ => pure none

/-- The object sizes of the binder `b`: its own, or those of the fields of a structure. -/
def sizesOf (b : Expr) : MetaM (List (String × Nat)) := do
  let ty ← whnfR (← inferType b)
  if let some s ← sizeOf? ty then return [s]
  let some sn := ty.getAppFn.constName? | return []
  unless isStructure (← getEnv) sn do return []
  (getStructureFields (← getEnv) sn).toList.filterMapM fun f => do sizeOf? (← inferType (← mkProjection b f))

/-- The line of one bound. -/
def line (source : String) (k : Nat) (strict : Bool) : String :=
  Json.compress (Json.mkObj [("source", Json.str source), ("bound", toJson k), ("strict", Json.bool strict)])

syntax "#contract_bounds " ident : command

elab_rules : command
  | `(#contract_bounds $id:ident) => liftTermElabM do
  let n ← realizeGlobalConstNoOverload id
  let some v := (← getConstInfo n).value? | throwError "{n} has no value"
  lambdaTelescope v fun bs body => do
    for p in conjuncts body do
      if let some (k, strict) ← boundOf? p then IO.println (line "contract" k strict)
    for b in bs do
      for (src, k) in ← sizesOf b do IO.println (line src k false)

end Skel.BoundProbe
