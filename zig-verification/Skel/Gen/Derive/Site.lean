import Lean
import Lift.Tactic.Block
import Lift.Tactic.Simp

/-! The site equations of an L1 program (task N1 of `docs/research/symexec-pilot-20261118.md`, section 5; decision D41:
the block terms come from the Kraken L1 semantics).

For the address `a` of a decoded instruction, `siteEq` adds the theorem `∀ d, step ⟨d, a⟩ = body`. The body is the
`simp` normal form of the `whnf` of the site of the table entry of `a`, after `Lift.Tactic.normLits`. The kernel checks
the theorem (`addDecl`, synchronous). Route E of `docs/research/symexec-derive-level2-20261118.md` then needs only
these theorems to unfold a block.

The function runs at the limits of its caller: it does not raise `maxRecDepth` or `maxHeartbeats` (`#lift_exact`
raises `maxRecDepth` to 20000). Each site has the whole `maxHeartbeats` budget. A site that passes a limit is an
error value that names the site and the limit. The `whnf` is of `site d`, not of `step ⟨d, a⟩`: the `whnf` of the
dispatch walks the table up to the entry, and its recursion depth grows with the index of the entry (at the default
`maxRecDepth` it fails at 34 of the 171 pilot sites and at 208 of the 347 level 2 sites). -/

open Lean Meta Elab Term Lift.P2.Total Lift.Sem

namespace Skel.Gen.Derive

/-- The limit of the elaborator that stopped a site, with its value. -/
inductive Limit where
  | maxRecDepth (limit : Nat)
  | maxHeartbeats (limit : Nat)
  deriving BEq, Repr

/-- Why a site has no equation. Each case names the address. -/
inductive SiteError where
  /-- The `whnf` of the step at this address is not a site (the address is not a decoded instruction). -/
  | notASite (addr : Nat)
  /-- The site passes a limit of the elaborator. -/
  | limit (addr : Nat) (which : Limit)
  /-- Any other error: the text of the message. -/
  | failed (addr : Nat) (msg : String)
  deriving BEq, Repr

/-- The site equation: the address, the name of the theorem, and the body as `fun d : MachineData => …`. -/
structure SiteEq where
  addr : Nat
  name : Name
  body : Expr

/-- The name of the theorem of a site: `pfx.site<addr>`, the address in decimal. -/
def siteName (pfx : Name) (addr : Nat) : Name := .str pfx s!"site{addr}"

/-- The simp set of the site bodies: the default set, `lift_site` and `lift_flag`. -/
def siteContext : MetaM Simp.Context := do
  let site ← (← getSimpExtension? `lift_site).get!.getTheorems
  let flag ← (← getSimpExtension? `lift_flag).get!.getTheorems
  Simp.mkContext (simpTheorems := #[← getSimpTheorems, site, flag])

/-- An entry `Prod.mk pc site` of the table: the `Int64` literal `pc` and the constant `site`. -/
private def entrySite (entry : Expr) : MetaM (Nat × Name) := do
  let_expr Prod.mk _ _ pc site := entry | throwError "table entry is not a pair{indentExpr entry}"
  let_expr OfNat.ofNat _ n _ := pc | throwError "table address is not a literal{indentExpr pc}"
  let some a ← evalNat n | throwError "table address is not a numeral{indentExpr pc}"
  let some c := site.constName? | throwError "table site is not a constant{indentExpr site}"
  return (a, c)

/-- The entries of the table of `step` (`dispatch table`, as `#lift_exact` makes it), in table order: the address and
the constant `site` of the entry. The walk reads the constants `table`, `tail0`, `tail1`, … (each one the value of
the one before, or a list cell) without `whnf`, so it does not pass a limit. -/
partial def tableSites (step : Name) : MetaM (List (Nat × Name)) := do
  let some ci := (← getEnv).find? step | throwError "unknown step {step}"
  let some v := ci.value? | throwError "step {step} has no value"
  let_expr Lift.P1.dispatch table := v | throwError "step {step} is not `dispatch table`{indentExpr v}"
  go table []
where
  go (e : Expr) (acc : List (Nat × Name)) : MetaM (List (Nat × Name)) := do
    let some c := e.constName? | throwError "table tail is not a constant{indentExpr e}"
    let some v := (← getEnv).find? c >>= (·.value?) | throwError "table tail {c} has no value"
    if v.isConst then return ← go v acc
    match_expr v with
    | List.nil _ => return acc.reverse
    | List.cons _ entry rest => go rest ((← entrySite entry) :: acc)
    | _ => throwError "table tail {c} is not a list{indentExpr v}"

/-- The equation for the address and the constant `site` of its table entry. The left side is `step ⟨d, addr⟩`; the
`whnf` is of `site d`, which is the same term for the kernel (`dispatch` takes the entry of this address). -/
private def addSite (step pfx : Name) (addr : Nat) (site : Name) : TermElabM (Option SiteEq) :=
  withLocalDeclD `d (mkConst ``MachineData) fun d => do
    let pc ← mkNumeral (mkConst ``Int64) addr
    let lhs ← mkAppM step #[← mkAppM ``MachineState.mk #[d, pc]]
    let w ← whnf (mkApp (mkConst site) d)
    unless w.isAppOf ``Effects.require_exec_access do return none
    let w ← Lift.Tactic.normLits w
    let (r, _) ← simp w (← siteContext) #[← Simp.getSimprocs]
    let prf ← mkEqTrans (← mkEqRefl lhs) (← r.getProof)
    let ty ← instantiateMVars (← mkForallFVars #[d] (← mkEq lhs r.expr))
    let v ← instantiateMVars (← mkLambdaFVars #[d] prf)
    let name := siteName pfx addr
    withOptions (fun o => Elab.async.set o false) do
      addDecl (.thmDecl { name, levelParams := [], type := ty, value := v })
    return some { addr, name, body := ← instantiateMVars (← mkLambdaFVars #[d] r.expr) }

/-- The equation of one site, or the error, given the entries of the table. An address that is not in the table is
`notASite`. -/
private def siteEqIn (step pfx : Name) (table : List (Nat × Name)) (addr : Nat) :
    TermElabM (Except SiteError SiteEq) :=
  withCurrHeartbeats do
    let ctx ← readThe Core.Context
    let some site := table.lookup addr | return .error (.notASite addr)
    tryCatchRuntimeEx
      (do match ← addSite step pfx addr site with
          | some e => pure (.ok e)
          | none => pure (.error (.failed addr "the whnf of the site is not a site")))
      fun ex => do
      if ex.isMaxRecDepth then pure (.error (.limit addr (.maxRecDepth ctx.maxRecDepth)))
      else if ex.isMaxHeartbeat then pure (.error (.limit addr (.maxHeartbeats (ctx.maxHeartbeats / 1000))))
      else pure (.error (.failed addr (← ex.toMessageData.toString)))

/-- The table, or none when the walk fails (an unknown step, or a step that is not `dispatch table`). The walk has the
whole `maxHeartbeats` budget, as each site has. -/
private def readTable (step : Name) : TermElabM (Option (List (Nat × Name))) :=
  withCurrHeartbeats <| tryCatchRuntimeEx (some <$> tableSites step) fun _ => pure none

private def noTable (step : Name) (addr : Nat) : Except SiteError SiteEq :=
  .error (.failed addr s!"cannot read the table of {step}")

/-- The equation of one site, or the error. The theorem `siteName pfx addr` is added to the environment. -/
def siteEq (step pfx : Name) (addr : Nat) : TermElabM (Except SiteError SiteEq) := do
  match ← readTable step with
  | some table => siteEqIn step pfx table addr
  | none => pure (noTable step addr)

/-- The equations of the sites at the addresses, in the order of the addresses. One error does not stop the others.
An unreadable table is `failed` at each address. -/
def siteEqs (step pfx : Name) (addrs : List Nat) : TermElabM (List (Except SiteError SiteEq)) := do
  match ← readTable step with
  | some table => addrs.mapM (siteEqIn step pfx table)
  | none => pure (addrs.map (noTable step))

end Skel.Gen.Derive
