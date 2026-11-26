module

public import Lift.Spike.Sites
public import Lift.Tactic.Simp
public import Lift.Tactic.SignedFlags
public import Lift.Tactic.SimState
public import Kraken.X64.Registers
public meta import Lean.Elab.Tactic

@[expose] public section

/-! `lift_block`: a first prototype of the tactic that proves a block lemma
`Reaches step policy Q ⟨d, pc⟩` (see `Lift/Spike/Sites/Sum.lean`).

Route A1 of `docs/research/lift-automation-literature-20261118.md`, section 4, with the site
lemma made inside the tactic at each step (no stored site equation):

1. `lift_exit`: if a hypothesis `h : c₁ → … → ∀ f, Q ⟨D f, pc⟩` has the `pc` of the goal, close
   the goal with `Reaches.done`; the state equation goes to `lift_state_eq`.
2. `lift_step`: `Reaches.of_step`; `whnf` of `step s` gives the site body (as the `show` of the
   site scripts); `simp [lift_site, lift_flag]` (as the site scripts); the execute check by
   `ExecRange` and `decide`; each load or store by its `readRam`/`writeRam` hypothesis
   (`lift_mem`); then the next state.
3. `split` on a PC `if c then a else b`.

What the tactic cannot close stays as a goal, with the hypotheses that the goal does not need
removed (`clearScaffold`): a missing access is `∃ v, readRam … = .ok v`; a state field that
`lift_side` does not prove is the field equation. -/

namespace Lift.Tactic

open Lift.P2.Total Lift.Sem

/-- The execute check of a site in the code range. -/
theorem exec_iff {M : Type} {policy : CpuPolicy} {lo hi : Int64} (h : SysV.ExecRange policy lo hi)
    {visible : DataMem → M} {prior : DataMem} {p : Std.Rco Int64} {k : Unit → Effects}
    {result : StepResult M} (hp : lo ≤ p.lower ∧ p.lower < p.upper ∧ p.upper ≤ hi) :
    Handled policy visible prior (.require_exec_access p k) result ↔
      Handled policy visible prior (k ()) result :=
  Lift.Spike.Sites.exec_iff h visible prior p k result hp

/-- An exit: `Q` holds at the state `t` if a hypothesis gives `Q` at `⟨D f, pc⟩` for each flag
value `f`, `pc` is the PC of `t`, and `D` with the flags of `t` is the data of `t`. -/
theorem exit_of {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop}
    {D : StatusFlags → MachineData} {pc : Int64} {t : MachineState}
    (hQ : ∀ f, Q ⟨D f, pc⟩) (hpc : pc = t.pc) (h : D t.data.status = t.data) :
    Reaches step policy Q t := by
  obtain ⟨d, p⟩ := t
  simp only at hpc h
  subst hpc
  exact .done (h ▸ hQ _)

/-! ## Simp sets -/

attribute [lift_site] BitVec.toAddressSize BitVec.signed BitVec.take BitVec.drop BitVec.ofInt_add
  BitVec.ofInt_mul UInt64.ofBitVec_toBitVec Int64.ofBitVec_toBitVec

attribute [lift_addr] UInt64.toBitVec_sub UInt64.toBitVec_add BitVec.sub_sub BitVec.add_assoc

/-- A branch of the step: one `done` with the branch in the PC. -/
@[lift_site] theorem ite_done (c : Prop) [Decidable c] (s t : MachineState) :
    (if c then Effects.done s else Effects.done t) = Effects.done (if c then s else t) := by
  split <;> rfl

@[lift_site] theorem ite_state (c : Prop) [Decidable c] (d : MachineData) (p q : Int64) :
    (if c then (⟨d, p⟩ : MachineState) else ⟨d, q⟩) = ⟨d, if c then p else q⟩ := by
  split <;> rfl

attribute [lift_flag] StatusFlags.zf_from_result StatusFlags.cf_from_result
  StatusFlags.from_result.Remaining.cf_mk

/-- `je` after `cmpq %y, %x`: `zf` is `x = y`. -/
@[lift_flag] theorem sub_beq_zero (x y : UInt64) :
    (x.toBitVec - y.toBitVec == BitVec.zero 64) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← UInt64.toBitVec_inj, BitVec.zero]
  exact Lean.Grind.AddCommGroup.sub_eq_zero_iff

/-! ## The tactic -/

open Lean Meta Elab Tactic

/-- The constants of the proof machinery: a hypothesis whose type has one of them is not kept in
a residual goal that does not use it. -/
meta def scaffold : List Name :=
  [``Reaches, ``Handled, ``readRam, ``writeRam, ``SysV.ExecRange]

/-- Remove from `g` each hypothesis that its target does not use and that is part of the proof
machinery (or is not a proposition and is unused), so that the goal stands alone. -/
meta def clearScaffold (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for _ in [0:2] do
    for ldecl in (← g.getDecl).lctx.decls.toList.reverse do
      let some ldecl := ldecl | continue
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let isProp ← g.withContext (Meta.isProp ty)
      let machinery := scaffold.any fun n => (ty.find? (·.isConstOf n)).isSome
      let qLike := ty.isForall && (ty.getForallBody.getAppFn.isFVar)
      if isProp && !(machinery || qLike) then continue
      try g ← g.clear ldecl.fvarId catch _ => pure ()
  return g

/-- Run a tactic on the goal `g` alone; the goals that stay. -/
meta def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  Term.withoutErrToSorry tac
  if (← instantiateMVars (mkMVar g)).hasSorry then
    throwError "lift_block: a step gave `sorry`"
  getGoals

/-- The side conditions: field equations of the exit state, conditions of an exit. -/
syntax "lift_side" : tactic
macro_rules
  | `(tactic| lift_side) =>
    `(tactic| first | rfl | assumption | ac_rfl | (simp only [lift_flag] at *; assumption) | grind)

/-- The state equation of an exit: one goal for each field that `lift_side` does not prove. -/
syntax "lift_state_eq" : tactic
macro_rules
  | `(tactic| lift_state_eq) =>
    `(tactic| (simp only [MachineData.mk.injEq, Reg64s.mk.injEq, and_true, true_and, and_self]
               all_goals (try and_intros)
               all_goals (try lift_side)))

/-- Each `OfNat.ofNat T v inst` whose value `v` evaluates to a numeral `n` becomes the numeral
`n : T` with its standard instance (the exact L1 has literals such as
`@OfNat.ofNat UInt64 (OfNat.ofNat 8) (UInt64.instOfNat Width.W64.bytes)`). -/
meta def normLits (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``OfNat.ofNat 3 then
      let v := x.getArg! 1
      if v.isRawNatLit then return .done x
      if let some n ← evalNat v then
        let ty := x.getArg! 0
        if ty.isConstOf ``Nat then return .done (mkNatLit n)
        try return .done (← mkNumeral ty n) catch _ => return .done x
    return .done x)

/-- Unfold `step s` in a hypothesis `Handled … (step s) r` to the site body, by `whnf`. -/
syntax "lift_unfold" " at " ident : tactic
elab_rules : tactic
  | `(tactic| lift_unfold at $h:ident) => withMainContext do
    let fv ← getFVarId h
    let ty ← instantiateMVars (← fv.getType)
    let_expr Handled M policy vis prior e res := ty
      | throwError "lift_unfold: not a `Handled` hypothesis{indentExpr ty}"
    let e' ← whnf e
    unless e'.isAppOf ``Effects.require_exec_access do
      throwError "lift_unfold: no site at this state{indentExpr e'}"
    let e' ← normLits e'
    let ty' := mkAppN ty.getAppFn #[M, policy, vis, prior, e', res]
    liftMetaTactic1 fun g => g.replaceLocalDeclDefEq fv ty'

/-- A hypothesis `readRam`/`writeRam` … ` = .ok u` that gives the access: the left side's
function, memory, width. -/
meta def accessHyps (fn : Name) : MetaM (Array (FVarId × Expr × Expr)) := do
  let mut out := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs.isAppOf fn && rhs.isAppOf ``Except.ok then
      out := out.push (ldecl.fvarId, lhs, rhs)
  return out

/-- Give the access of `e` (a load or a store of `D`) the proof `D`'s `readRam`/`writeRam` is
`.ok _`, from a hypothesis (`exact`, then `simpa [lift_addr]`), or a residual goal
`∃ v, … = .ok v`. Returns the proof and the residual goals. -/
meta def accessProof (policy e : Expr) : TacticM (Expr × List MVarId) := do
  let (fn, D, A, W, val?) ←
    if e.isAppOfArity ``MachineData.load 4 then
      pure (``readRam, e.getArg! 0, e.getArg! 1, e.getArg! 2, none)
    else if e.isAppOfArity ``MachineData.store 5 then
      pure (``writeRam, e.getArg! 0, e.getArg! 1, e.getArg! 2, some (e.getArg! 3))
    else throwError "lift_mem: not an access{indentExpr e}"
  let mem ← do
    let x := mkApp (mkConst ``MachineData.dmem) D
    let x' ← whnfR x
    pure (if x'.isProj then x else x')
  for (fv, lhs, rhs) in ← accessHyps fn do
    let args := lhs.getAppArgs
    -- `readRam policy mem a w`, `writeRam policy mem a w v`
    unless ← isDefEq args[3]! W do continue
    unless ← isDefEq args[1]! mem do continue
    let lhs' := mkAppN lhs.getAppFn <|
      match val? with
      | none => #[args[0]!, mem, A, W]
      | some v => #[args[0]!, mem, A, W, v]
    let target ← mkEq lhs' rhs
    let saved ← saveState
    try
      let m ← mkFreshExprMVar target
      let hstx ← Term.exprToSyntax (mkFVar fv)
      let rest ← runOn m.mvarId! (evalTactic (← `(tactic| first
        | exact $hstx
        | simpa only [lift_addr, lift_site] using $hstx
        | simpa [lift_addr, lift_site] using $hstx)))
      if rest.isEmpty then return (← instantiateMVars m, [])
      saved.restore
    catch _ => saved.restore
    -- The address up to `lift_addr` and ring arithmetic (`ac_rfl`, `grind`).
    try
      let e ← mkFreshExprMVar (← mkEq A args[2]!)
      let rest ← runOn e.mvarId! (evalTactic (← `(tactic|
        (try simp only [lift_addr, lift_site]) <;> first | rfl | ac_rfl | grind)))
      if rest.isEmpty then
        let e ← instantiateMVars e
        unless e.hasSyntheticSorry || e.hasSorry do
          -- `h : f a' = u`, `e : a = a'`: `f a = u`.
          let prf ← mkEqNDRec
            (← withLocalDeclD `x (← inferType A) fun x => do
              let l := mkAppN lhs'.getAppFn (lhs'.getAppArgs.set! 2 x)
              mkLambdaFVars #[x] (← mkEq l rhs))
            (mkFVar fv) (← mkEqSymm e)
          return (prf, [])
      saved.restore
    catch _ => saved.restore
  -- No hypothesis gives the access: a residual goal `∃ v, … = .ok v`.
  let lhs' := match val? with
    | none => mkAppN (mkConst fn) #[policy, mem, A, W]
    | some v => mkAppN (mkConst fn) #[policy, mem, A, W, v]
  let resTy ← whnfR (← inferType lhs')
  let_expr Except ε α := resTy | throwError "lift_mem: not an `Except` result{indentExpr resTy}"
  let ex ← withLocalDeclD `v α fun v => do
    let body ← mkEq lhs' (← mkAppOptM ``Except.ok #[ε, α, v])
    mkAppM ``Exists #[← mkLambdaFVars #[v] body]
  return (← mkFreshExprMVar ex, [])

/-- Remove each load and store of the hypothesis `h : Handled … e r` with its access proof. -/
syntax "lift_mem" " at " ident : tactic
elab_rules : tactic
  | `(tactic| lift_mem at $h:ident) => do
    let mut residual : List MVarId := []
    for _ in [0:16] do
      let (more, res) ← withMainContext do
        let ty ← instantiateMVars (← (← getFVarId h).getType)
        let_expr Handled _ policy _ _ e _ := ty | return (false, [])
        let e := e.headBeta
        unless e.isAppOf ``MachineData.load || e.isAppOf ``MachineData.store do return (false, [])
        let main ← getMainGoal
        let (prf, res) ← accessProof policy e
        let mut missing := res
        setGoals [main]
        let ds ← Term.exprToSyntax (e.getArg! 0)
        if e.isAppOf ``MachineData.load then
          match prf.isMVar, ← instantiateMVars prf with
          | true, _ =>
            -- No hypothesis gives the access: the residual goal `∃ v, … = .ok v`.
            let ts ← Term.exprToSyntax (← instantiateMVars (← inferType prf))
            evalTactic (← `(tactic| obtain ⟨_, hv⟩ : $ts))
            let miss :: main' :: _ ← getGoals | throwError "lift_mem: obtain"
            let miss :: _ ← runOn miss (evalTactic (← `(tactic|
                try simp only [lift_addr, lift_site, Width.bytes, BitVec.ofNat_eq_ofNat])))
              | throwError "lift_mem: residual"
            missing := missing ++ [← clearScaffold miss]
            setGoals [main']
            evalTactic (← `(tactic| replace $h := (Lift.Spike.Sites.load_iff _ $ds _ _ _ _ hv).mp $h))
          | false, prf =>
            let ps ← Term.exprToSyntax prf
            evalTactic (← `(tactic| replace $h := (Lift.Spike.Sites.load_iff _ $ds _ _ _ _ $ps).mp $h))
        else
          match prf.isMVar, ← instantiateMVars prf with
          | true, _ =>
            -- No hypothesis gives the access: the residual goal `∃ v, … = .ok v`.
            let ts ← Term.exprToSyntax (← instantiateMVars (← inferType prf))
            evalTactic (← `(tactic| obtain ⟨_, hv⟩ : $ts))
            let miss :: main' :: _ ← getGoals | throwError "lift_mem: obtain"
            let miss :: _ ← runOn miss (evalTactic (← `(tactic|
                try simp only [lift_addr, lift_site, Width.bytes, BitVec.ofNat_eq_ofNat])))
              | throwError "lift_mem: residual"
            missing := missing ++ [← clearScaffold miss]
            setGoals [main']
            evalTactic (← `(tactic| replace $h := (Lift.Spike.Sites.store_iff _ $ds _ _ _ _ _ hv).mp $h))
          | false, prf =>
            let ps ← Term.exprToSyntax prf
            evalTactic (← `(tactic| replace $h := (Lift.Spike.Sites.store_iff _ $ds _ _ _ _ _ $ps).mp $h))
        return (true, missing)
      residual := residual ++ res
      unless more do break
    setGoals ((← getGoals) ++ residual)

/-- One instruction: the goal `Reaches step policy Q s` becomes `Reaches step policy Q t` for the
next state `t` (or for each choice). -/
syntax "lift_step" : tactic
macro_rules
  | `(tactic| lift_step) =>
    `(tactic| (
      refine Lift.Sem.Reaches.of_step fun r hr => ?_
      lift_unfold at hr
      simp [lift_site, lift_flag] at hr
      replace hr := (Lift.Tactic.exec_iff ‹Lift.Sem.SysV.ExecRange _ _ _› (by decide)).mp hr
      lift_mem at hr
      simp only [Lift.P2.Total.Handled.done_iff, Lift.P2.Total.Handled.choice_iff, lift_site,
        UInt64.ofBitVec_toBitVec] at hr
      first | (obtain ⟨_, rfl⟩ := hr) | subst hr
      refine ⟨_, rfl, ?_⟩))

/-- Close an exit goal with a hypothesis that gives `Q` at its PC. Fails if no hypothesis has the
PC of the goal. -/
meta def liftExit (g : MVarId) : TacticM (List MVarId) := g.withContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let saved ← saveState
    try
      let hs ← g.apply (← mkConstWithFreshMVarLevels ``exit_of)
      let hQ :: hpc :: heq :: _ := hs | throwError "exit_of"
      let prem ← hQ.apply (mkFVar ldecl.fvarId)
      let [] ← runOn hpc (evalTactic (← `(tactic| first | rfl | decide)))
        | throwError "pc"
      let eqs ← runOn heq (evalTactic (← `(tactic| lift_state_eq)))
      let mut left := []
      for p in prem do
        let r ← runOn p (evalTactic (← `(tactic| try lift_side)))
        left := left ++ r
      return ← (left ++ eqs).mapM fun g => (clearScaffold g : MetaM MVarId)
    catch _ => saved.restore
  throwError "lift_exit: no exit hypothesis at this state"

/-- `lift_block`: exits, steps and PC splits, with at most `fuel` steps on each path. The goals
that stay are the residual side conditions. -/
syntax "lift_block" : tactic
elab_rules : tactic
  | `(tactic| lift_block) => do
    let fuel := 64
    let mut work : List (MVarId × Nat) := [(← getMainGoal, 0)]
    let mut out : List MVarId := []
    while true do
      match work with
      | [] => break
      | (g, n) :: rest =>
        work := rest
        if ← g.isAssigned then continue
        try
          out := out ++ (← liftExit g)
          continue
        catch _ => pure ()
        if n < fuel then
          let saved ← saveState
          try
            let gs ← runOn g (evalTactic (← `(tactic| lift_step)))
            work := gs.map (·, n + 1) ++ work
            continue
          catch _ => saved.restore
          try
            let gs ← runOn g (evalTactic (← `(tactic| split)))
            work := gs.map (·, n) ++ work
            continue
          catch _ => saved.restore
        out := out ++ [← clearScaffold g]
    setGoals out

end Lift.Tactic
