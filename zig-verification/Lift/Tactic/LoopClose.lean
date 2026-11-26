module

public import Lift.Tactic.Loop
public import Lift.Tactic.LoopSimp
public import Lift.Tactic.HeapField
public import Lift.Tactic.HeapSlice
public import Lift.Tactic.HeapFrame
public import Lift.Tactic.FlagNorm
public import Lift.Tactic.SpecDecide
public import Lift.Tactic.SimState
public import Lift.Tactic.ArrayUpdate
public import Lift.Tactic.WordArith
public import Lift.Tactic.ResStep
public import Lift.Tactic.HeapStep
public import Lift.Tactic.BridgeStep
public import Lift.Sem.HeapBytes
public import Lift.Sem.HeapValueView
public import Lift.Tactic.HeapPermStepTyped
public import Lift.Tactic.HeapPartitionExact
public import Lift.Tactic.HeapPermStep
public import Lift.Sem.PermReplayAt
public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic

@[expose] public section

/-! `loop_close` and `lift_loop!`.

`loop_close` tries to close the main goal with one fixed sequence. It is for the goals that
`lift_loop` leaves (`Lift/Tactic/Loop.lean`), and it uses no name of a function, a field or a label:

1. split each hypothesis `h : p ∧ q` into two, then `subst` each equation `h : x = e` with `x` a
   local variable;
2. add `e.toNat < 2 ^ 64` for each `UInt64.toNat e` of the context and the goal, and `a.toNat = b.toNat`
   or `a.toNat ≠ b.toNat` for each hypothesis `a = b` or `¬ a = b` on `UInt64`; then the flag normal form
   (`Lift/Tactic/FlagNorm.lean`) on each hypothesis with a flag `(if c then 1 else 0)` or an order of a `UInt` or a
   `BitVec`: a Boolean combination of linear facts of `toNat`, whose conjunctions are split again;
3. `simp only [heap_norm, extra] at *`, with the names `extra` of `loop_close [extra]` (the definitions
   of the heap and of the spec): the heaps become lists of `Obj.words` and the frame; then each
   equation `h : e = l` of heaps whose left side is not a local variable (such as `a.heap = …` or
   `x.mem = …`) rewrites `e` to `l` in the other hypotheses and in the goal;
4. `simp only [heap_load, …] at *`: a load at an index inside an array of the heap rewrites to the
   word, so that the equation of a `stuck` or `noFuel` load becomes `False`, and the equation of an
   `ok` load gives the loaded value (then `subst` again); a store to the array gives the new array;
5. `simp only [uint_norm, list_step, extra, …]` on the goal; the side conditions of the rules go to
   `omega`;
6. `condNorm`: each `ite` or `dite` of the goal whose condition or its negation `cond_disch` proves (`decide`, `omega`, or
   `omega` after the casts of `UInt`, `bitvec_to_nat` and `toNat_allOnes`, with no heap hypothesis) takes its branch, by a rewrite of all its
   occurrences (also in a dependent argument); an equation of two applications of one constructor (the result `Field`)
   becomes the equations of the fields (`injEq`);
7. split each conjunction of the goal, also under binders and hypotheses (`∀ m, Holds h m → p ∧ q`); close each part with
   the first of `omega`, `rfl`, `bv_omega`,
   `ac_rfl`, `simp_all [uint_norm, list_step, extra]` (the hypotheses rewrite each other, so that an
   equation `a = e` decides a condition `b = e'` of the goal; the sums of `UInt64` are in the order of
   `add_comm`), `bv_norm`, and `bv_decide` (last: its proof has an axiom of its own). `bv_norm` rewrites
   each hypothesis and the goal with `uint_norm`, `list_step` and `bv_norm` (`Lift/Tactic/LoopSimp.lean`):
   an equation of `UInt64` becomes an equation of `BitVec 64`, `toBitVec` goes inside `+`, and a `drop`,
   `take`, `range` or fold of the list at the index takes one step (the side conditions go to `omega`); then
   the hypotheses rewrite each other, and `bv_omega` closes the part. Thus the form of the invariant and the
   result is free: the `+` inside or outside `ofBitVec`, `a + b = c` or `c - b = a`, `drop` or `take`.

When a part is not closed by any of them, `loop_close` splits a case (`splitCase`) and closes each new goal in the same way,
at most 3 splits of the whole goal and 2 of a part: a hypothesis `h : p ∨ q` (such as `x = 0 ∨ x ∈ chain …`) gives two goals;
a list that a hypothesis or the goal takes apart with a `match` (such as `WalkStatement.head ps`) gives the goals of `[]` and
`a :: l`, with the equations of the function applied. For `p ∈ Heap.chain h off q` and `Heap.ends h off q = true` in the
context, the facts `Heap.ends h off p = true` and `next p = 0 ∨ next p ∈ chain` are added (`addChainFacts`).

If a part is not closed, `loop_close` fails with an error and the goal is unchanged. Each step has
a budget of `stepBudget` heartbeats (a tenth of the default limit); a step that exceeds it counts as
failed. `set_option trace.loop_close true` shows the time and the heartbeats of each step and the step with the most heartbeats,
and each part that stays open.

A part with `Mem.has` goes to `heap_has` first.

`lift_loop! I μ out` is `lift_loop I μ out` and then `loop_close_all` on the goals that stay; `lift_loop! I μ out
[extra]` passes `extra` to `loop_close`. `loop_close_all` is `try loop_close` on each goal, but the `stuck` and the
`noFuel` goal of one step take one proof (see `evalLoopCloseAll`). The goals that `loop_close` does not close stay with their
names and their texts. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

initialize registerTraceClass `loop_close

/-- The heartbeats of one step, in the unit of the option `maxHeartbeats` (the default limit is 200000). -/
meta def stepBudget : Nat := 20000

/-- Split each hypothesis `h : p ∧ q` into `h_l : p` and `h_r : q`, until there is none. -/
meta partial def splitAnds (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``And 2 then
      let h := d.toExpr
      let (_, g) ← g.assertHypotheses #[
        { userName := d.userName.appendAfter "_l", type := ← inferType (← mkAppM ``And.left #[h]),
          value := ← mkAppM ``And.left #[h] },
        { userName := d.userName.appendAfter "_r", type := ← inferType (← mkAppM ``And.right #[h]),
          value := ← mkAppM ``And.right #[h] }]
      return ← splitAnds (← g.clear d.fvarId)
  return g

/-- Split each hypothesis `h : p ∧ q` or `h : ∃ x, p`, also when a definition hides it, until there is none. A
structure of proofs stays whole: the lemmas on the heap take it as one hypothesis. -/
meta partial def splitStructs (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfD (← instantiateMVars d.type)
    if ty.isAppOf ``And || ty.isAppOf ``Exists then
      let #[s] ← g.cases d.fvarId | return g
      return ← splitStructs s.mvarId
  return g

/-- `split_hyps`: split each hypothesis that is a conjunction or an existential, also when a definition hides it
(such as `SimArr xs a`). The new hypotheses have no names. It uses no name of a function, a field or a label. -/
syntax (name := splitHyps) "split_hyps" : tactic

@[tactic splitHyps] meta def evalSplitHyps : Tactic := fun _ => do
  replaceMainGoal [← splitStructs (← getMainGoal)]

/-- The subterms of `e` for which `p` holds and that have no loose bound variable. -/
meta def collect (p : Expr → Bool) (e : Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef (#[] : Array Expr)
  discard <| Meta.transform e (post := fun e => do
    if p e && !e.hasLooseBVars then r.modify fun a => if a.contains e then a else a.push e
    return .done e)
  r.get

/-- Each `UInt64.toNat n` of `e` with `n` a number as the number `n` (a definitional change): `omega` takes
`UInt64.toNat 0` of the fact `¬x.toNat = UInt64.toNat 0` of `¬x = 0` as an atom. -/
meta def litToNats (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    unless x.isAppOfArity ``UInt64.toNat 1 do return .done x
    let some n ← getUInt64Value? x.appArg! | return .done x
    return .done (mkNatLit n.toNat))

/-- Add the facts on `UInt64` that `omega` needs: see the top of the file. A fact that the context has
already is not added again. -/
meta def addUIntFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mut tys : Array Expr := #[← instantiateMVars (← g.getType)]
  let mut hyps : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let ty ← instantiateMVars d.type
      tys := tys.push ty
      hyps := hyps.push (d.toExpr, ty)
  let u64 := mkConst ``UInt64
  let mut facts : Array Expr := #[]
  for ty in tys do
    for e in ← collect (·.isAppOfArity ``UInt64.toNat 1) ty do
      facts := facts.push (← mkAppM ``UInt64.toNat_lt #[e.appArg!])
  for (h, ty) in hyps do
    if let some (α, _, _) := ty.eq? then
      if ← isDefEq α u64 then
        facts := facts.push (← mkAppM ``congrArg #[mkConst ``UInt64.toNat, h])
    else if let some p := ty.not? then
      if let some (α, a, b) := p.eq? then
        if ← isDefEq α u64 then
          let inj := mkApp2 (mkConst ``UInt64.toNat_inj) a b
          facts := facts.push (← mkAppM ``mt #[← mkAppM ``Iff.mp #[inj], h])
  let mut known : Array Expr := hyps.map (·.2)
  let mut g := g
  for f in facts do
    let ty ← litToNats (← inferType f)
    unless known.contains ty do
      known := known.push ty
      let (_, g') ← (← g.assert `hfact ty f).intro1P
      g := g'
  return g

/-- The facts on a chain that `simp` cannot use: for each hypothesis `hm : p ∈ Heap.chain h off q` and `he : Heap.ends h off q
= true`, add that the walk from `p` ends (`Heap.ends_of_mem_chain`) and that the next pointer of `p` is `0` or in the chain
(`Heap.next_mem_chain_or_zero`). A fact that the context has already is not added again. -/
meta def addChainFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mut hyps : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      hyps := hyps.push (d.toExpr, ← instantiateMVars d.type)
  let mut facts : Array Expr := #[]
  for (hm, tm) in hyps do
    unless tm.isAppOfArity ``Membership.mem 5 do continue
    let c := tm.getArg! 3
    unless c.isAppOfArity ``Lift.Sem.Heap.chain 3 do continue
    for (he, te) in hyps do
      let some (_, l, _) := te.eq? | continue
      unless l.isAppOfArity ``Lift.Sem.Heap.ends 3 && (List.range 3).all fun i => l.getArg! i == c.getArg! i do continue
      facts := facts.push (← mkAppM ``Lift.Sem.Heap.ends_of_mem_chain #[he, hm])
      facts := facts.push (← mkAppM ``Lift.Sem.Heap.next_mem_chain_or_zero #[he, hm])
  let mut known : Array Expr := hyps.map (·.2)
  let mut g := g
  for f in facts do
    let ty ← inferType f
    unless known.contains ty do
      known := known.push ty
      let (_, g') ← (← g.assert `hchainfact ty f).intro1P
      g := g'
  return g

/-- The subterms of `e` for which `p` gives a result, and that have no loose bound variable. -/
meta def collectM {α : Type} (p : Expr → MetaM (Option α)) (e : Expr) : MetaM (Array α) := do
  let r ← IO.mkRef (#[] : Array α)
  discard <| Meta.transform e (post := fun e => do
    if !e.hasLooseBVars then
      if let some a ← p e then r.modify (·.push a)
    return .done e)
  r.get

/-- A list `l` that `e` takes apart: `e` is `match l with …`, or `f … l` with `f` a definition by `match` on its last
argument; `l` is not a constructor application, and its local variables are in `lctx`. The result is `l` and the equations
of `f` (none for a `match`), which reduce `f` on a constructor. -/
meta def listMatch? (lctx : LocalContext) (e : Expr) : MetaM (Option (Expr × Array Name)) := do
  let isList (l : Expr) : MetaM Bool := do
    if (l.find? fun f => f.isFVar && !lctx.contains f.fvarId!).isSome then return false
    if (← isConstructorApp? l).isSome then return false
    return (← whnfR (← inferType l)).isAppOf ``List
  if let some m ← matchMatcherApp? e then
    if let some l := m.discrs.find? (·.isFVar) then
      if ← isList l then return some (l, #[])
    return none
  let .const f _ := e.getAppFn | return none
  if e.getAppNumArgs == 0 then return none
  let l := e.appArg!
  unless ← isList l do return none
  let some (.defnInfo ci) := (← getEnv).find? f | return none
  let onLast ← lambdaTelescope ci.value fun xs body => do
    let some m ← matchMatcherApp? body | return false
    return xs.size == e.getAppNumArgs && m.discrs.back? == xs.back?
  unless onLast do return none
  let some eqns ← Meta.getEqnsFor? f | return none
  return some (l, eqns)

/-- The case split of a goal: on a hypothesis `h : p ∨ q` (for example `x ∈ chain …` or `x = 0`); else on a list that a
hypothesis or the goal takes apart with a `match` (a local variable, or a term, which `cases h : l` generalizes). The new goals have the equations of the function that took the list apart applied. `none` when there is nothing
to split. -/
meta def splitCase (g : MVarId) : TacticM (Option (List MVarId)) := do
  let g ← splitAnds g
  let (lctx, tys) ← g.withContext do
    let lctx ← getLCtx
    let mut tys : Array Expr := #[← instantiateMVars (← g.getType)]
    for d in lctx do
      unless d.isImplementationDetail do tys := tys.push (← instantiateMVars d.type)
    return (lctx, tys)
  if let some gs ← g.withContext do
      for d in lctx do
        if d.isImplementationDetail then continue
        if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``Or 2 then
          return some ((← g.cases d.fvarId).toList.map (·.mvarId))
      return none then
    return some gs
  g.withContext do
    for ty in tys do
      if let some (l, eqns) := (← collectM (listMatch? lctx) ty)[0]? then
        let ids ← eqns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
        setGoals [g]
        if l.isFVar then
          evalTactic (← `(tactic| cases $(← Term.exprToSyntax l):term))
        else
          evalTactic (← `(tactic| cases hlist : $(← Term.exprToSyntax l):term))
        let mut out := []
        for s in ← getGoals do
          setGoals [s]
          evalTactic (← `(tactic| simp -failIfUnchanged only [$ids,*, List.forall_mem_cons] at *))
          out := out ++ (← getGoals)
        return some out
    return none

/-- Whether `e` is a local variable (a `subst` takes such an equation). -/
meta def isLocal (e : Expr) : Bool := e.isFVar

/-- Rewrite with each equation `h : e = l` of heaps (`Lift.Sem.Heap`) whose left side `e` is not a local variable and does
not occur in `l`: `e` becomes `l` in each other hypothesis and in the goal. -/
meta def rewriteHeapEqs (g : MVarId) : MetaM MVarId := do
  let heapTy := mkConst ``Lift.Sem.Heap
  -- One rewrite at a time: a rewrite of a hypothesis gives new names to the hypotheses after it.
  let next (g : MVarId) : MetaM (Option (FVarId × Option FVarId)) := g.withContext do
    let lctx ← getLCtx
    let tgt ← instantiateMVars (← g.getType)
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (α, lhs, rhs) := ty.eq? | continue
      if isLocal lhs || (rhs.find? (· == lhs)).isSome then continue
      unless ← isDefEq α heapTy do continue
      for d' in lctx do
        if d'.isImplementationDetail || d'.fvarId == d.fvarId then continue
        if ((← instantiateMVars d'.type).find? (· == lhs)).isSome then
          return some (d.fvarId, some d'.fvarId)
      if (tgt.find? (· == lhs)).isSome then return some (d.fvarId, none)
    return none
  let mut g := g
  for _ in [0:100] do
    let some (h, at?) ← next g | return g
    g ← g.withContext do
      match at? with
      | some d =>
        let r ← g.rewrite (← instantiateMVars (← d.getType)) (mkFVar h)
        return (← g.replaceLocalDecl d r.eNew r.eqProof).mvarId
      | none =>
        let r ← g.rewrite (← instantiateMVars (← g.getType)) (mkFVar h)
        g.replaceTargetEq r.eNew r.eqProof
  return g

/-- Replace each projection of a defined constant applied to arguments, such as `(f a).field`, by the
field of the constructor that the definition gives (`simp only` does not unfold a definition that it is
not told about). -/
meta def reduceProjDefs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const fn _ := e.getAppFn | return .done e
    let some info ← getProjectionFnInfo? fn | return .done e
    -- `decide` of an instance stays: `instDecidableEqBitVec a b` reduces to the decision of `a.toFin = b.toFin`, whose atoms
    -- `bv_decide` does not take.
    if info.ctorName == ``Decidable.intro || e.getAppNumArgs != info.numParams + 1 then return .done e
    let s := e.appArg!
    let .const sf _ := s.getAppFn | return .done e
    if (← getEnv).isConstructor sf || (← getProjectionFnInfo? sf).isSome then return .done e
    let s ← whnfD s
    let some c ← isConstructorApp? s | return .done e
    return .done (s.getArg! (c.numParams + info.i)))

/-- The log of the steps: the name, the time in milliseconds, the heartbeats (in the unit of `maxHeartbeats`), and the
result (`done`, or the error). -/
abbrev StepLog := IO.Ref (Array (String × Nat × Nat × String))

/-- Run `tac`; on any exception, including a heartbeat limit, undo it and give `false`. The budget is
`stepBudget` heartbeats. The time and the result go to `log`. -/
meta def step (log : StepLog) (name : String) (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  let r ← tryCatchRuntimeEx
    (Core.withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := Nat.min c.maxHeartbeats (stepBudget * 1000) })
      (do tac; return none))
    (fun e => do
      let msg ← e.toMessageData.toString
      saved.restore
      return some msg)
  let t1 ← IO.monoMsNow
  let h1 ← IO.getNumHeartbeats
  log.modify (·.push (name, t1 - t0, (h1 - h0) / 1000, r.getD "done"))
  return r.isNone

/-- `unfold_bv_consts`: unfold in the goal each constant with no argument and no universe whose type is `BitVec w` (a
constant of a spec, such as `none64 := BitVec.allOnes 64`), so that `bv_omega` sees its value. It fails if there is none. -/
syntax (name := unfoldBvConsts) "unfold_bv_consts" : tactic

@[tactic unfoldBvConsts] meta def evalUnfoldBvConsts : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let env ← getEnv
    let names := tgt.getUsedConstants.filter fun c => match env.find? c with
      | some (.defnInfo ci) => ci.levelParams.isEmpty && ci.type.isAppOfArity ``BitVec 1
      | _ => false
    if names.isEmpty then throwError "unfold_bv_consts: no constant of type BitVec"
    replaceMainGoal [← g.replaceTargetDefEq (← deltaExpand tgt names.contains)]

/-- `cond_prep`: clear each hypothesis on a heap (`Heap`, `Obj`, `Mem.has`): a condition of a spec is a fact of numbers, and
the `simp … at *` of `cond_disch` costs the most on the lists of objects. It does not fail. -/
syntax (name := condPrep) "cond_prep" : tactic

@[tactic condPrep] meta def evalCondPrep : Tactic := fun _ => do
  let g ← getMainGoal
  let heapConsts := [``Lift.Sem.Heap, ``Lift.Sem.Obj, ``Lift.Trusted.Mem.has]
  let fvars ← g.withContext do
    let mut fvars := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if (t.find? fun x => heapConsts.any x.isConstOf).isSome then fvars := fvars.push d.fvarId
    return fvars
  replaceMainGoal [← g.tryClearMany fvars]

/-- `unfold_objs`: unfold in the goal each application of a definition whose value is an `Object` (such as `cellsObj xs p` of
a statement, which `loop_close` is not given), so that `heap_obj_mem` sees its fields. It fails if there is none. -/
syntax (name := unfoldObjs) "unfold_objs" : tactic

@[tactic unfoldObjs] meta def evalUnfoldObjs : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let objTy := mkConst ``Lift.Trusted.Object
    let tgt' ← Meta.transform tgt (post := fun e => do
      let .const fn _ := e.getAppFn | return .done e
      let some (.defnInfo _) := (← getEnv).find? fn | return .done e
      if e.hasLooseBVars then return .done e
      let ty ← try instantiateMVars (← inferType e) catch _ => return .done e
      unless ty == objTy do return .done e
      let some v ← unfoldDefinition? e | return .done e
      return .visit v.headBeta)
    if tgt' == tgt then throwError "unfold_objs: no definition of an object"
    replaceMainGoal [← g.replaceTargetDefEq tgt']

/-- `decide_closed`: `decide` on a goal with no local variable (a condition of constants); else it fails at once. -/
syntax (name := decideClosed) "decide_closed" : tactic

@[tactic decideClosed] meta def evalDecideClosed : Tactic := fun _ => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  if t.hasFVar || t.hasMVar then throwError "decide_closed: the goal has a local variable"
  evalTactic (← `(tactic| decide))

/-- `cond_disch`: the proof of a condition of an `ite` or a `dite`, or of its negation, from the context with no heap
(`cond_prep`): `decide` (a closed condition), `omega` (linear facts of `toNat`), or `omega` after the constants of type
`BitVec` and the casts of `UInt` go to `BitVec` (`bv_norm`) and `BitVec` goes to `toNat` (`bitvec_to_nat`, with the widths
`Width.W8.bits` as numbers: a load of 8 bits has a value of `BitVec Width.W8.bits`; and `toNat_allOnes`: a constant
`none64 := allOnes 64` of a spec, which `omega` otherwise takes as an atom), or `spec_decide` (a condition on the fields of a
spec type from the words of its encoding, `Lift/Tactic/SpecDecide.lean`). -/
syntax "cond_disch" : tactic
macro_rules
  | `(tactic| cond_disch) => `(tactic| (cond_prep; first
      | assumption | decide_closed | omega
      | (simp only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod]; omega)
      | ((try unfold_bv_consts) <;> (try simp only [bv_norm, UInt64.toNat_toBitVec, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *) <;>
         (try simp -implicitDefEqProofs only [bitvec_to_nat, BitVec.toNat_allOnes, _root_.Width.bits, UInt64.toNat_toBitVec,
           Nat.reducePow, Nat.reduceSub] at *) <;> omega)
      | spec_decide))

/-- Run `tac` on a new goal `e`; the proof, if `tac` closes it. A proof with `sorryAx` does not count (a tactic can log its
error and admit the goal). The state is as before if there is no proof. -/
meta def proveBy (tac : TSyntax `tactic) (e : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  let run : MetaM (Option Expr) := do
    let m ← mkFreshExprSyntheticOpaqueMVar e
    let gs ← (Term.withoutErrToSorry (Tactic.run m.mvarId! (Tactic.withoutRecover (evalTactic tac)))).run'
    let pf ← instantiateMVars m
    return if gs.isEmpty && !pf.hasSorry && !pf.hasExprMVar then some pf else none
  let r ← try run catch ex => do
    trace[loop_close] "no proof of {e}: {ex.toMessageData}"
    pure none
  if r.isNone then s.restore
  return r

/-- Rewrite each `ite` or `dite` of the goal whose condition `c` (or `¬c`) `cond_disch` proves to its branch, with
`ite_eq_left` (or `_right`) for all its occurrences at once: a `rw`, not a `simp`, so also inside a dependent argument (the
field `out : Vector _ cap.toNat` of `(dite c t e).snd`). The outer `ite` first: its branch can drop an inner one. Each
condition is tried once. -/
meta def rewriteConds (g : MVarId) : MetaM MVarId := do
  let tac ← `(tactic| cond_disch)
  let mut g := g
  let mut failed : Array Expr := #[]
  for _ in [0:32] do
    let next ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      for x in (← collect (fun x => x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5) tgt).reverse do
        let c := x.getArg! 1
        if failed.contains c then continue
        let lemmas := if x.isAppOfArity ``ite 5 then (``ite_eq_left, ``ite_eq_right) else (``dite_eq_left, ``dite_eq_right)
        let args (pf : Expr) := #[some c, some (x.getArg! 2), some pf, some (x.getArg! 0), some (x.getArg! 3), some (x.getArg! 4)]
        let eq? ← match ← proveBy tac c with
          | some pf => pure (some (← mkAppOptM lemmas.1 (args pf)))
          | none => match ← proveBy tac (mkNot c) with
            | some pf => pure (some (← mkAppOptM lemmas.2 (args pf)))
            | none => pure none
        let some eq := eq? | return some (Sum.inl c)
        try
          let r ← g.rewrite tgt eq
          return some (Sum.inr (← g.replaceTargetEq r.eNew r.eqProof))
        catch _ => return some (Sum.inl c)
      return none
    match next with
    | none => return g
    | some (.inl c) => failed := failed.push c
    | some (.inr g') => g := g'
  return g

/-- The rules of the `simp` of `condNorm`: `True` and `False` conditions, and the equations of the fields after a constructor
equation. -/
meta def condRules : Array Name :=
  #[``ite_true, ``ite_false, ``dite_true, ``dite_false, ``eq_self_iff_true, ``heq_eq_eq, ``true_and, ``and_true]

/-- The `injEq` theorems of the equations of `e` whose two sides are applications of one constructor. -/
meta def ctorInjEqs (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let r ← IO.mkRef (#[] : Array Name)
  Meta.forEachExpr e fun x => do
    let some (_, l, r') := x.eq? | return
    let .const c _ := l.getAppFn | return
    unless r'.getAppFn.isConstOf c && env.isConstructor c do return
    let n := Name.str c "injEq"
    if env.contains n then r.modify fun a => if a.contains n then a else a.push n
  r.get

/-- The conditions of the goal: `rewriteConds`, then a `simp` with `condRules` and the `injEq` theorems of the goal
(`ctorInjEqs`). `none` if the goal is closed; an error if nothing changes. -/
meta def condNorm (g : MVarId) : TacticM (Option MVarId) := do
  let g' ← rewriteConds g
  g'.withContext do
    let mut thms : SimpTheorems := {}
    for n in condRules ++ (← ctorInjEqs (← instantiateMVars (← g'.getType))) do
      thms ← thms.addConst n
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← simpTarget g' ctx
    if r == some g then throwError "cond-norm: no change"
    return r

/-- The closers of one part of a goal, in order; the last one uses the names `extra`. -/
meta def closers (extra : Array Term) : TacticM (Array (String × TSyntax `tactic)) := do
  let args ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  -- The rewrites of `bv_norm`: in each hypothesis and the goal, with `omega` for the side conditions (`norm`), and
  -- with the hypotheses that rewrite each other (`normAll`, which takes no discharger).
  let norm ← `(tactic| simp -failIfUnchanged (disch := (first | assumption | omega |
      (simp only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod]; omega)))
    only [uint_norm, list_step, bv_norm, Nat.reducePow, Nat.reduceMod, ↓reduceIte, $args,*] at *)
  let normAll ← `(tactic| simp_all -failIfUnchanged
    only [uint_norm, list_step, bv_norm, Nat.reducePow, Nat.reduceMod, ↓reduceIte, $args,*])
  return #[
  ("heap_frame", ← `(tactic| heap_frame)),
  ("omega", ← `(tactic| omega)), ("rfl", ← `(tactic| rfl)), ("bv_omega", ← `(tactic| bv_omega)),
  ("ac_rfl", ← `(tactic| ac_rfl)),
  ("simp_all", ← `(tactic| (simp_all only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
      UInt64.add_comm, UInt64.add_left_comm', $args,*]
    <;> first | done | ac_rfl | omega))),
  ("bv_norm", ← `(tactic| (intros; $norm <;> $normAll <;> $norm <;> first | done | bv_omega | omega))),
  -- A `Mem.has` part: the object is in a heap that a hypothesis holds (`Lift/Tactic/HeapField.lean`).
  -- `∀ m, Holds h m → ∀ o ∈ [o₁, …], Mem.has m o` is one part for each object.
  ("heap_has", ← `(tactic|
    ((try simp only [List.forall_mem_cons, List.forall_mem_nil, List.not_mem_nil, false_implies, imp_and, forall_and, and_true,
      implies_true])
     (repeat' refine And.intro ?_ ?_); all_goals (intros; (try unfold_objs); heap_has)))),
  -- A fact of numbers with a constant of type `BitVec` of a spec (`x = ofBitVec none64` from `x.toNat = 2 ^ 64 - 1`).
  ("cond_disch", ← `(tactic| cond_disch)),
  ("bv_decide", ← `(tactic| bv_decide (config := { timeout := 10 })))]

/-- Close the main goal, one part of a goal, with the first closer that does it. If there is none, split a list that a
hypothesis or the goal takes apart (`splitCase`) and close each new goal in the same way, at most `fuel` splits deep.
The state is as before if the result is `false`. -/
meta partial def closePart (log : StepLog) (extra : Array Term) (fuel : Nat) : TacticM Bool := do
  let g ← getMainGoal
  setGoals [g]
  trace[loop_close] "part:{indentD (MessageData.ofGoal g)}"
  let mut closed := false
  -- A `Mem.has` part goes to `heap_has` first: the other closers do not close it, and their failures cost the most.
  let cs ← closers extra
  let cs := if ((← instantiateMVars (← g.getType)).find? (·.isConstOf ``Lift.Trusted.Mem.has)).isSome then
      cs.filter (·.1 == "heap_has") ++ cs.filter (·.1 != "heap_has") else cs
  for (name, c) in cs do
    unless closed do
      closed ← step log name do
        evalTactic c
        unless (← getGoals).isEmpty do throwError "goals remain"
  if closed then return true
  if fuel == 0 then return false
  let saved ← saveState
  let some gs ← (try splitCase g catch _ => do saved.restore; pure none) | return false
  trace[loop_close] "case split of a part: {gs.length} goals"
  for g' in gs do
    setGoals [g']
    unless ← closePart log extra (fuel - 1) do
      saved.restore
      return false
  setGoals []
  return true

/-- Whether the goal or a hypothesis has one of the constants `names`. -/
meta def hasConsts (names : List Name) (g : MVarId) : MetaM Bool := g.withContext do
  let has (e : Expr) : MetaM Bool := return ((← instantiateMVars e).find? fun x => names.any x.isConstOf).isSome
  if ← has (← g.getType) then return true
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← has d.type) then return true
  return false

/-- Whether the goal has the constant `n`. -/
meta def hasConst (n : Name) (g : MVarId) : MetaM Bool := do
  return ((← instantiateMVars (← g.getType)).find? (·.isConstOf n)).isSome

/-- Whether the goal or a hypothesis has a typed heap (`Heap`, `Obj`, `toObj`, or a load or a store of a heap). -/
meta def hasToObj (g : MVarId) : MetaM Bool :=
  hasConsts [``Lift.Sem.Heap, ``Lift.Sem.Obj, ``Lift.Sem.Bridge.toObj, ``Lift.Sem.Heap.load, ``Lift.Sem.Heap.store,
    ``Lift.Sem.Heap.loadB, ``Lift.Sem.Heap.storeB] g

/-- The names of the hypotheses of the main goal with a load or a store of a heap; a hypothesis with no source name gets
one (`hacc_i`), so that a `simp ... at` can name it. -/
meta def heapAccessHyps : TacticM (Array Ident) := do
  let consts := [``Lift.Sem.Heap.load, ``Lift.Sem.Heap.store, ``Lift.Sem.Heap.loadB, ``Lift.Sem.Heap.storeB]
  let mut g ← getMainGoal
  let mut names := #[]
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless (t.find? fun x => consts.any x.isConstOf).isSome do continue
    -- a name with macro scopes, or the name of a later hypothesis too, does not name `d`
    let found := ((← g.getDecl).lctx.findFromUserName? d.userName).map (·.fvarId)
    if d.userName.hasMacroScopes || found != some d.fvarId then
      let n := Name.mkSimple s!"hacc_{names.size}"
      g ← g.rename d.fvarId n
      names := names.push (mkIdent n)
    else
      names := names.push (mkIdent d.userName)
  replaceMainGoal [g]
  return names

/-- The terms `t - k` of type `Nat` of `e`, with `k` a number above 0 and `t` not a number; for each `t` the largest `k`. -/
meta def natSubs (e : Expr) : MetaM (Array (Expr × Nat)) := do
  let r ← IO.mkRef (#[] : Array (Expr × Nat))
  Meta.forEachExpr e fun x => do
    unless x.isAppOfArity ``HSub.hSub 6 && !x.hasLooseBVars && (x.getArg! 0).isConstOf ``Nat do return
    let some k := (x.getArg! 5).nat? | return
    let t := x.getArg! 4
    if k == 0 || t.nat?.isSome then return
    r.modify fun a => match a.findIdx? (·.1 == t) with
      | some i => a.modify i fun (t', k') => (t', max k k')
      | none => a.push (t, k)
  r.get

/-- `pred-shift`: for each term `t - k` of the goal or a hypothesis (`natSubs`) with `k ≤ t` (`omega`), a new `j` with `t = j + k`, which
rewrites `t` in each hypothesis and the goal; then `j + k - k` is `j`. The index `i - 1` of a loop that counts down becomes
`j`, and the prefix `take i` becomes `take (j + 1)`, which `list_step` takes apart. It fails if no term is rewritten. -/
meta def predShift : TacticM Unit := do
  -- The goal and the hypotheses: the load at `i - 1` of a hypothesis goes with the prefix `take i` of the goal.
  let subs ← (← getMainGoal).withContext do
    let mut es := #[← instantiateMVars (← (← getMainGoal).getType)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
    let mut out : Array (Expr × Nat) := #[]
    for e in es do
      for (t, k) in ← natSubs e do
        out := match out.findIdx? (·.1 == t) with
          | some i => out.modify i fun (t', k') => (t', max k k')
          | none => out.push (t, k)
    pure out
  let mut done := false
  for (t, k) in subs do
    let g ← getMainGoal
    let ok ← g.withContext do
      return (← proveBy (← `(tactic| omega)) (← mkAppM ``LE.le #[mkNatLit k, t])).isSome
    unless ok do continue
    g.withContext do
      let ts ← Term.exprToSyntax t
      let ks := Syntax.mkNumLit (toString k)
      let j := mkIdent `j
      let hj := mkIdent `hshift
      evalTactic (← `(tactic| obtain ⟨$j, $hj⟩ : ∃ j, $ts = j + $ks := ⟨$ts - $ks, by omega⟩))
      evalTactic (← `(tactic| simp -failIfUnchanged only [$hj:ident, Nat.add_sub_cancel] at *))
    done := true
    if (← getGoals).isEmpty then return
  unless done do throwError "pred-shift: no term t - k with k ≤ t"

/-- Steps 1 to 7 of the top of the file on the main goal, with the names `extra`; `true` if the goal is closed. -/
meta def attemptClose (log : StepLog) (extra : Array Term) : TacticM Bool := do
  let args ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let prep : TacticM Unit := do
    let g ← getMainGoal
    let g ← splitAnds g
    let g ← substVars g
    replaceMainGoal [← addChainFacts (← addUIntFacts g)]
  -- `x + 18446744073709551615` of `UInt64` as `x - 1` (`UInt64.add_lit_eq_sub`): a proof by a rewrite, not by definition.
  let simpNorm ← `(tactic| simp (disch := decide) only [heap_norm, Option.some.injEq, Option.getD_some, UInt64.add_lit_eq_sub,
    Nat.reducePow, Nat.reduceSub, $args,*] at *)
  -- `assumption` at the default transparency unfolds the numbers of 64 bits of a side condition such as
  -- `(i.toBitVec + 18446744073709551615).toNat < n` against `i.toNat ≤ n` (maximum recursion depth, which `first` does not
  -- catch): it runs at the reducible transparency first, and at the default one last.
  let simpHyps ← `(tactic| simp (disch := (first | with_reducible assumption | decide | omega | heap_mem | (simp only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod]; omega) | assumption))
    only [heap_load, uint_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Lift.Sem.Res.ok.injEq, reduceCtorEq, exists_eq',
      not_true_eq_false, Option.ite_none_right_eq_some, Option.some.injEq] at *)
  let simpGoal ← `(tactic| simp (disch := (first | with_reducible assumption | decide | omega | (simp only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod]; omega) | assumption))
    only [uint_norm, list_step, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Lift.Sem.Res.ok.injEq, eq_self, and_self,
      and_true, true_and, ↓reduceIte, *, $args,*])
  -- A conjunction under binders and hypotheses (`∀ m, Holds h m → p ∧ q`, the post of a result) splits too.
  let split ← `(tactic| ((try simp only [imp_and, forall_and]); repeat' refine And.intro ?_ ?_))
  let simpFieldNorm ← `(tactic| simp only [heap_field, natOffGet, natOffSet, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, $args,*] at *)
  -- Only the hypotheses with a load or a store, and the goal (`heapAccessHyps`): the other hypotheses (`Holds`, sizes, bounds)
  -- have no access for the rules. The discharger `heap_disch` runs only the tactic of the form of each side condition.
  let simpFields : TacticM Unit := do
    let hs ← heapAccessHyps
    evalTactic (← `(tactic| simp (disch := heap_disch)
      only [Lift.Sem.Heap.load_of_found, Lift.Sem.Heap.loadB_of_found, Lift.Sem.Heap.store_of_storeAt,
        Lift.Sem.Heap.storeB_of_storeAt, Lift.Sem.Heap.storeB_of_storeSpanAt, heap_field, bvOffToNat, natOffGet,
        natOffSet, Lift.Sem.Res.ok.injEq, reduceCtorEq, exists_eq', not_true_eq_false, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceSub, $args,*] at $hs* ⊢))
  -- `has_of_holds_mem` has the heap only in its hypothesis, so `simp` cannot rewrite with it: each `Mem.has` part takes
  -- the `Holds` of a hypothesis, then `heap_obj_mem`. The step closes the goal or changes nothing.
  -- A part with no `Mem.has` fails the step before `heap_has` runs on the other parts.
  let simpHas : TacticM Unit := do
    evalTactic (← `(tactic|
      (intros; subst_vars; (try simp only [List.forall_mem_cons, List.forall_mem_nil, and_true, $args,*])
       (repeat' refine And.intro ?_ ?_))))
    for g in ← getGoals do
      unless ← hasConst ``Lift.Trusted.Mem.has g do throwError "heap-has: a part with no Mem.has"
    evalTactic (← `(tactic| all_goals heap_has))
  _ ← step log "prep" prep
  -- The flag hypotheses as linear facts (`Lift/Tactic/FlagNorm.lean`); a hypothesis that becomes `False` closes the goal.
  _ ← step log "flag-norm" do
    match ← flagNormHyps (← getMainGoal) with
    | none => replaceMainGoal []
    | some g => replaceMainGoal [← addUIntFacts (← splitAnds g)]
  if (← getGoals).isEmpty then return true
  _ ← step log "simp-norm" (evalTactic simpNorm)
  _ ← step log "heap-eqs" do
    replaceMainGoal [← rewriteHeapEqs (← getMainGoal)]
  -- `simp-norm` can close the goal; then there is no main goal for `hasToObj`.
  if (← getGoals).isEmpty then return true
  -- The rules of typed objects run only on goals with a typed heap; the other goals see the old steps.
  if ← hasToObj (← getMainGoal) then
    _ ← step log "heap-field-norm" (evalTactic simpFieldNorm)
    -- The objects of definitions that `extra` does not name: the projections give the fields.
    _ ← step log "heap-obj-projs" do
      replaceMainGoal [← reduceObjProjsAll (← getMainGoal)]
      evalTactic simpFieldNorm
    -- A list definition gives `toObj (f xs)` with `f` an object definition: `simp-field-norm` makes its projections, so a
    -- second pass reduces them.
    _ ← step log "heap-obj-projs" do
      replaceMainGoal [← reduceObjProjsAll (← getMainGoal)]
      evalTactic simpFieldNorm
    -- A `Holds` for each heap of a chain of stores.
    _ ← step log "heap-holds" do
      replaceMainGoal [← addStoreHolds (← getMainGoal)]
    -- The size of each object of a `Holds`: the bound of an offset at an index below a length that is not a number.
    _ ← step log "heap-sizes" addObjSizes
    -- Each store gives the next heap; `subst` puts it into the next access, so the steps repeat while they progress.
    for _ in [0:8] do
      unless ← step log "heap-fields" simpFields do break
      if (← getGoals).isEmpty then return true
      _ ← step log "heap-subst" do
        replaceMainGoal [← substVars (← getMainGoal)]
      _ ← step log "heap-field-norm" (evalTactic simpFieldNorm)
    if (← getGoals).isEmpty then return true
    if ← hasConst ``Lift.Trusted.Mem.has (← getMainGoal) then
      _ ← step log "heap-has" simpHas
      if (← getGoals).isEmpty then return true
  _ ← step log "simp-hyps" (evalTactic simpHyps)
  if (← getGoals).isEmpty then return true
  _ ← step log "subst" do
    let g ← getMainGoal
    replaceMainGoal [← addChainFacts (← addUIntFacts (← substVars (← splitAnds g)))]
  _ ← step log "reduce-defs" do
    let g ← getMainGoal
    replaceMainGoal [← g.replaceTargetDefEq (← reduceProjDefs (← instantiateMVars (← g.getType)))]
  _ ← step log "simp-goal" (evalTactic simpGoal)
  if (← getGoals).isEmpty then return true
  -- A counter that goes down: `t - k` with `k ≤ t` becomes `j` with `t = j + k`, so that `take (j + 1)` takes a step.
  if ← step log "pred-shift" predShift then
    _ ← step log "simp-goal" (evalTactic simpGoal)
    if (← getGoals).isEmpty then return true
  _ ← step log "cond-norm" do
    replaceMainGoal (← condNorm (← getMainGoal)).toList
  if (← getGoals).isEmpty then return true
  _ ← step log "split" (evalTactic split)
  for g in ← getGoals do
    setGoals [g]
    unless ← closePart log extra 2 do
      trace[loop_close] "open part:{indentD (MessageData.ofGoal g)}"
      return false
  setGoals []
  return true

/-- `attemptClose` on the main goal; when a part stays open, a case split of the goal (`splitCase`) and the
same on each new goal, at most `fuel` splits deep. The state is as before if the result is `false`. -/
meta partial def attemptCloseSplit (log : StepLog) (extra : Array Term) (fuel : Nat) : TacticM Bool := do
  let g ← getMainGoal
  setGoals [g]
  let saved ← saveState
  if ← attemptClose log extra then return true
  saved.restore
  if fuel == 0 then return false
  let some gs ← (try splitCase g catch _ => do saved.restore; pure none) | return false
  trace[loop_close] "case split of the goal: {gs.length} goals"
  for g' in gs do
    setGoals [g']
    unless ← attemptCloseSplit log extra (fuel - 1) do return false
  setGoals []
  return true

/-- `loop_close` and `loop_close [extra]`: see the top of the file. -/
syntax (name := loopClose) "loop_close" (" [" term,* "]")? : tactic

@[tactic loopClose] meta def evalLoopClose : Tactic := fun stx => do
  let extra : Array Term := match stx with
    | `(tactic| loop_close [$ts,*]) => ts.getElems
    | _ => #[]
  let g ← getMainGoal
  let rest ← getGoals
  let saved ← saveState
  let log ← IO.mkRef #[]
  let ok ← attemptCloseSplit log extra 3
  let ts ← log.get
  unless ok do
    saved.restore
  for (name, ms, hb, r) in ts do
    trace[loop_close] "{name}: {ms} ms, {hb} heartbeats, {r}"
  if let some (name, ms, hb, _) := ts.foldl (init := none) fun
      | none, t => some t
      | some t, t' => if t'.2.2.1 > t.2.2.1 then some t' else some t then
    trace[loop_close] "costliest: {name}, {ms} ms, {hb} heartbeats"
  unless ok do
    -- With `set_option trace.loop_close true`, the error holds the result of each step.
    let steps ← if ← isTracingEnabledFor `loop_close then
        pure (ts.foldl (fun acc (n, _, _, r) => acc ++ s!"\n{n}: {r}") "")
      else pure ""
    g.withContext do throwError "loop_close: cannot close the goal{indentExpr (← g.getType)}{steps}"
  setGoals (rest.drop 1)

/-- A step that faults has no `ok` result. -/
theorem _root_.Lift.Sem.Res.not_ok_of_stuck {α : Type} {e : Lift.Sem.Res α} {s : String} (h : e = .stuck s) :
    ¬∃ v, e = .ok v := by
  rintro ⟨v, rfl⟩
  cases h

theorem _root_.Lift.Sem.Res.not_ok_of_noFuel {α : Type} {e : Lift.Sem.Res α} (h : e = .noFuel) : ¬∃ v, e = .ok v := by
  rintro ⟨v, rfl⟩
  cases h

/-- The fault of a `nofault` goal: the target is `False` and the last hypothesis is `e = .stuck s` (`true`) or
`e = .noFuel` (`false`). -/
meta def faultHyp? (g : MVarId) : MetaM (Option (LocalDecl × Expr × Bool)) := g.withContext do
  unless (← instantiateMVars (← g.getType)).isConstOf ``False do return none
  let some d := (← getLCtx).lastDecl | return none
  let some (_, e, r) := (← instantiateMVars d.type).eq? | return none
  if r.isAppOfArity ``Lift.Sem.Res.stuck 2 then return some (d, e, true)
  if r.isAppOfArity ``Lift.Sem.Res.noFuel 1 then return some (d, e, false)
  return none

/-- The goals `gS` (`e = .stuck s`) and `gN` (`e = .noFuel`) of one step: one goal with `¬∃ v, e = .ok v` in place of the
fault, in the context of `gN` (with no fault hypothesis); `none` if `gN` has a hypothesis that `gS` does not have. -/
meta def faultPairGoal? (gS gN : MVarId) (dS dN : LocalDecl) (e : Expr) : MetaM (Option MVarId) := do
  let lS := (← gS.getDecl).lctx
  let lN := (← gN.getDecl).lctx
  let common := lN.all fun d => d.isImplementationDetail || d.fvarId == dN.fvarId ||
    (lS.find? d.fvarId).any (·.type == d.type)
  unless common && dS.fvarId != dN.fvarId do return none
  gN.withContext do
    let resTy ← whnfR (← inferType e)
    let some α := resTy.getAppArgs[0]? | return none
    let okE ← withLocalDeclD `v α fun v => do
      mkLambdaFVars #[v] (← mkEq e (mkApp2 (mkConst ``Lift.Sem.Res.ok) α v))
    let ty := mkNot (← mkAppM ``Exists #[okE])
    let G ← withLCtx (lN.erase dN.fvarId) (← getLocalInstances) do
      mkFreshExprSyntheticOpaqueMVar (← mkArrow ty (mkConst ``False)) (← gN.getTag)
    let (_, g) ← G.mvarId!.intro `hfault
    -- the two goals take the proof of `G`
    gS.assign (mkApp G (← gS.withContext (mkAppM ``Lift.Sem.Res.not_ok_of_stuck #[dS.toExpr])))
    gN.assign (mkApp G (← mkAppM ``Lift.Sem.Res.not_ok_of_noFuel #[dN.toExpr]))
    return some g

/-- `loop_close_all` and `loop_close_all [extra]`: `try loop_close [extra]` on each goal, with one change. Two goals in a row
that fault at one step (`e = .stuck s`, then `e = .noFuel`, with the same other hypotheses) are one goal with
`¬∃ v, e = .ok v` in place of the fault, so `loop_close` runs once for the two. If that goal stays open, `loop_close` runs on
each of the two. A goal that stays open is as before. -/
syntax (name := loopCloseAll) "loop_close_all" (" [" term,* "]")? : tactic

@[tactic loopCloseAll] meta def evalLoopCloseAll : Tactic := fun stx => do
  let extra : Array Term := match stx with
    | `(tactic| loop_close_all [$ts,*]) => ts.getElems
    | _ => #[]
  let lc ← `(tactic| loop_close [$extra,*])
  -- `try loop_close` on `g`: the goals after it
  let close (g : MVarId) : TacticM (List MVarId) := do
    setGoals [g]
    let s ← saveState
    try evalTactic lc; getGoals catch _ => do s.restore; pure [g]
  let rec go : List MVarId → TacticM (List MVarId)
    | [] => pure []
    | gS :: gN :: rest => do
      if let (some (dS, e, true), some (dN, e', false)) := (← faultHyp? gS, ← faultHyp? gN) then
        if e == e' then
          let s ← saveState
          if let some g ← faultPairGoal? gS gN dS dN e then
            if (← close g).isEmpty then return ← go rest
          s.restore
          return (← close gS) ++ (← close gN) ++ (← go rest)
      return (← close gS) ++ (← go (gN :: rest))
    | [g] => close g
  setGoals (← go (← getGoals))

/-- `lift_loop! I μ out`: `lift_loop I μ out`, then `loop_close_all`. -/
macro "lift_loop! " i:term:max ppSpace m:term:max ppSpace o:term:max : tactic =>
  `(tactic| (lift_loop $i $m $o; loop_close_all))

/-- `lift_loop! I μ out [extra]`: `lift_loop I μ out`, then `loop_close_all [extra]`. -/
macro "lift_loop! " i:term:max ppSpace m:term:max ppSpace o:term:max " [" ts:term,* "]" : tactic =>
  `(tactic| (lift_loop $i $m $o; loop_close_all [$ts,*]))

end Lift.Tactic

/-! `lift_straight` (task UP-STRAIGHT): the goal `∃ r, b.Returns noCall l s r ∧ Q r` of blocks with no loop. Each path from `l`
ends at a return or at a step that is `stuck` or `noFuel`, in a bounded number of blocks, so the rule needs no invariant
and no result term: `Visits` with no state at the jump back (`fun _ => False`). The goals are those of `lift_loop`: `ret_k`
(`Q r`) and `nofault_k` (`False`), with the facts of the path. A jump back to `l` is an error. -/

namespace Lift.Sem

/-- The paths from `l` with no jump to `head` return a result of `Q`. -/
theorem Visits.exists_returns_of {L σ R : Type} {b : Leaf L σ R} {head : L} {Q : R → Prop} {l : L} {s : σ}
    (h : Visits b head (fun _ => False) Q l s) : ∃ r, b.Returns noCall l s r ∧ Q r := by
  induction h with
  | ret hs hq => exact ⟨_, .ret hs, hq⟩
  | back _ hp => exact hp.elim
  | goto hs _ ih =>
    obtain ⟨r, hr, hq⟩ := ih
    exact ⟨r, .goto hs hr, hq⟩
  | exit hr hq => exact ⟨_, hr, hq⟩

/-- The paths from `l` with no jump back to `l` return a result of `Q`. -/
theorem Visits.exists_returns {L σ R : Type} {b : Leaf L σ R} {Q : R → Prop} {l : L} {s : σ}
    (h : Visits b l (fun _ => False) Q l s) : ∃ r, b.Returns noCall l s r ∧ Q r :=
  Visits.exists_returns_of h

end Lift.Sem

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- `lift_straight`: see above. `lift_straight exits [l₁, …]` ends each path at the labels `l₁, …` (PIL-HEAP2: the head of a
loop after the entry): the goal `exit_k` is `Visits … lᵢ s` at that label, for `Visits.exit` with the lemma of the label. -/
syntax (name := liftStraight) "lift_straight" (" exits " "[" term,* "]")? : tactic

@[tactic liftStraight] meta def evalLiftStraight : Tactic := fun stx => do
  let `(tactic| lift_straight $[exits [$ts,*]]?) := stx | throwUnsupportedSyntax
  evalTactic (← `(tactic| refine Lift.Sem.Visits.exists_returns ?_))
  let g ← getMainGoal
  let base := (← g.getDecl).lctx.numIndices
  let stops ← g.withContext do
    let lty ← inferType ((← instantiateMVars (← g.getType)).getArg! 4)
    (ts.map (·.getElems) |>.getD #[]).mapM fun t => Term.elabTermAndSynthesize t lty
  let mut ends := #[]
  let mut counts : Std.HashMap String Nat := {}
  for (kind, g') in ← walk stops g [] 0 do
    if kind == "back" then
      throwError "lift_straight: a path jumps back to the start label (a loop: use lift_loop)"
    let k := counts.getD kind 0 + 1
    counts := counts.insert kind k
    ends := ends ++ (← finish base kind k g')
  setGoals ends.toList

/-- `lift_straight!`: `lift_straight`, then `loop_close_all`. -/
macro "lift_straight!" : tactic => `(tactic| (lift_straight; loop_close_all))

/-- `lift_straight! [extra]`: `lift_straight`, then `loop_close_all [extra]`. -/
macro "lift_straight! " " [" ts:term,* "]" : tactic => `(tactic| (lift_straight; loop_close_all [$ts,*]))

end Lift.Tactic

/-! `heap_fault` (task PIL-HEAP2): the goal `False` with a hypothesis `h.load a w = .stuck s` or `.noFuel` (or the same of
`loadB`), where the heap is a list of objects (the objects of the statement, then the frame) and `a` is the address of a cell of
one of them. The fault is impossible: some object has a cell of width `w` at `a`, so the load is `ok`. The tactic substitutes
the variables, unfolds the names `extra` with `heap_norm` (the heap becomes the list of `toObj` of the objects and the frame),
rewrites the heap equations, and finds the object and the cell (`heap_ok`, `heap_cell`): the first object of the list whose
cell has the address `a` (`rfl`, `simp` or `bv_omega`) and the width `w` (`rfl`). It needs no `Holds`. -/

namespace Lift.Sem

/-- A load from a heap whose first object has a cell of width `w` at `a` is `ok`. -/
theorem Heap.load_ok_cons_head {o : Obj} {h : Heap} {a : BitVec 64} {w : Width} (hg : (o.get a w).isSome) :
    ∃ v, Heap.load (o :: h) a w = .ok v := by
  unfold Heap.load
  cases hgo : o.get a w with
  | none => simp [hgo] at hg
  | some v => exact ⟨v, by simp [List.findSome?_cons, hgo]⟩

/-- A load from a heap after its first object is `ok` when it is `ok` from the rest of the heap. -/
theorem Heap.load_ok_cons_tail {o : Obj} {h : Heap} {a : BitVec 64} {w : Width} (ht : ∃ v, Heap.load h a w = .ok v) :
    ∃ v, Heap.load (o :: h) a w = .ok v := by
  obtain ⟨v, hv⟩ := ht
  unfold Heap.load at hv ⊢
  cases hgo : o.get a w with
  | some u => exact ⟨u, by simp [List.findSome?_cons, hgo]⟩
  | none => exact ⟨v, by simpa [List.findSome?_cons, hgo] using hv⟩

/-- An object has a cell of width `w` at `a` when one of its cells starts at `a` and has the width `w`. -/
theorem Obj.get_isSome_of_cell {o : Obj} {a : BitVec 64} {w : Width}
    (hx : ∃ x ∈ offsets 0 o.cells, o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w) : (o.get a w).isSome := by
  obtain ⟨x, hx, ha, hw⟩ := hx
  unfold Obj.get
  cases hf : (offsets 0 o.cells).findSome? (fun x => if o.addr + BitVec.ofNat 64 x.1 = a then x.2.get w else none) with
  | some _ => rfl
  | none =>
    have := List.findSome?_eq_none_iff.mp hf x hx
    simp [ha, hw, Cell.get] at this

theorem exists_mem_cons_of_exists_mem {α : Type} {P : α → Prop} {y : α} {l : List α} (h : ∃ x ∈ l, P x) :
    ∃ x ∈ y :: l, P x := by
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

theorem Heap.load_fault_stuck {h : Heap} {a : BitVec 64} {w : Width} {s : String} (hp : Heap.load h a w = .stuck s)
    (hok : ∃ v, Heap.load h a w = .ok v) : False := by
  obtain ⟨v, hv⟩ := hok
  rw [hv] at hp
  cases hp

theorem Heap.load_fault_noFuel {h : Heap} {a : BitVec 64} {w : Width} (hp : Heap.load h a w = .noFuel)
    (hok : ∃ v, Heap.load h a w = .ok v) : False := by
  obtain ⟨v, hv⟩ := hok
  rw [hv] at hp
  cases hp

theorem Heap.loadB_fault_stuck {h : Heap} {a : BitVec 64} {w : Width} {s : String} (hp : Heap.loadB h a w = .stuck s)
    (hok : ∃ v, Heap.load h a w = .ok v) : False := by
  obtain ⟨v, hv⟩ := hok
  rw [Heap.loadB_of_load hv] at hp
  cases hp

theorem Heap.loadB_fault_noFuel {h : Heap} {a : BitVec 64} {w : Width} (hp : Heap.loadB h a w = .noFuel)
    (hok : ∃ v, Heap.load h a w = .ok v) : False := by
  obtain ⟨v, hv⟩ := hok
  rw [Heap.loadB_of_load hv] at hp
  cases hp

end Lift.Sem

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- `heap_cell`: the goal `∃ x ∈ offsets n cs, P x`, with each cell tried in order. -/
syntax "heap_cell" : tactic
macro_rules
  | `(tactic| heap_cell) => `(tactic| first
      | (refine ⟨_, List.mem_cons_self .., ?_, rfl⟩; first | rfl | (simp [Lift.Sem.Bridge.toObj]; done) | bv_omega)
      | (refine Lift.Sem.exists_mem_cons_of_exists_mem ?_; heap_cell))

/-- `heap_ok`: the goal `∃ v, Heap.load (o₁ :: o₂ :: … :: h) a w = .ok v`, with each object tried in order. -/
syntax "heap_ok" : tactic
macro_rules
  | `(tactic| heap_ok) => `(tactic| first
      | (refine Lift.Sem.Heap.load_ok_cons_head (Lift.Sem.Obj.get_isSome_of_cell ?_); heap_cell)
      | (refine Lift.Sem.Heap.load_ok_cons_tail ?_; heap_ok))

/-- `heap_rw`: `rewriteHeapEqs` on the main goal. -/
syntax "heap_rw" : tactic

@[tactic «tacticHeap_rw»] meta def evalHeapRw : Tactic := fun _ => do
  replaceMainGoal [← rewriteHeapEqs (← getMainGoal)]

/-- `heap_fault [extra]`: see above. -/
macro "heap_fault" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  subst_vars
  simp only [heap_norm, $ts,*] at *
  heap_rw
  first
  | (apply Lift.Sem.Heap.load_fault_stuck; assumption; heap_ok)
  | (apply Lift.Sem.Heap.load_fault_noFuel; assumption; heap_ok)
  | (apply Lift.Sem.Heap.loadB_fault_stuck; assumption; heap_ok)
  | (apply Lift.Sem.Heap.loadB_fault_noFuel; assumption; heap_ok)))

end Lift.Tactic
