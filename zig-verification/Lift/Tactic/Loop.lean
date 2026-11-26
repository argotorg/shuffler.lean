module

public import Lift.Sem.Loop
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic.RenameInaccessibles

@[expose] public section

/-! `lift_loop I μ out`: the step goals of the loop rule `Lift.Sem.loop_vc`, one for each path.

The goal is `∀ x, I x → b.Returns noCall head x (out x)` (the result of the goal must be `out x`
up to `rfl`), or `b.Returns noCall head s r` (then the goal `entry : I s ∧ out s = r` stays). The
tactic applies `loop_vc` and walks the paths from `head`: it unfolds `b.step` at the present label
(`b` is a constant, or an application of one), splits each `if` and `match` of the step, and ends a
path at a return, at a jump to `head`, or at a step that is `stuck` or `noFuel`. The goals, in the
order of the paths (each kind has its own count `k`):

* `ret_k`: `r = out x`;
* `back_k.inv`, `back_k.dec`, `back_k.out`: `I y`, `μ y < μ x` and `out y = out x` for the state `y`
  at the jump to `head` (three goals; a conjunction `I y` stays one goal);
* `nofault_k`: `False`, for a step that is `stuck` or `noFuel` under the facts of the path;
* `entry`: `I s ∧ out s = r` (only in the second form).

Each goal has `x : σ` and `hx : I x`, and the facts of the path as `hp1`, `hp2`, … (conditions of an
`if`, equations of a `match`) and `v1`, `v2`, … (values of a `match`), in the order of the path.
A path that visits a label a second time without passing `head` is an error, and so is a path with
more than 64 blocks. -/

namespace Lift.Tactic

open Lift.P2.Total Lift.Sem

/-- The steps of a block, one result: `ret` and `back` end a path, `goto` goes on at another label. -/
inductive VRes {L σ R : Type} (b : Leaf L σ R) (head : L) (P : σ → Prop) (Q : R → Prop) :
    Res (Next L σ R Empty Empty.elim Empty.elim) → Prop
  | ret {r} : Q r → VRes b head P Q (.ok (.ret r))
  | back {s} : P s → VRes b head P Q (.ok (.goto head s))
  | goto {l s} : Visits b head P Q l s → VRes b head P Q (.ok (.goto l s))

/-- The paths from `l`, `s` are the paths of the result of the step. -/
theorem Visits.of_unfold {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {l : L} {s : σ} {r : Res (Next L σ R Empty Empty.elim Empty.elim)}
    (h : b.step l s = r) (hv : VRes b head P Q r) : Visits b head P Q l s := by
  cases hv with
  | ret hq => exact .ret h hq
  | back hp => exact .back h hp
  | goto hv => exact .goto h hv

theorem VRes.ite {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {c : Prop} [Decidable c] {r₁ r₂ : Res (Next L σ R Empty Empty.elim Empty.elim)}
    (h₁ : c → VRes b head P Q r₁) (h₂ : ¬ c → VRes b head P Q r₂) :
    VRes b head P Q (if c then r₁ else r₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem VRes.ok_ite {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {c : Prop} [Decidable c] {n₁ n₂ : Next L σ R Empty Empty.elim Empty.elim}
    (h₁ : c → VRes b head P Q (.ok n₁)) (h₂ : ¬ c → VRes b head P Q (.ok n₂)) :
    VRes b head P Q (.ok (if c then n₁ else n₂)) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem VRes.dite {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {c : Prop} [Decidable c] {r₁ : c → Res (Next L σ R Empty Empty.elim Empty.elim)}
    {r₂ : ¬ c → Res (Next L σ R Empty Empty.elim Empty.elim)}
    (h₁ : ∀ h : c, VRes b head P Q (r₁ h)) (h₂ : ∀ h : ¬ c, VRes b head P Q (r₂ h)) :
    VRes b head P Q (if h : c then r₁ h else r₂ h) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem VRes.ok_dite {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {c : Prop} [Decidable c] {n₁ : c → Next L σ R Empty Empty.elim Empty.elim}
    {n₂ : ¬ c → Next L σ R Empty Empty.elim Empty.elim}
    (h₁ : ∀ h : c, VRes b head P Q (.ok (n₁ h))) (h₂ : ∀ h : ¬ c, VRes b head P Q (.ok (n₂ h))) :
    VRes b head P Q (.ok (if h : c then n₁ h else n₂ h)) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- `loop_vc` from the state `s`, with the result `r`. -/
theorem loop_vc_at {L σ R : Type} {b : Leaf L σ R} {head : L} (I : σ → Prop) (μ : σ → Nat)
    (out : σ → R)
    (step : ∀ x, I x → Visits b head (fun y => I y ∧ μ y < μ x ∧ out y = out x)
      (fun r => r = out x) head x)
    {s : σ} {r : R} (h : I s ∧ out s = r) : b.Returns noCall head s r :=
  h.2 ▸ loop_vc I μ out step s h.1

open Lean Meta Elab Tactic

/-- The most blocks on one path. -/
meta def maxBlocks : Nat := 64

/-- Run a tactic on the goal `g` alone; it must close `g`. -/
meta def closeWith (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  setGoals [g]
  tac
  unless (← getGoals).isEmpty do
    throwError "lift_loop: cannot unfold the step{indentExpr (← g.getType)}"

/-- The ends of the paths from the goal `g`, in the order of the paths: the kind `ret`, `back`,
`nofault` or `exit`, and the goal. `path` holds the labels of the blocks since `head`. A path that
reaches a label of `stops` after the head ends there (`exit`): the goal `Visits … l s` stays, for
`Visits.exit` with the lemma of that label (the head of a later loop, or the outer head). -/
meta partial def walk (stops : Array Expr) (g : MVarId) (path : List Expr) (depth : Nat) :
    TacticM (Array (String × MVarId)) :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let label := path.head?.getD (mkConst ``Unit.unit)
    if depth > 1000 then
      throwError "lift_loop: fuel ended at label `{label}`: more than 1000 splits"
    if ty.isAppOf ``Visits then
      let b := ty.getArg! 3
      let head := ty.getArg! 4
      let l ← instantiateMVars (ty.getArg! 7)
      if path.length ≥ maxBlocks then
        throwError "lift_loop: fuel ended at label `{l}`: a path has more than {maxBlocks} blocks"
      if !path.isEmpty then
        for t in stops do
          if ← isDefEq t l then
            return #[("exit", g)]
      for p in path do
        if ← isDefEq p l then
          throwError "lift_loop: the path visits label `{l}` a second time without passing the head `{head}`"
      let some bn := b.getAppFn.constName?
        | throwError "lift_loop: the blocks are not a constant{indentExpr b}"
      let [h, hv] ← g.apply (← mkConstWithFreshMVarLevels ``Visits.of_unfold)
          { newGoals := .nonDependentOnly }
        | throwError "lift_loop: Visits.of_unfold"
      closeWith h (evalTactic (← `(tactic| (simp only [$(mkIdent bn):ident]; try rfl))))
      walk stops hv (l :: path) (depth + 1)
    else if ty.isAppOf ``VRes then
      let head := ty.getArg! 4
      let r ← whnfR (← instantiateMVars (ty.getArg! 7))
      let step (lem : Name) (kind : String) : TacticM (Array (String × MVarId)) := do
        let [g'] ← g.apply (← mkConstWithFreshMVarLevels lem) | throwError "lift_loop: {lem}"
        return #[(kind, g')]
      let branches (lem : Name) : TacticM (Array (String × MVarId)) := do
        let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
        let mut out := #[]
        for g' in gs do
          let (_, g'') ← g'.intro (← mkFreshUserName `h)
          out := out ++ (← walk stops g'' path (depth + 1))
        return out
      let split (e : Expr) : TacticM (Array (String × MVarId)) := do
        let mut out := #[]
        for g' in ← Split.splitMatch g e do
          out := out ++ (← walk stops g' path (depth + 1))
        return out
      if r.isAppOfArity ``Res.ok 2 then
        let n ← whnfR (r.getArg! 1)
        if n.isAppOfArity ``Next.ret 7 then
          step ``VRes.ret "ret"
        else if n.isAppOfArity ``Next.goto 8 then
          if ← isDefEq (n.getArg! 6) head then
            step ``VRes.back "back"
          else
            let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``VRes.goto)
              | throwError "lift_loop: VRes.goto"
            walk stops g' path (depth + 1)
        else if n.isAppOfArity ``ite 5 then
          branches ``VRes.ok_ite
        else if n.isAppOfArity ``dite 5 then
          branches ``VRes.ok_dite
        else if (← matchMatcherApp? n).isSome then
          split n
        else
          throwError "lift_loop: the step at label `{label}` is not a jump or a return{indentExpr n}"
      else if r.isAppOfArity ``Res.stuck 2 || r.isAppOfArity ``Res.noFuel 1 then
        return #[("nofault", ← g.exfalso)]
      else if r.isAppOfArity ``ite 5 then
        branches ``VRes.ite
      else if r.isAppOfArity ``dite 5 then
        branches ``VRes.dite
      else if (← matchMatcherApp? r).isSome then
        split r
      else
        throwError "lift_loop: cannot unfold the step at label `{label}`{indentExpr r}"
    else
      throwError "lift_loop: not a path goal{indentExpr ty}"

/-- Name the hypotheses that the walk made (the last inaccessible ones, after `base` hypotheses):
`hp1`, … for propositions and `v1`, … for values; then reduce the beta redexes of the target. -/
meta def finish (base : Nat) (kind : String) (k : Nat) (g : MVarId) : TacticM (Array MVarId) := do
  -- The discriminant that `match` generalizes is a value that nothing uses.
  let mut g := g
  for d in (← g.getDecl).lctx.decls.toList.reverse do
    if let some d := d then
      if d.index ≥ base && d.userName.hasMacroScopes && !(← g.withContext (isProp d.type)) then
        g ← g.tryClear d.fvarId
  let news ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc d =>
      if d.index ≥ base && d.userName.hasMacroScopes then
        return acc.push (← isProp d.type)
      else return acc
  let mut hs : Array (TSyntax `Lean.binderIdent) := #[]
  let mut (p, v) := (0, 0)
  for isP in news do
    if isP then
      p := p + 1
      hs := hs.push (← `(binderIdent| $(mkIdent (.mkSimple s!"hp{p}")):ident))
    else
      v := v + 1
      hs := hs.push (← `(binderIdent| $(mkIdent (.mkSimple s!"v{v}")):ident))
  g ← renameInaccessibles g hs
  let tag : Name := .mkSimple s!"{kind}_{k}"
  g.setTag tag
  g ← g.withContext do g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  if kind == "back" then
    let [inv, rest] ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      | throwError "lift_loop: the back goal is not a conjunction"
    let [dec, out] ← rest.apply (← mkConstWithFreshMVarLevels ``And.intro)
      | throwError "lift_loop: the back goal is not a conjunction"
    for (g', n) in [(inv, "inv"), (dec, "dec"), (out, "out")] do
      g'.setTag (.str tag n)
    return #[inv, dec, out]
  return #[g]

/-- `lift_loop I μ out`: see the top of the file. `lift_loop I μ out exits [l₁, …]` ends each path at the labels
`l₁, …` (L2-LOOPS): the goal `exit_k` is `Visits … lᵢ s` at that label, for `Visits.exit`. -/
syntax (name := liftLoop) "lift_loop " term:max ppSpace term:max ppSpace term:max
  (" exits " "[" term,* "]")? : tactic

@[tactic liftLoop] meta def evalLiftLoop : Tactic := fun stx => do
  let `(tactic| lift_loop $i $m $o $[exits [$ts,*]]?) := stx | throwUnsupportedSyntax
  let ty ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  unless ← forallTelescope ty fun _ body => pure (body.isAppOf ``Blocks.Returns) do
    throwError "lift_loop: the goal must be `b.Returns noCall head s r` or `∀ x, I x → b.Returns noCall head x r`{indentExpr ty}"
  if ty.isForall then
    evalTactic (← `(tactic| refine Lift.Sem.loop_vc $i $m $o ?_))
  else
    evalTactic (← `(tactic| refine Lift.Tactic.loop_vc_at $i $m $o ?_ ?_))
  let step :: entry := ← getGoals | throwError "lift_loop: no goal"
  let (_, step) ← step.intro `x
  let (_, step) ← step.intro `hx
  let base := (← step.getDecl).lctx.numIndices
  let stops ← step.withContext do
    let ty ← instantiateMVars (← step.getType)
    let lty ← inferType (ty.getArg! 4)
    (ts.map (·.getElems) |>.getD #[]).mapM fun t => Term.elabTermAndSynthesize t lty
  let mut ends := #[]
  let mut counts : Std.HashMap String Nat := {}
  for (kind, g) in ← walk stops step [] 0 do
    let k := counts.getD kind 0 + 1
    counts := counts.insert kind k
    ends := ends ++ (← finish base kind k g)
  let entry ← entry.mapM fun g => do
    g.setTag `entry
    g.withContext do g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  setGoals (entry ++ ends.toList)

end Lift.Tactic
