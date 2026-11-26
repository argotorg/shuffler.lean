module

/-
`kblock`: closes the easy verification conditions (VCs) of a Kraken proof, so that a proof worker
works on the hard ones only. The design, with the measured classes of VCs, is in
`docs/kblock-design.md`.

Use it after `vcgen [prog] invariants … with skip`:

    kblock?            -- or `kblock? [lemma₁, lemma₂]`

`kblock?` splits each goal into leaves (`∧`, `Program.Intercept`, `∃`), tries a fixed list of
steps on each leaf, and prints a report and a script: `case vcN => …` with the tactic that closed
each leaf and `sorry` at each leaf that stays open. The goals do not change. The user puts the
script in the file in place of `kblock?`; the later checks run the script only, not the search.
`kblock [...]` runs the same search and leaves the open leaves as goals. `set_option trace.kblock
true` shows each attempt.

The steps are in stages (`Recipe.stage`): the cheap steps (`rfl`, the class steps) on every leaf,
then `kfinish`, then `mem_simp; kfinish`, then the variants with lemma hints and
`Inside.of_toNat`. Every attempt has its own limit of heartbeats and its own wall-clock limit, and
the whole search has a wall-clock limit (the options `kblock.*` below). A heartbeat timeout is not
caught by `try` or `first`, and the heartbeats count per command, so the search runs without the
heartbeat limit of the command and gives the heartbeats back at its end. The wall-clock limit
sets a cancel token, which `checkSystem` reads; `omega` does not call it, so `kb_bv` does not call
`omega` on a goal that it cannot prove (see there).

The steps are ordinary tactics, each one deterministic:
- `kb_hyps`: splits the conjunctions of the hypotheses, substitutes the variable equations;
- `kb_bv`: the arithmetic of addresses and registers, with the facts of the goal only;
- `kb_inside`, `kb_disj`: `Mem.Blocks.Inside` and `Mem.Blocks.Disjoint`, block by block;
- `kb_mapped h`: `Mem.Mapped` and `isSome` of a load, from the mapped block list `h`;
- `kb_rsp`, `kb_stack`: the stack side conditions of a jump or a return;
- `kb_load`: a load through a chain of stores, `havoc` and `WritesOnly`;
- `kb_incl`, `kb_frame`: `Mem.WritesOnly` frames.

Extension points, all fields of `Kb.Cx`: `hints` (lemma names for `kfinish [...]`), `skip` (a leaf
that stays open without a try, for a counterexample of a `#fuzz` run), `extra` (steps for a class
of leaf, as from a footprint engine).
-/
public import VerifiedNix.MemSimp
public import VerifiedNix.ProofLemmas
public import VerifiedNix.Tactics
public meta import Kraken.SeparationTactics
public meta import Lean.Elab.Tactic

@[expose] public section

open Lean Elab Tactic Meta

/-! ## Common helpers -/

namespace Kb

/-- An arithmetic fact for `bv_omega`: `=`, `≠`, `≤`, `<` over `Nat`, `Int`, `BitVec`, `UInt64`. -/
meta def isArith (ty : Expr) : MetaM Bool := do
  let ty := ty.consumeMData
  let ty := if ty.isAppOfArity ``Not 1 then ty.getArg! 0 else ty
  let carrier? : Option Expr :=
    if ty.isAppOfArity ``Eq 3 then some (ty.getArg! 0)
    else if ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 then some (ty.getArg! 0)
    else none
  match carrier? with
  | none => return false
  | some c =>
    let c ← whnfR c
    return c.isConstOf ``Nat || c.isConstOf ``Int || c.isAppOf ``BitVec || c.isConstOf ``UInt64

/-- The atoms of an arithmetic fact or goal: the maximal subterms that are not literals, sums,
differences, products, quotients, `toNat` or comparisons (the explicit arguments of these only). -/
meta partial def atoms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  -- the head, and the number of trailing arguments that are operands
  let ops : List (Name × Nat) := [(``HAdd.hAdd, 2), (``HSub.hSub, 2), (``HMul.hMul, 2),
    (``HDiv.hDiv, 2), (``HMod.hMod, 2), (``HPow.hPow, 2), (``LE.le, 2), (``LT.lt, 2),
    (``GE.ge, 2), (``GT.gt, 2), (``Eq, 2), (``Ne, 2), (``And, 2), (``Or, 2), (``Iff, 2),
    (``Neg.neg, 1), (``Not, 1), (``BitVec.toNat, 1), (``BitVec.toInt, 1), (``UInt64.toBitVec, 1),
    (``BitVec.ofNat, 1), (``Nat.cast, 1), (``Int.ofNat, 1), (``OfNat.ofNat, 0)]
  match e.getAppFn.constName?.bind fun n => ops.lookup n with
  | some k =>
    let args := e.getAppArgs
    (args.extract (args.size - k) args.size).foldl
      (fun acc a => (atoms a).foldl (fun acc x => if acc.contains x then acc else acc.push x) acc) #[]
  | none => if e.isLit then #[] else #[e]

/-- A register atom: a local variable, or a projection of one (`s.regs.rsp`, `Reg64s.get64`). An
atom of another shape (a value loaded from memory) makes `omega` search for minutes on a goal
that it cannot prove. -/
meta partial def isRegAtom (env : Environment) (e : Expr) : Bool :=
  e.isFVar || match e.getAppFn.constName? with
    | some n =>
      (n == ``Reg64s.get64 || (env.getProjectionFnInfo? n).isSome) && e.getAppNumArgs > 0
        && isRegAtom env e.getAppArgs[0]!
    | none => false

/-- `bv_omega` on `g` with only the hypotheses that satisfy `keep` in the context. -/
meta def bvOmegaWith (g : MVarId) (keep : LocalDecl → MetaM Bool) : TacticM Unit := do
  let g ← g.withContext do
    let mut drop : Array FVarId := #[]
    for d in ← getLCtx do
      unless ← keep d do drop := drop.push d.fvarId
    g.tryClearMany drop
  replaceMainGoal [g]
  evalTactic (← `(tactic| bv_omega))

/-- The first of the actions that succeeds; the others leave no trace. -/
meta def firstOf (alts : Array (TacticM Unit)) : TacticM Unit := do
  for alt in alts do
    let s ← saveState
    try
      withoutRecover alt
      return
    catch _ => s.restore
  throwError "no alternative worked"

/-- The accessible names of the local hypotheses whose type has the head constant `c`, up to
reducible unfolding. A shadowed name is left out. -/
meta def hypNames (c : Name) : MetaM (Array Name) := do
  let lctx ← getLCtx
  let mut out := #[]
  for d in lctx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    unless (← whnfR (← instantiateMVars d.type)).getAppFn.isConstOf c do continue
    if (lctx.findFromUserName? d.userName).map (·.fvarId) == some d.fvarId then
      out := out.push d.userName
  return out

/-- The local hypotheses whose type has the head constant `c`, as terms. -/
meta def hypTerms (c : Name) : TacticM (Array Term) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← whnfR (← instantiateMVars d.type)).getAppFn.isConstOf c then
      out := out.push (← Term.exprToSyntax d.toExpr)
  return out

end Kb

/-! ## Arithmetic and hypotheses -/

/-- `kb_bv`: first `(x - a).toNat` with a constant difference becomes a literal (`MemSimp.subToNat`)
and `omega` decides the rest (`omega` on five `BitVec` sums and differences, also over one atom,
ran for minutes); then `bv_omega` with no hypothesis, when the goal has one atom at most (two
unrelated registers make a false goal, and `omega` does not check the time or the heartbeats in
its search: a false goal of five sums and differences over two atoms ran for 300 s); then with the
arithmetic facts (`=`, `≠`, `≤`, `<` over `Nat`, `Int`, `BitVec`, `UInt64`) that share an atom with
the goal, when there are at most 12. All atoms must be registers (`isRegAtom`), at most 3 in the
goal: a goal about a value loaded from memory is not arithmetic, and `omega` ran for 370 s on it.
`bv_omega` with the whole context took minutes and gigabytes on a false goal. -/
syntax (name := kbBv) "kb_bv" : tactic

@[tactic kbBv] meta def evalKbBv : Tactic.Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let s ← saveState
  -- `(x - a).toNat` with a constant difference (`MemSimp.subToNat`) becomes a literal
  try
    evalTactic (← `(tactic| simp only [MemSimp.subToNat]))
    if (Kb.atoms (← instantiateMVars (← getMainTarget))).isEmpty then
      evalTactic (← `(tactic| omega))
      return
    s.restore
  catch _ => s.restore
  let env ← getEnv
  let tgt ← instantiateMVars (← g.getType)
  let goalAtoms := Kb.atoms tgt
  unless goalAtoms.size ≤ 3 && goalAtoms.all (Kb.isRegAtom env) do
    throwError "kb_bv: the goal has {goalAtoms.size} atoms, not all registers"
  if goalAtoms.size ≤ 1 then
    try
      Kb.bvOmegaWith g fun _ => pure false
      return
    catch _ => s.restore
  let keep (d : LocalDecl) : MetaM Bool := do
    if d.isImplementationDetail then return false
    let ty ← instantiateMVars d.type
    if !(← Kb.isArith ty) then return false
    let as := Kb.atoms ty
    return as.all (Kb.isRegAtom env) && as.any goalAtoms.contains
  let facts ← (← getLCtx).foldlM (fun (n : Nat) d => do return if ← keep d then n + 1 else n) 0
  if facts == 0 then throwError "kb_bv: no fact about the atoms of the goal"
  if facts > 12 then throwError "kb_bv: {facts} facts about the atoms of the goal"
  Kb.bvOmegaWith g keep

/-- `kb_hyps`: `cases` on each hypothesis that is a conjunction up to reducible unfolding (the
conjuncts of an `abbrev` precondition become facts), `subst` of the variable equations
(`t = s.push64 ra`), then `dsimp only at *` (the projections of the state literals of callee
frames). It closes the goal of a loop entry (`s' = s₀`). -/
syntax (name := kbHyps) "kb_hyps" : tactic

@[tactic kbHyps] meta def evalKbHyps : Tactic.Tactic := fun _ => withMainContext do
  let gs ← (← getMainGoal).casesRec fun d => do
    if d.isImplementationDetail then return false
    return (← whnfR (← instantiateMVars d.type)).isAppOfArity ``And 2
  let [g] := gs | throwError "kb_hyps: cases gave {gs.length} goals"
  let g ← try substVars g catch _ => pure g
  replaceMainGoal [g]
  try evalTactic (← `(tactic| dsimp only at *)) catch _ => pure ()

/-! ## Memory side conditions -/

/-- One block of `kb_inside`: `Inside.of_toNat` or `Inside.of_stackSlots_toNat` for the first block
of the list, the arithmetic by `kb_bv`; else the next block. The two lemmas unify with reducible
transparency only: with the default one, the block `(0, 4)` against `Block.ofStackSlots ?rsp ?k`
unfolded `BitVec` arithmetic and ran out of heartbeats in `whnf`. -/
macro "kb_inside_step" : tactic => `(tactic| first
  | ((with_reducible refine Mem.Blocks.Inside.of_toNat ?_); kb_bv)
  | ((with_reducible refine Mem.Blocks.Inside.of_stackSlots_toNat ?_); kb_bv)
  | apply Mem.Blocks.Inside.tail)

/-- `kb_inside`: `Mem.Blocks.Inside x n bs`, block by block. Fails when a block is left. -/
macro "kb_inside" : tactic => `(tactic| ((repeat kb_inside_step); done))

/-- `kb_disj1`: a singleton disjointness `Disjoint [(x, k)] [(a, n)]`: by `Disjoint.of_sub`
(also after `ofStackSlots_eq`), or from a `Disjoint` hypothesis and two `Inside` facts. -/
syntax (name := kbDisj1) "kb_disj1" : tactic

@[tactic kbDisj1] meta def evalKbDisj1 : Tactic.Tactic := fun _ => withMainContext do
  let ds ← Kb.hypTerms ``Mem.Blocks.Disjoint
  let ofSub : TacticM Unit := evalTactic (← `(tactic|
    exact Mem.Blocks.Disjoint.of_sub (by kb_bv) (by kb_bv)))
  let ofSub' : TacticM Unit := evalTactic (← `(tactic|
    (rw [MemSimp.ofStackSlots_eq]; exact Mem.Blocks.Disjoint.of_sub (by kb_bv) (by kb_bv))))
  let fromHyp (symm : Bool) (d : Term) : TacticM Unit := do
    if symm then
      evalTactic (← `(tactic| apply Mem.Blocks.Disjoint.symm))
    Kb.firstOf #[
      evalTactic (← `(tactic| exact Mem.Blocks.Disjoint.of_inside $d (by kb_inside) (by kb_inside))),
      evalTactic (← `(tactic| exact Mem.Blocks.Disjoint.of_inside' $d (by kb_inside) (by kb_inside)))]
  Kb.firstOf (#[ofSub, ofSub'] ++ ds.map (fromHyp false) ++ ds.map (fromHyp true))

/-- `kb_disj`: `Mem.Blocks.Disjoint [(x, k)] bs` for a list `bs` of any length: one singleton for
each block (`kb_disj1`). -/
macro "kb_disj" : tactic => `(tactic|
  ((repeat' (rw [Mem.Blocks.Disjoint.cons_cons_right_iff]; constructor)) <;> kb_disj1))

/-- `kb_peel`: strips `havoc`, `storeInt` and `WritesOnly` steps off a mapped memory. -/
macro "kb_peel" : tactic => `(tactic|
  repeat' (first
    | apply Mem.Mapped.havoc
    | apply Mem.Mapped.storeInt
    | (apply Mem.WritesOnly.mapped; assumption)))

/-- `kb_mapped h`: `Mem.Mapped [(x, n)] m` (a store) or `(m.loadInt x n).isSome = true` (a load),
from `h : Mem.Mapped bs m₀` where `m` is `m₀` after stores, `havoc` and `WritesOnly` steps, and
`Inside x n bs` by `kb_inside`. -/
macro "kb_mapped " h:term : tactic => `(tactic| first
  | ((try rw [Option.isSome_map]); apply Mem.Mapped.loadInt_isSome; (focus (kb_peel; exact $h)); kb_inside)
  | (apply Mem.Mapped.of_inside; (focus (kb_peel; exact $h)); kb_inside))

/-! ## Stack and registers -/

/-- `kb_rsp`: an equation of the stack pointer, after a `push64`. -/
macro "kb_rsp" : tactic => `(tactic| first
  | kb_bv
  | (simp only [Reg64s.get64_rsp, Reg64s.rsp_mk, UInt64.toBitVec_ofBitVec] <;> kb_bv)
  | (simp [MachineData.regs_push64, MachineData.push64] <;> kb_bv))

/-- `kb_stack`: the stack part of a jump (`StackAtOrBelow`), of an exit (`StackBelow` of the state
after a `push64`) and of the exit of an `Intercept` (`∀ l ∈ ls, label l = a → …`). -/
macro "kb_stack" : tactic => `(tactic| first
  | exact MachineData.stackAtOrBelow_of_rsp (by kb_rsp)
  | exact MachineData.push64_stackBelow (by kb_rsp)
  | exact fun _ _ _ => MachineData.push64_stackBelow (by kb_rsp))

/-- `kb_load`: rewrites a load through a chain of `havoc`, `storeInt` and `WritesOnly` steps whose
blocks are disjoint from the loaded block. Fails when nothing changes. -/
syntax (name := kbLoad) "kb_load" : tactic

@[tactic kbLoad] meta def evalKbLoad : Tactic.Tactic := fun _ => withMainContext do
  let t0 ← instantiateMVars (← getMainTarget)
  let rewriteOnce : TacticM Unit := withMainContext do
    let ws ← Kb.hypTerms ``Mem.WritesOnly
    Kb.firstOf (#[
      evalTactic (← `(tactic| rw [Mem.loadInt_havoc_of_disjoint (by kb_disj)])),
      evalTactic (← `(tactic| rw [Mem.loadInt_storeInt_of_disjoint (by kb_disj)]))] ++
      ws.map fun w => do evalTactic (← `(tactic| rw [Mem.WritesOnly.loadInt $w (by kb_disj)])))
  for _ in List.range 3 do
    if (← getUnsolvedGoals).isEmpty then return
    try evalTactic (← `(tactic| mem_simp)) catch _ => pure ()
    repeat
      if (← getUnsolvedGoals).isEmpty then break
      try rewriteOnce catch _ => break
  if (← getUnsolvedGoals).isEmpty then return
  if (← instantiateMVars (← getMainTarget)) == t0 then throwError "kb_load: no load to rewrite"

/-! ## Frames -/

/-- `kb_incl`: `∀ a, Mem.Blocks.Inside a 1 cs → Mem.Blocks.Inside a 1 bs` for explicit lists. -/
syntax (name := kbIncl) "kb_incl" : tactic

namespace Kb

/-- `∀ a, Inside a 1 cs → Inside a 1 bs`, block by block: `cases` on the `Or` of `cs`, then
`kb_inside` with the fact of the block. -/
meta partial def inclGo (fuel : Nat) : TacticM Unit := withMainContext do
  if fuel == 0 then throwError "kb_incl: fuel"
  let hz := mkIdent `hz
  let ty ← whnfD (← instantiateMVars (← getLocalDeclFromUserName `hz).type)
  if ty.isAppOfArity ``Or 2 then
    evalTactic (← `(tactic| rcases $hz:ident with $hz:ident | $hz:ident))
    for g in ← getGoals do
      setGoals [g]
      inclGo (fuel - 1)
    setGoals []
  else if ty.isConstOf ``False then
    evalTactic (← `(tactic| exact absurd $hz:ident id))
  else
    evalTactic (← `(tactic| ((try simp only [MemSimp.ofStackSlots_eq] at $hz:ident); kb_inside; done)))

/-- `Mem.WritesOnly bs m M` where `M` is `m` after a chain of `storeInt` and `havoc`. -/
meta partial def frameGo (fuel : Nat) : TacticM Unit := withMainContext do
  if fuel == 0 then throwError "kb_frame: fuel"
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOf ``Mem.WritesOnly do throwError "kb_frame: not a WritesOnly goal"
  let M ← whnfR ty.appArg!
  -- `exact WritesOnly.refl` on a large memory term ran out of heartbeats in `whnf`: syntactic test
  if (← instantiateMVars (ty.getArg! 2)) == M then
    evalTactic (← `(tactic| exact Mem.WritesOnly.refl _ _))
  else if M.isAppOf ``Mem.havoc then
    let s ← saveState
    try
      withReducible (evalTactic (← `(tactic| exact Mem.WritesOnly.havoc _ _ _)))
      return
    catch _ => s.restore
    evalTactic (← `(tactic| refine Mem.WritesOnly.trans ?_ ((Mem.WritesOnly.havoc _ _ _).mono ?_)))
    let [g1, g2] ← getGoals | throwError "kb_frame: havoc split"
    setGoals [g2]
    evalTactic (← `(tactic| kb_incl))
    setGoals [g1]
    frameGo (fuel - 1)
  else if M.isAppOf ``Mem.storeInt then
    evalTactic (← `(tactic| refine Mem.WritesOnly.trans_storeInt ?_ ?_ _))
    let [g1, g2] ← getGoals | throwError "kb_frame: store split"
    setGoals [g2]
    evalTactic (← `(tactic| (kb_inside; done)))
    setGoals [g1]
    frameGo (fuel - 1)
  else
    evalTactic (← `(tactic| rw [MachineData.dmem_push64]))
    frameGo (fuel - 1)

end Kb

@[tactic kbIncl] meta def evalKbIncl : Tactic.Tactic := fun _ => withMainContext do
  evalTactic (← `(tactic| intro $(mkIdent `z) $(mkIdent `hz)))
  Kb.inclGo 32

/-- `kb_frame`: `Mem.WritesOnly bs m M` where `M` is `m` after a chain of `storeInt` and `havoc`;
the blocks of the stores are inside `bs`, the blocks of a `havoc` by `kb_incl`. -/
syntax (name := kbFrame) "kb_frame" : tactic

@[tactic kbFrame] meta def evalKbFrame : Tactic.Tactic := fun _ => Kb.frameGo 64

/-! ## The search

The search splits each goal into leaves and tries the steps of the class of each leaf. A leaf that
a step closes records the text of the step; the printed script is the list of these texts. -/

register_option kblock.stepHeartbeats : Nat := {
  defValue := 20000
  descr := "kblock: heartbeats (in thousands) of one attempt of a class step" }

register_option kblock.kfinishHeartbeats : Nat := {
  defValue := 60000
  descr := "kblock: heartbeats (in thousands) of one attempt of `kfinish`" }

register_option kblock.stepMs : Nat := {
  defValue := 10000
  descr := "kblock: wall-clock limit in ms of one attempt of a class step" }

register_option kblock.kfinishMs : Nat := {
  defValue := 30000
  descr := "kblock: wall-clock limit in ms of one attempt of `kfinish`" }

register_option kblock.totalMs : Nat := {
  defValue := 150000
  descr := "kblock: wall-clock limit in ms of the whole search; later leaves stay open" }

register_option kblock.times : Bool := {
  defValue := true
  descr := "kblock: the report gives the time of each leaf" }

register_option kblock.ecancel : Bool := {
  defValue := false
  descr := "kblock: Kraken's `ecancel` as a step for the memory and frame leaves, after `kfinish`" }

register_option kblock.reportAll : Bool := {
  defValue := true
  descr := "kblock: the report lists each leaf (else only the open leaves)" }

initialize Lean.registerTraceClass `kblock

namespace Kb

/-- What the head of a goal says about the steps to try. -/
meta inductive Cls where
  | and | intercept | ex | all | invariant
  | isSome | mapped | disjoint | inside | stackBelow | stackAtOrBelow | writesOnly
  | eq (carrier : String)
  | other (head : String)

meta def Cls.name : Cls → String
  | .and => "And" | .intercept => "Program.Intercept" | .ex => "Exists" | .all => "forall"
  | .invariant => "invariant" | .isSome => "isSome" | .mapped => "Mem.Mapped"
  | .disjoint => "Mem.Blocks.Disjoint" | .inside => "Mem.Blocks.Inside"
  | .stackBelow => "MachineData.StackBelow" | .stackAtOrBelow => "MachineData.StackAtOrBelow"
  | .writesOnly => "Mem.WritesOnly" | .eq c => s!"eq:{c}" | .other h => h

meta def headName (e : Expr) : String :=
  match e.getAppFn.constName? with
  | some n => n.toString
  | none => if e.isFVar then "fvar" else if e.isLambda then "lam" else "?"

/-- The class of a goal, by the head of its target after `instantiateMVars` and `headBeta`.
`whnfR` only finds a conjunction behind an `abbrev`; there is no `whnf` at default transparency,
because the targets carry state literals of thousands of characters. -/
meta def classify (target : Expr) : MetaM Cls := do
  let e := (← instantiateMVars target).headBeta.consumeMData
  if e.isForall then return .all
  let some h := e.getAppFn.constName? | return .other (headName e)
  if h == ``Eq then
    let lhs := (e.getArg! 1).consumeMData
    if lhs.getAppFn.constName? == some ``Option.isSome then return .isSome
    return .eq (headName (e.getArg! 0))
  if h == ``Not && (e.getArg! 0).getAppFn.constName? == some ``MachineData.StackBelow then
    return .stackAtOrBelow
  if h == ``And then return .and
  if h == ``Program.Intercept then return .intercept
  if h == ``Exists then return .ex
  if h == ``Mem.Mapped then return .mapped
  if h == ``Mem.Blocks.Disjoint then return .disjoint
  if h == ``Mem.Blocks.Inside then return .inside
  if h == ``Mem.WritesOnly then return .writesOnly
  if h == ``MachineData.StackBelow then return .stackBelow
  if h == ``MachineData.StackAtOrBelow then return .stackAtOrBelow
  if (Match.Extension.getMatcherInfo? (← getEnv) h).isSome then return .invariant
  if (← whnfR e).isAppOf ``And then return .and
  return .other h.toString

/-- The limits of the search: heartbeats in thousands, times in ms. -/
meta structure Limits where
  stepHeartbeats : Nat
  kfinishHeartbeats : Nat
  stepMs : Nat
  kfinishMs : Nat
  totalMs : Nat
  ecancel : Bool

meta def Limits.get (o : Options) : Limits where
  stepHeartbeats := o.get `kblock.stepHeartbeats (20000 : Nat)
  kfinishHeartbeats := o.get `kblock.kfinishHeartbeats (60000 : Nat)
  stepMs := o.get `kblock.stepMs (10000 : Nat)
  kfinishMs := o.get `kblock.kfinishMs (30000 : Nat)
  totalMs := o.get `kblock.totalMs (150000 : Nat)
  ecancel := o.get `kblock.ecancel (false : Bool)

/-- A step to try: the tactic text, its heartbeats (thousands) and its time (ms), and its stage.
The search tries the steps of stage 0 (cheap: `rfl`, the class steps) on every leaf, then those of
stage 1 on the leaves that are open, and so on: when the total time runs out, every leaf has had
the cheap steps. -/
meta structure Recipe where
  text : String
  heartbeats : Nat
  ms : Nat
  stage : Nat := 0

/-- The context of one search. `hints` are the lemma names for `kfinish [...]`. `skip path` gives
the reason to leave the leaf `path` open without a try, for a source of counterexamples (a leaf
that a `#fuzz` run showed false). `extra cls` are steps for a leaf of class `cls`, tried after the
class steps and before `kfinish` (the extension point for a source of steps, as a footprint). `deadline`
is a `IO.monoMsNow` time. -/
meta structure Cx where
  limits : Limits
  hints : Array String := #[]
  skip : String → Option String := fun _ => none
  extra : Cls → Array Recipe := fun _ => #[]
  deadline : Nat

/-- Why an attempt failed. -/
meta inductive Failure where
  | error | heartbeats | time

meta def Failure.name : Failure → String
  | .error => "failed" | .heartbeats => "heartbeats" | .time => "time"

/-! ### One attempt -/

/-- Sets `tk` when the deadline passes or when `outer` is set. -/
meta partial def watch (tk : IO.CancelToken) (outer : Option IO.CancelToken) (stop : IO.Ref Bool)
    (deadline : Nat) : BaseIO Unit := do
  if ← stop.get then return
  let outerSet ← match outer with
    | some o => o.isSet
    | none => pure false
  if outerSet || (← IO.monoMsNow) ≥ deadline then tk.set
  else
    IO.sleep 5
    watch tk outer stop deadline

/-- Runs `x` with a wall-clock limit of `ms`: a timer thread sets the cancel token of the context,
and `checkSystem` (in `whnf`, `isDefEq`, `simp`, …) then throws an interrupt exception. -/
meta def withTimeLimit {α : Type} (ms : Nat) (x : TacticM α) : TacticM α := do
  let tk ← IO.CancelToken.new
  let stop ← IO.mkRef false
  let outer := (← readThe Core.Context).cancelTk?
  let _ ← (watch tk outer stop ((← IO.monoMsNow) + ms)).asTask (prio := .dedicated)
  try
    withTheReader Core.Context (fun c => { c with cancelTk? := some tk }) x
  finally
    stop.set true

/-- `tryCatchRuntimeEx` that also catches the interrupt exception. -/
meta def catchAllCore {α : Type} (x : CoreM α) (h : Exception → CoreM α) : CoreM α := fun ctx sref => do
  match ← (x ctx sref).toBaseIO with
  | .ok a => pure a
  | .error e => h e ctx sref

meta def catchAll {α : Type} (x : TacticM α) (h : Exception → TacticM α) : TacticM α :=
  controlAt CoreM fun runInBase => catchAllCore (runInBase x) fun ex => runInBase (h ex)

/-- The result of an attempt: the goals that remain, or the failure; the time in ms. -/
meta structure Run where
  result : Except Failure (List MVarId)
  ms : Nat

/-- Runs the tactic `text` on `g` with a limit of `hb` thousand heartbeats and of `ms` ms of its
own. With `closing`, the goal must be closed and the proof must have no `sorry` (a failed `by`
block can leave one without an exception). A failed attempt leaves no trace. -/
meta def run (cx : Cx) (hb ms : Nat) (g : MVarId) (text : String) (closing : Bool) : TacticM Run := do
  let t0 ← IO.monoMsNow
  if t0 ≥ cx.deadline then return ⟨.error .time, 0⟩
  let .ok stx := Parser.runParserCategory (← getEnv) `tactic text | return ⟨.error .error, 0⟩
  let s ← saveState
  let outer := (← readThe Core.Context).cancelTk?
  let r ← catchAll
    (withTimeLimit (min ms (cx.deadline - t0)) do
      withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
        withCurrHeartbeats do
          withEnableInfoTree false do
            setGoals [g]
            withoutRecover <| Term.withoutErrToSorry <| evalTactic stx
            if (← instantiateMVars (mkMVar g)).hasSorry then throwError "sorry"
            let gs ← getUnsolvedGoals
            if closing && !gs.isEmpty then throwError "goals remain"
            return Except.ok gs)
    fun ex => do
      if let some o := outer then
        if ← o.isSet then throw ex
      return .error (if ex.isInterrupt then .time else if ex.isMaxHeartbeat then .heartbeats else .error)
  let ms' := (← IO.monoMsNow) - t0
  if let .error _ := r then s.restore
  trace[kblock] "{text}: {match r with | .ok _ => "ok" | .error f => f.name} ({ms'} ms)"
  return ⟨r, ms'⟩

/-- A structural step (not a closer): the goals that it leaves, or `none`. -/
meta def step (cx : Cx) (g : MVarId) (text : String) : TacticM (Option (List MVarId)) := do
  match (← run cx cx.limits.stepHeartbeats cx.limits.stepMs g text false).result with
  | .ok gs => return some gs
  | .error _ => return none

/-! ### The steps of a class -/

/-- The steps for a leaf of class `cls`, cheapest first: the class steps, then `kfinish` with and
without `mem_simp`, with the hints, with `Inside.of_toNat`. `mapped` are the names of the
`Mem.Mapped` hypotheses; a step for a leaf that uses them names one. -/
meta def recipes (cx : Cx) (cls : Cls) (mapped : Array Name) : Array Recipe :=
  let L := cx.limits
  let cheap (t : String) : Recipe := { text := t, heartbeats := 2000, ms := 2000 }
  let stepR (t : String) : Recipe := { text := t, heartbeats := L.stepHeartbeats, ms := L.stepMs }
  let kf (stage : Nat) (t : String) : Recipe :=
    { text := t, heartbeats := L.kfinishHeartbeats, ms := L.kfinishMs, stage }
  let n (h : Name) : String := h.toString (escape := true)
  let viaMapped : Array String := Id.run do
    let mut out := #[]
    for pre in ["", "mem_simp; ", "mem_simp at *; "] do
      for h in mapped do
        out := out.push (if pre.isEmpty then s!"kb_mapped {n h}" else s!"({pre}kb_mapped {n h})")
    return out
  let ofClass : Array Recipe :=
    match cls with
    | .isSome | .mapped => viaMapped.map stepR
    | .disjoint => #[stepR "kb_disj"]
    | .inside => #[stepR "(mem_simp; done)", stepR "kb_inside"]
    | .stackBelow | .stackAtOrBelow | .all => #[stepR "kb_stack"]
    | .writesOnly => #[
        { text := "kb_frame", heartbeats := 2 * L.stepHeartbeats, ms := L.stepMs },
        { text := "(mem_simp; kb_frame)", heartbeats := 2 * L.stepHeartbeats, ms := L.stepMs }]
    | .eq "Int64" => #[stepR "(kb_load; first | exact Int64.ofBitVec_ofBytes_toBytes _ | (simp only [Option.map_some, Option.get!_some]; exact Int64.ofBitVec_ofBytes_toBytes _) | (simp [Int64.ofBitVec_ofBytes_toBytes]; done))"]
    | .eq "UInt64" | .eq "BitVec" => #[
        stepR "exact UInt64.toBitVec_inj.mp (by simp only [UInt64.toBitVec_ofBitVec]; kb_bv)",
        stepR "kb_bv",
        stepR "(kb_load; simp only [Option.get!_some]; exact UInt64.ofBytes_toBytes _)"]
    | .eq "Option" => #[stepR "(kb_load; done)"]
    | _ => #[]
  let hintList := ", ".intercalate cx.hints.toList
  let hinted (stage : Nat) (pre : String) : Array Recipe :=
    if cx.hints.isEmpty then #[]
    else #[kf stage (if pre.isEmpty then s!"kfinish [{hintList}]" else s!"({pre}kfinish [{hintList}])")]
  let separation : Array Recipe :=
    match cls with
    | .isSome | .mapped | .disjoint | .inside | .writesOnly | .eq "Option" =>
      if L.ecancel then #[{ stepR "ecancel" with stage := 1 }, { stepR "(simp; ecancel)" with stage := 1 }]
      else #[]
    | _ => #[]
  #[cheap "rfl", cheap "trivial"] ++ ofClass ++ cx.extra cls ++
    #[kf 1 "kfinish"] ++ hinted 1 "" ++ #[kf 2 "(mem_simp; kfinish)"] ++ hinted 2 "mem_simp; " ++
    #[kf 3 "kfinish [Mem.Blocks.Inside.of_toNat]", kf 3 "(mem_simp; kfinish [Mem.Blocks.Inside.of_toNat])"] ++
    separation

/-! ### The tree of a search -/

/-- A leaf: the goal that no split reduces. `step` is the text that closed it, `none` if open
(then `goal` is the open goal). -/
meta structure Leaf where
  path : String
  kind : Cls
  step : Option String
  ms : Nat
  fails : Array Failure
  goal : Option MVarId := none
  note : String := ""

/-- The tactics that were applied, and what is left: a node with the splits as children, or a
leaf. A node with no children is a goal that its tactics closed. -/
meta inductive Tree where
  | leaf (l : Leaf)
  | node (steps : Array String) (kids : Array Tree)

meta instance : Inhabited Tree := ⟨.node #[] #[]⟩

meta partial def Tree.leaves : Tree → Array Leaf
  | .leaf l => #[l]
  | .node _ kids => kids.flatMap Tree.leaves

/-- The lines of the script of a tree. A child of a node with two or more children is a bullet. -/
meta partial def Tree.render : Tree → Array String
  | .leaf l =>
    match l.step with
    | some t => #[t]
    | none => #[s!"sorry -- {l.path} {l.kind.name}"]
  | .node steps kids =>
    if kids.size == 1 then steps ++ kids[0]!.render
    else steps ++ kids.flatMap fun k =>
      k.render.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l

/-! ### The split and the leaves -/

/-- Tries the steps of stage `stage` of the leaf's class on its goal; the leaf records the step
that closed it, or stays open. A leaf without a goal, or one that is skipped, is not changed. -/
meta def tryStage (cx : Cx) (stage : Nat) (l : Leaf) : TacticM Leaf := do
  let some g := l.goal | return l
  if !l.note.isEmpty then return l
  let mapped ← g.withContext (hypNames ``Mem.Mapped)
  let mut ms := l.ms
  let mut fails := l.fails
  for r in recipes cx l.kind mapped do
    unless r.stage == stage do continue
    let res ← run cx r.heartbeats r.ms g r.text true
    ms := ms + res.ms
    match res.result with
    | .ok _ => return { l with step := some r.text, ms, fails, goal := none }
    | .error f => fails := fails.push f
  return { l with ms, fails }

/-- A new leaf, with the steps of stage 0 tried. -/
meta def leafOf (cx : Cx) (path : String) (cls : Cls) (g : MVarId) : TacticM Leaf := do
  if let some why := cx.skip path then
    return { path, kind := cls, step := none, ms := 0, fails := #[], goal := some g, note := why }
  tryStage cx 0 { path, kind := cls, step := none, ms := 0, fails := #[], goal := some g }

/-- The last stage of the steps. -/
meta def lastStage : Nat := 3

/-- `f` on each leaf of the tree, in order. -/
meta partial def Tree.mapLeaves (f : Leaf → TacticM Leaf) : Tree → TacticM Tree
  | .leaf l => return .leaf (← f l)
  | .node steps kids => return .node steps (← kids.mapM (Tree.mapLeaves f))

/-- The steps of stages 1 to `lastStage` on the leaves of the tree that are open. -/
meta def Tree.finish (cx : Cx) (t : Tree) : TacticM Tree := do
  let mut t := t
  for stage in [1:lastStage + 1] do
    t ← t.mapLeaves (tryStage cx stage)
  return t

/-- The number of labels of the list `ls` of `Program.Intercept ls s₀ I' E a s`. -/
meta def interceptLabels (e : Expr) : Nat :=
  (((e.getAppArgs[1]?).bind (·.listLit?)).map (·.2.length)).getD 0

mutual

/-- The tree of the goal `g` at `path`: splits `∧`, `Program.Intercept`, `∃` (witness `0`, kept
only if every leaf closes) and an invariant behind a `match` on the label; a leaf otherwise. -/
meta partial def solve (cx : Cx) (path : String) (g : MVarId) : TacticM Tree := do
  let cls ← g.withContext do classify (← g.getType)
  let asLeaf : TacticM Tree := return .leaf (← leafOf cx path cls g)
  match cls with
  | .and => return (← splitAnd cx path 1 g).getD (← asLeaf)
  | .intercept =>
    let n := interceptLabels (← g.withContext do instantiateMVars (← g.getType))
    for i in [0:n] do
      let s ← saveState
      let t1 := s!"apply Program.Intercept.intro_label (i := {i}) rfl"
      if let some [g1] ← step cx g t1 then
        if let some [ga, gb] ← step cx g1 "refine Or.inl ⟨?_, ?_⟩" then
          return .node #[t1, "refine Or.inl ⟨?_, ?_⟩"]
            #[← solve cx s!"{path}.L{i}.stack" ga, ← solve cx s!"{path}.L{i}.inv" gb]
      s.restore
    if let some [ga, gb] ← step cx g "refine Or.inr ⟨?_, ?_⟩" then
      return .node #["refine Or.inr ⟨?_, ?_⟩"]
        #[← solve cx s!"{path}.E" ga, ← solve cx s!"{path}.stack" gb]
    asLeaf
  | .ex =>
    let s ← saveState
    if let some [g1] ← step cx g "refine Exists.intro 0 ?_" then
      let t ← (← solve cx s!"{path}.w0" g1).finish cx
      if t.leaves.all (·.step.isSome) then return .node #["refine Exists.intro 0 ?_"] #[t]
    s.restore
    asLeaf
  | .invariant =>
    let s ← saveState
    match ← step cx g "dsimp only" with
    | some [] => return .leaf { path, kind := cls, step := some "dsimp only", ms := 0, fails := #[] }
    | some [g1] =>
      let cls1 ← g1.withContext do classify (← g1.getType)
      if cls1.name != cls.name then return .node #["dsimp only"] #[← solve cx path g1]
      s.restore
      asLeaf
    | _ => asLeaf
  | _ => asLeaf

/-- `a₁ ∧ a₂ ∧ … ∧ aₖ`, one `constructor` for each `∧`; the conjuncts are `path.i`, `path.(i+1)`,
… so that a path names the position of a conjunct of an invariant. -/
meta partial def splitAnd (cx : Cx) (path : String) (i : Nat) (g : MVarId) : TacticM (Option Tree) := do
  let some [g1, g2] ← step cx g "constructor" | return none
  let t1 ← solve cx s!"{path}.{i}" g1
  let cls2 ← g2.withContext do classify (← g2.getType)
  let t2 ← match cls2 with
    | .and =>
      match ← splitAnd cx path (i + 1) g2 with
      | some t => pure t
      | none => pure (.leaf (← leafOf cx s!"{path}.{i + 1}" cls2 g2))
    | _ => solve cx s!"{path}.{i + 1}" g2
  return some (.node #["constructor"] #[t1, t2])

end

/-- A verification condition: `kb_hyps` and `expose_names` first (the steps name hypotheses),
then `solve`. `kb_hyps` closes the entry VC (`s' = s₀` at the first label). -/
meta def vc (cx : Cx) (g : MVarId) : TacticM Tree := do
  let tag ← g.getTag
  let path := if tag.isAnonymous then "goal" else tag.eraseMacroScopes.toString
  match ← step cx g "kb_hyps" with
  | some [] => return .leaf { path, kind := .other "entry", step := some "kb_hyps", ms := 0, fails := #[] }
  | some [g1] =>
    match ← step cx g1 "expose_names" with
    | some [g2] => return .node #["kb_hyps", "expose_names"] #[← solve cx path g2]
    | _ => return .node #["kb_hyps"] #[← solve cx path g1]
  | _ => solve cx path g

/-! ### Reports and the script -/

meta def fmtMs (ms : Nat) : String := s!"{ms / 1000}.{ms % 1000 / 100} s"

/-- A line of the report: the path, the class, the step or `open`, the time. -/
meta def Leaf.report (times : Bool) (l : Leaf) : String :=
  let count (f : Failure → Bool) := (l.fails.filter f).size
  let what := match l.step with
    | some t => t
    | none =>
      let why := if l.note.isEmpty then
          s!"{l.fails.size} attempts: {count (·matches .error)} failed, {count (·matches .time)} time, {count (·matches .heartbeats)} heartbeats"
        else l.note
      s!"open ({why})"
  s!"{l.path} {l.kind.name}: {what}" ++ (if times then s!" ({fmtMs l.ms})" else "")

/-- The lines of the script for the goals `items` (tag and tree). One goal with no tag is the
script itself; else each goal is a `case`, or a bullet when it has no tag. -/
meta def scriptLines (items : Array (Name × Tree)) : Array String :=
  if items.size == 1 && items[0]!.1.isAnonymous then items[0]!.2.render
  else items.flatMap fun (tag, t) =>
    if tag.isAnonymous then t.render.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
    else #[s!"case {tag.eraseMacroScopes} =>"] ++ t.render.map ("  " ++ ·)

/-! ### The tactics -/

/-- Runs the search with `cx` on the goals. The search runs without the heartbeat limit of the
command, each attempt with its own limit, and gives the heartbeats back at its end: the heartbeats
count per command, and a search of many attempts would stop the command at its next check. -/
meta def searchWith (cx : Cx) : TacticM (Array (Name × Tree)) := do
  let h0 ← IO.getNumHeartbeats
  let goals ← getUnsolvedGoals
  try
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
      let items ← goals.toArray.mapM fun g => do return ((← g.getTag), ← vc cx g)
      -- the later stages, over all the goals: the time goes to the steps in the order of their stage
      let mut items := items
      for stage in [1:lastStage + 1] do
        items ← items.mapM fun (tag, t) => do return (tag, ← t.mapLeaves (tryStage cx stage))
      return items
  finally
    IO.setNumHeartbeats h0

/-- The search with the limits of the options; the time of the search in ms. -/
meta def search (hints : Array String) : TacticM (Array (Name × Tree) × Nat) := do
  let limits := Limits.get (← getOptions)
  let t0 ← IO.monoMsNow
  let items ← searchWith { limits, hints, deadline := t0 + limits.totalMs }
  return (items, (← IO.monoMsNow) - t0)

meta def summary (times : Bool) (items : Array (Name × Tree)) (ms : Nat) : String :=
  let leaves := items.flatMap (·.2.leaves)
  let closed := leaves.filter (·.step.isSome)
  let goalsClosed := items.filter fun (_, t) => t.leaves.all (·.step.isSome)
  s!"kblock: {closed.size} of {leaves.size} leaves closed, {goalsClosed.size} of {items.size} goals closed" ++ (if times then s!", {fmtMs ms}" else "")

meta def report (items : Array (Name × Tree)) (ms : Nat) : TacticM String := do
  let all := (← getOptions).get `kblock.reportAll (true : Bool)
  let times := (← getOptions).get `kblock.times (true : Bool)
  let leaves := items.flatMap (·.2.leaves)
  let shown := if all then leaves else leaves.filter (·.step.isNone)
  return "\n".intercalate (summary times items ms :: (shown.map fun l => "  " ++ l.report times).toList)

/-- `kblock? [h₁, …]`: searches, prints the report and the script, and does not change the goals.
The hints are lemma names, or lemmas with arguments, for `kfinish [h₁, …]`. -/
syntax (name := kblockQ) "kblock?" (" [" term,* "]")? : tactic

/-- `kblock [h₁, …]`: the same search, applied: the goals that stay are the open leaves. -/
syntax (name := kblockT) "kblock" (" [" term,* "]")? : tactic

/-- The text of the hints, as written. -/
meta def hintNames (hs : Option (Syntax.TSepArray `term ",")) : Array String :=
  (hs.map fun hs => hs.getElems.map fun h =>
    " ".intercalate (((h.raw.reprint.getD "").replace "\n" " ").splitOn " " |>.filter (· ≠ ""))).getD #[]

@[tactic kblockQ] meta def evalKblockQ : Tactic.Tactic := fun stx => do
  let `(tactic| kblock? $[[$hs,*]]?) := stx | throwUnsupportedSyntax
  let saved ← saveState
  let (items, ms) ← search (hintNames hs)
  saved.restore
  -- the indentation of the line of the tactic, as the script goes in its place
  let fileMap ← getFileMap
  let col := (stx.getPos?.map fun p =>
    let line := ((fileMap.source.splitOn "\n")[(fileMap.toPosition p).line - 1]?).getD ""
    (line.toList.takeWhile (· == ' ')).length).getD 0
  let pad := "".pushn ' ' col
  let lines := scriptLines items
  let script := ("\n" ++ pad).intercalate lines.toList
  logInfo (← report items ms)
  logInfo m!"Try this:\n{pad}{script}"

@[tactic kblockT] meta def evalKblockT : Tactic.Tactic := fun stx => do
  let `(tactic| kblock $[[$hs,*]]?) := stx | throwUnsupportedSyntax
  let (items, ms) ← search (hintNames hs)
  let open_ := items.flatMap (·.2.leaves) |>.filterMap fun l => l.goal.map (l.path, ·)
  for (path, g) in open_ do
    g.setTag (Name.mkSimple path)
  setGoals (open_.map (·.2)).toList
  logInfo (← report items ms)

end Kb
