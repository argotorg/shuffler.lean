import Lean
import Lift.Sem.Blocks
import Skel.Lean.Refute
import NxLift.Proc
import Skel.Discover.Features

/-! The step and the pool of a machine loop site (`docs/research/invariant-discovery-design-20261119.md`, sections 3.1 and
3.3 (b), task D11b). A machine site is a head label `H` of a `Leaf` model `b` (`blocksP`). Its step is one pass of the blocks
from `H` (what `Skel.Refute.stepTo` runs): the arm of `H`, and the arm of each label that a `goto` reaches, until a `goto H`.

`machineStepExpr b H` builds that step as an `Expr` `fun (st : σ) => B : σ → Step σ R`. It takes the value of `b`, puts the label
for the argument of its step function and reduces the `match` on the label. In the tail positions of the arm (`if`, `if h :`,
`let` and the matchers that the elaborator makes) a `Res.ok (Next.goto H y)` becomes `Step.cont y`, a `Res.ok (Next.goto L y)` of
another label is the arm of `L` at `y`, a `Res.ok (Next.ret r)` becomes `Step.exit r`, and `Res.stuck` and `Res.noFuel` become
`Step.fault`. With the runner `run : ∀ f, X f → Res (Y f)` of the callee (DISC-CALL), a `Res.ok (Next.call f a k)` becomes
`callStep (run f a) (fun y => <the goto of k y>)`: the callee steps to its return with the result of the runner, which is the
callee's L3 spec, as `Skel.Refute.inline` runs it. The errors name the cause: a name that is no constant or no label, a model
that is no `Blocks`, a label that a pass reaches twice before `H` (a loop inside the pass), a call with no runner, a
continuation that is no pair, an arm that has no tail form.

`machinePoolOf` is `poolOf` (D4, D4b) of that step, without the frame atoms: the slots of the loop row have no entry state.
The skeleton holds the model as text, so the pool runs in a Lean process: `poolFile` is a file with the model and an `#eval` that
prints the pool as one JSON line, and `runPool` runs it and reads that line. -/

namespace Skel.Discover

open Lean Meta Lift.Sem

private abbrev MM := ExceptT String MetaM

/-- The step after a call: `k y` for the result `y` of the callee, else a fault (a callee that is stuck or out of fuel). -/
def callStep.{u, v} {Y : Type} {σ : Type u} {R : Type v} (r : Res Y) (k : Y → Step σ R) : Step σ R :=
  match r with
  | .ok y => k y
  | _ => .fault

/-- What the pass needs: the step function of the blocks, the head, and the types of the step. -/
private structure MCtx where
  stepFn : Expr
  head : Name
  stateTy : Expr
  out : Expr
  stepTy : Expr
  stepLevel : Level
  /-- The runner of the callee (`∀ f, X f → Res (Y f)`), if the blocks have one. -/
  callee : Option Expr := none

private def ofE {α : Type} : Except String α → MM α
  | .ok a => pure a
  | .error e => throwThe String e

private def mcont (c : MCtx) (y : Expr) : MM Expr := liftM (mkAppOptM ``Step.cont #[c.stateTy, c.out, y] : MetaM Expr)
private def mexit (c : MCtx) (r : Expr) : MM Expr := liftM (mkAppOptM ``Step.exit #[c.stateTy, c.out, r] : MetaM Expr)
private def mfault (c : MCtx) : MM Expr := liftM (mkAppOptM ``Step.fault #[c.stateTy, c.out] : MetaM Expr)

/-- The step of the tail value `e` by `k` at each leaf, through `let`, `if`, `if h :` and the matchers. -/
private partial def push (c : MCtx) (k : Expr → MM Expr) (e : Expr) : MM Expr := do
  let under (f : Expr) (n : Nat) : MM Expr := do
    forallBoundedTelescope (← inferType f) (some n) fun xs _ => do mkLambdaFVars xs (← k (f.beta xs))
  if let .letE n t v b _ := e then
    return ← withLetDecl n t v fun x => do mkLetFVars #[x] (← k (b.instantiate1 x))
  if e.isAppOfArity ``ite 5 then
    let #[_, p, inst, t, f] := e.getAppArgs | throwThe String "an if with no branches"
    return ← liftM (mkAppOptM ``ite #[c.stepTy, p, inst, ← k t, ← k f] : MetaM Expr)
  if e.isAppOfArity ``dite 5 then
    let #[_, p, inst, t, f] := e.getAppArgs | throwThe String "an if with no branches"
    return ← liftM (mkAppOptM ``dite #[c.stepTy, p, inst, ← under t 1, ← under f 1] : MetaM Expr)
  if let some m ← matchMatcherApp? e then
    unless m.remaining.isEmpty do throwThe String "a match with arguments after its alternatives"
    let motive ← lambdaTelescope m.motive fun xs _ => mkLambdaFVars xs c.stepTy
    let levels := match m.uElimPos? with
      | some pos => m.matcherLevels.set! pos c.stepLevel
      | none => m.matcherLevels
    let alts ← (m.alts.zip m.altNumParams).mapM fun (alt, n) => under alt n
    return { m with motive, matcherLevels := levels, alts }.toExpr
  throwThe String s!"an arm with no tail form: {(← ppExpr e).pretty 200}"

mutual
/-- The arm of the label `l` at the state `x`, after the labels `seen` of the pass. -/
private partial def arm (c : MCtx) (seen : List Name) (l x : Expr) : MM Expr := do
  let some lc := l.consumeMData.constName? | throwThe String "a goto to a label that is no constructor"
  let body := (mkApp2 c.stepFn l x).headBeta
  match ← reduceMatcher? body with
  | .reduced e => resTail c (lc :: seen) e.headBeta
  | _ => throwThe String s!"the arm of {lc} does not reduce"

/-- The step of a tail value of the type `Res (Next …)`. -/
private partial def resTail (c : MCtx) (seen : List Name) (e : Expr) : MM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Res.ok 2 then return ← nextTail c seen e.appArg!
  if e.isAppOfArity ``Res.stuck 2 || e.isAppOfArity ``Res.noFuel 1 then return ← mfault c
  push c (resTail c seen) e

/-- The step of a tail value of the type `Next …`. -/
private partial def nextTail (c : MCtx) (seen : List Name) (e : Expr) : MM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Next.goto 8 then return ← gotoTail c seen (e.getArg! 6) (e.getArg! 7)
  if e.isAppOfArity ``Next.ret 7 then return ← mexit c (e.getArg! 6)
  if e.isAppOfArity ``Next.call 9 then return ← callTail c seen (e.getArg! 6) (e.getArg! 7) (e.getArg! 8)
  push c (nextTail c seen) e

/-- The step of a jump to the label `l` with the state `y`: `Step.cont y` at the head, else the arm of `l`. -/
private partial def gotoTail (c : MCtx) (seen : List Name) (l y : Expr) : MM Expr := do
  let some lc := l.consumeMData.constName? | throwThe String "a goto to a label that is no constructor"
  if lc == c.head then return ← mcont c y
  if seen.contains lc then throwThe String s!"a loop inside the pass: the label {lc} is reached twice before the head {c.head}"
  arm c seen l y

/-- The step of a call of `f` on `a` that goes on at `k y`: `callStep (run f a) (fun y => <the jump of k y>)`. -/
private partial def callTail (c : MCtx) (seen : List Name) (f a k : Expr) : MM Expr := do
  let some run := c.callee | throwThe String "a call in the pass with no runner of the callee"
  let r := mkApp2 run f a
  let rTy ← whnf (← inferType r)
  unless rTy.isAppOfArity ``Res 1 do throwThe String "the runner of the callee does not give a Res"
  let yTy := rTy.appArg!
  let body ← withLocalDeclD `y yTy fun y => do
    let ky ← whnfCore (k.beta #[y]).headBeta
    unless ky.isAppOfArity ``Prod.mk 4 do throwThe String "the continuation of a call is no pair"
    mkLambdaFVars #[y] (← gotoTail c seen (ky.getArg! 2) (ky.getArg! 3))
  liftM (mkAppOptM ``callStep #[yTy, c.stateTy, c.out, r, body] : MetaM Expr)
end

/-- `e` with each projection of a constructor application replaced by its field (`(St.mk a b c).rcx` is `c`; also the
projection functions). A pass puts the state of a `goto` (a `{ x with … }`, so a constructor whose fields project `x`) into
the arm of the next label, so after `k` blocks the state is a tree of about `fields ^ k` nodes with sharing: the pool walk
visits the tree (DISC-PILOT: the pass of `closestCopy` at `LBB29_1` had 8305806191 nodes, 6191 after this). `transform`
visits each shared node once. -/
def projReduce (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match e with
    | .proj _ i s =>
      match ← projectCore? s.consumeMData i with
      | some v => pure (.visit v)
      | none => pure (.done e)
    | .app .. =>
      let some c := e.getAppFn.constName? | return .done e
      let some info ← getProjectionFnInfo? c | return .done e
      if info.fromClass || e.getAppNumArgs < info.numParams + 1 then return .done e
      let args := e.getAppArgs
      match ← projectCore? args[info.numParams]!.consumeMData info.i with
      | some v => pure (.visit (mkAppN v (args.extract (info.numParams + 1) args.size)))
      | none => pure (.done e)
    | _ => pure (.done e))

/-- The step function of the blocks value `e` and the runner of its callee: a `Blocks.mk` gives its step with no runner, a constant
its value, and `Skel.Refute.inline b run` the step of `b` with the runner `run`. -/
private def stepOfValue : Nat → Expr → MetaM (Option (Expr × Option Expr))
  | 0, _ => pure none
  | fuel + 1, e => do
    let e ← whnfCore e.consumeMData
    if e.isAppOfArity ``Blocks.mk 7 then return some (e.appArg!, none)
    if e.isAppOfArity ``Skel.Refute.inline 8 then
      return (← stepOfValue fuel (e.getArg! 6)).map fun (f, _) => (f, some (e.getArg! 7))
    let some n := e.getAppFn.constName? | return none
    let some (.defnInfo info) := (← getEnv).find? n | return none
    let v ← instantiateValueLevelParams (.defnInfo info) e.getAppFn.constLevels!
    stepOfValue fuel (mkAppN v e.getAppArgs).headBeta

/-- The step `fun (st : σ) => B : σ → Step σ R` of one pass of the blocks `blocks` from the head label `head`, or the error that
names why there is none. The projections of the states of the pass are reduced (`projReduce`). Blocks `Skel.Refute.inline b run`
are the blocks `b` with the runner `run` of the callee; `callee` names a runner of the callee of blocks with calls. -/
def machineStepExpr (blocks head : Name) (callee : Option Name := none) : MetaM (Except String Expr) := do
  let some (.defnInfo _) := (← getEnv).find? blocks | return .error s!"no definition {blocks}"
  let ty ← whnfR (← inferType (mkConst blocks))
  unless ty.isAppOfArity ``Blocks 6 do return .error s!"{blocks} is not a Blocks model"
  let some (.ctorInfo ci) := (← getEnv).find? head | return .error s!"no label {head} of {blocks}"
  unless ty.getArg! 0 |>.isConstOf ci.induct do return .error s!"no label {head} of {blocks}"
  let some (stepFn, inlined) ← stepOfValue 4 (mkConst blocks) | return .error s!"the value of {blocks} is not a Blocks structure"
  let args := ty.getAppArgs
  let stateTy := args[1]!
  let out := args[2]!
  let stepTy ← mkAppM ``Step #[stateTy, out]
  if let some n := callee then
    unless (← getEnv).contains n do return .error s!"no runner {n} of the callee"
  let c : MCtx := { stepFn, head, stateTy, out, stepTy, stepLevel := ← getLevel stepTy,
                    callee := (callee.map mkConst) <|> inlined }
  withLocalDeclD `st stateTy fun st => do
    match ← (arm c [] (mkConst head) st).run with
    | .error e => pure (.error s!"{blocks} at {head}: {e}")
    | .ok body =>
      let step ← mkLambdaFVars #[st] (← projReduce body)
      try check step; pure (.ok step)
      catch ex => pure (.error s!"{blocks} at {head}: the step does not type check: {← ex.toMessageData.toString}")

/-- The pool of the machine site of the blocks `blocks` at the head `head` (D4 and D4b on its step), without the frame atoms. -/
def machinePoolOf (blocks head : Name) (callee : Option Name := none) : MetaM (Except String Pool) := do
  match ← machineStepExpr blocks head callee with
  | .error e => pure (.error e)
  | .ok step =>
    let p ← poolOf step
    pure (.ok { p with atoms := p.atoms.filter fun (a, _) => !(a matches .frameEq _) })

/-- The constructor `label` of the label type of the blocks `blocks`, or the error that names why there is none. -/
def labelOf (blocks : Name) (label : String) : MetaM (Except String Name) := do
  let some _ := (← getEnv).find? blocks | return .error s!"no definition {blocks}"
  let ty ← whnfR (← inferType (mkConst blocks))
  unless ty.isAppOfArity ``Blocks 6 do return .error s!"{blocks} is not a Blocks model"
  let some l := (ty.getArg! 0).constName? | return .error s!"{blocks} has a label type that is no constant"
  let head := l.str label
  match (← getEnv).find? head with
  | some (.ctorInfo _) => pure (.ok head)
  | _ => pure (.error s!"no label {label} of {blocks}")

/-- The pool of the blocks `blocks` at the label `label` as one line `POOL <json>`, or `POOL-ERROR <why>`. -/
def machinePoolLine (blocks : Name) (label : String) (callee : Option Name := none) : MetaM String := do
  match ← labelOf blocks label with
  | .error e => pure ("POOL-ERROR " ++ e)
  | .ok head =>
    match ← machinePoolOf blocks head callee with
    | .ok p => pure ("POOL " ++ (toJson p).compress)
    | .error e => pure ("POOL-ERROR " ++ e)

/-- Prints `machinePoolLine`; the `#eval` of the pool file runs it. -/
def printMachinePool (blocks : Name) (label : String) (callee : Option Name := none) : MetaM Unit := do
  IO.println (← machinePoolLine blocks label callee)

/-- The pool file: the imports, the namespace `ns`, the opens, the model text, and the `#eval` of the pool of the blocks
`blocks` (a name in the namespace) at the label `head` (a constructor name of its label type, with no prefix), with the runner
`callee` of the callee (a name in the namespace that the model text defines) when it is given. -/
def poolFile (imports : List String) (ns : String) (opens : String) (model : String) (blocks head : String)
    (callee : Option String := none) : String :=
  let run := match callee with
    | some n => s!" (some ``{n})"
    | none => ""
  "\n".intercalate
    ((("Skel.Discover.Machine" :: imports).eraseDups.map ("import " ++ ·)) ++
      [ "set_option linter.all false", s!"namespace {ns}", s!"open {opens}", model, "",
        s!"#eval Skel.Discover.printMachinePool ``{blocks} {head.quote}{run}", s!"end {ns}", "" ])

/-- The pool of an output of the pool file, or the error that names why there is none. -/
def parsePoolOutput (out : String) : Except String Pool := do
  let lines := out.splitOn "\n"
  if let some l := lines.find? (fun l => (l.splitOn "POOL-ERROR ").length > 1) then
    throw ((l.splitOn "POOL-ERROR ").getLast!)
  let some l := lines.find? (fun l => (l.splitOn "POOL ").length > 1) | throw s!"no pool in the output: {(out.take 300).toString}"
  let j ← Json.parse ((l.splitOn "POOL ").getLast!)
  fromJson? j

/-- Writes the pool file to `file`, runs it with `lake env lean` for at most `limitMs` milliseconds, and reads the pool. -/
def runPool (text : String) (file : System.FilePath) (limitMs : Nat) : IO (Except String Pool) := do
  if let some dir := file.parent then IO.FS.createDirAll dir
  IO.FS.writeFile file text
  let r ← NxLift.Proc.runLean #[file.toString] limitMs
  match r.ending with
  | .timedOut _ => pure (.error "the pool file timed out")
  | .exited 0 => pure (parsePoolOutput r.output)
  | .exited n =>
    match parsePoolOutput r.output with
    | .error e => pure (.error s!"lean exited with {n}: {e}")
    | .ok p => pure (.ok p)

/-- The measures of a pool: each feature as a measure of one component, in the order of the pool. -/
def Pool.measures (p : Pool) : List Measure := p.features.map (.one ·.1)

end Skel.Discover
