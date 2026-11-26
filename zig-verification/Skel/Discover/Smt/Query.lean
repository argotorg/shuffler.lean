import Lean
import Skel.Discover.Smt.Ts
import Lift.Inv.Gen.TS
import Lift.Inv.Gen.Sygus
import Lift.Smt.Solver
import Lift.Smt.Sexp

/-! The solver queries and the runners of the invariant discovery (`docs/research/invariant-discovery-solver-20261119.md`,
task S2).

The input is the `Lift.Inv.Gen.Loop.TS` of a site (`Sys.toTS` of `Skel/Discover/Smt/Ts.lean`). The module makes three queries:

* `fuelTS t fuel`: `t` with a ghost step counter and the fuel at the entry, as a `Safety` problem. A head with `steps ≥ fuel0`
  is a call at fuel 0 (a bad state), so the fuel is enough iff no bad state is reachable. `Safety.horn` prints it for z3
  Spacer (`sat`: safe, with an invariant over the state, the ghosts and the frame) and `Safety.synthInv` for cvc5 `synth-inv`.
* `rankQuery t consts`: the invariant and the ranking function of `TS.rankQuery`, with the constants `consts` in the grammar
  of the ranking function (the grammar of `TS.rankQuery` has `0` and `1` only).

A `Query` carries its text, the functions that the answer must define, and their arity. `runQuery` and `runSite` run the solver
under a time limit (20 s for a query, 60 s for a site) and give a `Run`: the `Result`, the solver and its version, the hash of
the query and the time. Nothing in Lean trusts the answer: `Result.solved` has the `define-fun` texts (`Def`), as a proposal.

The cache keeps the text that the solver printed, in one file for each query, `<solver>-<hash>.json`. The key is the hash of the
solver name, the solver version and the text of the query; the file repeats the three, and a file whose hash is not the key is
not used and is written again by the next live run. A run with a cache directory and no solver on the path (`cmd` that does not
run) takes the version from `pinnedVersion` (the version of the `flake.lock` of this repository), so a test needs no solver. Only
the answers `sat`, `unsat`, `infeasible` and the solutions are kept: a time limit depends on the limit. -/

namespace Skel.Discover.Smt

open Lean Lift.Smt

/-- The transition system of `Lift.Inv.Gen.Loop`. -/
abbrev LTS := Lift.Inv.Gen.Loop.TS

/-! ## The fuel as safety -/

/-- A transition system and the states that must be unreachable: `steps ≥ fuel0`. -/
structure Safety where
  ts : LTS
  /-- The ghost counter: 0 at the entry, `+ 1` on each path back to the head. A state variable of `ts`. -/
  steps : String
  /-- The fuel at the entry: a frame variable of `ts`, which no path changes. -/
  fuel0 : String
  deriving Repr

/-- The bad states: a head that is a call at fuel 0. -/
def Safety.bad (s : Safety) : String := s!"(>= {s.steps} {s.fuel0})"

/-- `n` without its suffix `_p`. -/
private def stem (n : String) : Option String := if n.endsWith "_p" then some (n.dropEnd 2).toString else none

/-- The ghost names are fresh: a name `c` that `t` does not use, and its primed name `c_p` neither. -/
def ghostNames (t : LTS) : String × String :=
  let used := t.vars.map (·.name) |>.flatMap fun n => [n, n ++ "_p"]
  let taken := used ++ used.filterMap stem
  let steps := freshName taken "steps"
  (steps, freshName (steps :: taken) "fuel0")

/-- `t` with the ghost counter, and the fuel `fuel` (an SMT term over the state variables of the entry) as the frame
variable `fuel0`. -/
def fuelTS (t : LTS) (fuel : String) : Safety :=
  let (steps, fuel0) := ghostNames t
  { ts := { t with
      state := t.state ++ [{ name := steps, kind := .nat }]
      frame := t.frame ++ [{ name := fuel0, kind := .nat }]
      paths := t.paths.map fun p => { p with next := p.next ++ [(steps, s!"(+ {steps} 1)")] }
      entries := t.entries.map fun (pc, vals) => (pc ++ [s!"(= {steps} 0)", s!"(= {fuel0} {fuel})"], vals) },
    steps, fuel0 }

/-! ## The queries -/

/-- The solver that a query is for. -/
inductive Which where
  | z3
  | cvc5
  deriving BEq, Repr, Inhabited

def Which.name : Which → String
  | .z3 => "z3"
  | .cvc5 => "cvc5"

/-- The versions of the solvers of the `flake.lock` (`nix develop -c z3 --version`, `cvc5 --version`): the first line. -/
def Which.pinnedVersion : Which → String
  | .z3 => "Z3 version 5.3.2 - 64 bit"
  | .cvc5 => "cvc5 1.4.0"

/-- A query: its text, the solver, and what the answer must define: the name and the sort of each function, over `arity`
arguments. -/
structure Query where
  which : Which
  text : String
  funs : List (String × String)
  arity : Nat
  deriving Repr, Inhabited

private def sorted (vs : List Lift.Inv.Gen.Loop.Var) (suffix : String := "") : String :=
  " ".intercalate (vs.map fun v => s!"({v.name}{suffix} Int)")

private def primedVars (vs : List Lift.Inv.Gen.Loop.Var) : List Lift.Inv.Gen.Loop.Var :=
  vs.map fun v => { name := Lift.Inv.Gen.Loop.prime v, kind := v.kind }

/-- The clauses of `s` for z3 Spacer, as `(set-logic HORN)`: `sat` is safe, and `(get-model)` gives the interpretation of
`inv` over the state and the frame. -/
def Safety.horn (s : Safety) : Query :=
  let t := s.ts
  let sv := t.state ++ t.frame
  let all := t.vars ++ primedVars t.state
  let invAt (suffix : String) : String :=
    s!"(inv {" ".intercalate ((t.state.map fun v => v.name ++ suffix) ++ t.frame.map (·.name))})"
  { which := .z3, funs := [("inv", "Bool")], arity := sv.length,
    text := "\n".intercalate [
      "(set-logic HORN)",
      s!"(declare-fun inv ({" ".intercalate (sv.map fun _ => "Int")}) Bool)",
      s!"(assert (forall ({sorted all}) (=> (and {t.dom} {t.init}) {invAt ""})))",
      s!"(assert (forall ({sorted all}) (=> (and {t.dom} {invAt ""} {t.cont true}) {invAt "_p"})))",
      s!"(assert (forall ({sorted all}) (=> (and {t.dom} {invAt ""} {s.bad}) false)))",
      "(check-sat)", "(get-model)", ""] }

/-- The same question for cvc5, as a `synth-inv` problem. The havoc variables of a path are existential in `trans`. -/
def Safety.synthInv (s : Safety) : Query :=
  let t := s.ts
  let sv := t.state ++ t.frame
  let frameEq := t.frame.map fun v => s!"(= {v.name}_p {v.name})"
  let domP := t.state.map (·.dom "_p")
  let domV := sv.map (·.dom)
  let domH := t.havoc.map (·.dom)
  let ex := if t.havoc.isEmpty then s!"(and {t.cont true})"
    else s!"(exists ({sorted t.havoc}) (and {" ".intercalate domH} {t.cont true}))"
  let initEx := if t.havoc.isEmpty then t.init else s!"(exists ({sorted t.havoc}) {t.init})"
  { which := .cvc5, funs := [("inv", "Bool")], arity := sv.length,
    text := "\n".intercalate [
      "(set-logic LIA)",
      s!"(synth-inv inv ({sorted sv}))",
      s!"(define-fun pre_f ({sorted sv}) Bool (and {" ".intercalate domV} {initEx}))",
      s!"(define-fun trans_f ({sorted sv} {sorted (primedVars t.state ++ primedVars t.frame)}) Bool (and {" ".intercalate (domV ++ domP ++ frameEq)} {ex}))",
      s!"(define-fun post_f ({sorted sv}) Bool (not (and {" ".intercalate domV} {s.bad})))",
      "(inv-constraint inv pre_f trans_f post_f)",
      "(check-synth)", ""] }

/-- `TS.rankQuery` with the constants `consts` in the grammar of the ranking function, after `0` and `1`, in increasing
order (`0`, `1` and repeats dropped). With no constant it is `TS.rankQuery`. -/
def rankQuery (t : LTS) (consts : List Nat := []) : Query :=
  let d := t.dom
  let c := t.cont true
  let extra := (consts.filter (· > 1)).eraseDups.toArray.qsort (· < ·) |>.toList
  let lits := " ".intercalate (["0", "1"] ++ extra.map toString)
  let vars := " ".intercalate ((t.state ++ t.frame).map (·.name))
  { which := .cvc5, funs := [("inv", "Bool"), ("rho", "Int")], arity := (t.state ++ t.frame).length,
    text := "\n".intercalate [
      "(set-logic LIA)",
      s!"(synth-fun inv ({t.args}) Bool)",
      s!"(synth-fun rho ({t.args}) Int ((I Int)) ((I Int ({vars} {lits} (+ I I) (- I I)))))",
      t.decls,
      s!"(constraint (=> (and {d} {t.init}) {t.call "inv"}))",
      s!"(constraint (=> (and {d} {t.call "inv"} {c}) {t.call "inv" "_p"}))",
      s!"(constraint (=> (and {d} {t.call "inv"} {c}) (and (> {t.call "rho"} {t.call "rho" "_p"}) (>= {t.call "rho" "_p"} 0))))",
      "(check-synth)", ""] }

/-! ## The ghost query of the arrays (task S6)

`ghostQuery s gs entry` is the safety of the ghost properties `gs` (`Sys.ghosts`) over the system `s` itself, with its arrays
as SMT arrays. The state of `inv` is the state of `s` and the tracked positions `q`, `q1` of each `perm` ghost; its frame is
the parameters, the index `g` of each `index` ghost, and the entry array `v0` and the positions `p`, `p1` of each `perm` ghost.
The entry clause has the entry condition of the site. There is one clause for each path. `sat` gives an invariant over all of
them; `unsat` says that a ghost property fails. The fuel is not in this query: with the fuel, Spacer gave a case for each
value of the index of `fill` (16 cases), and `grind` did not close the step goal in the limit. The fuel stays with `fuelTS`. -/

/-- The ghost variables of one ghost property: `[g]` for `index`, `v0s ++ [p, q, p1, q1]` for `perm vs` (an entry array
`v0` for each array of `vs`). -/
structure GhostVars where
  ghost : Ghost
  vars : List String
  deriving BEq, Repr, Inhabited

/-- The variables of a `perm vs` ghost: each array of `vs` with its entry array, and `p`, `q`, `p1`, `q1`. -/
structure PermVars where
  arrays : List (String × String)
  p : String
  q : String
  p1 : String
  q1 : String

def GhostVars.perm? (g : GhostVars) : Option PermVars :=
  match g.ghost with
  | .perm vs =>
    match g.vars.drop vs.length with
    | [p, q, p1, q1] => some { arrays := vs.zip (g.vars.take vs.length), p, q, p1, q1 }
    | _ => none
  | .index .. => none

structure GhostQuery where
  sys : Sys
  ghosts : List GhostVars
  /-- The parameters of `inv`, in order. -/
  args : List String
  query : Query
  deriving Repr, Inhabited

private def srtOf : Kind → String
  | .scalar _ => "Int"
  | .array .. => "(Array Int Int)"

private def domOf (n : String) : Kind → Option String
  | .scalar .nat => some s!"(>= {n} 0)"
  | .scalar (.fin k) => some s!"(and (>= {n} 0) (< {n} {k}))"
  | .scalar .bool => some s!"(and (>= {n} 0) (<= {n} 1))"
  | .scalar (.bv w) => some s!"(and (>= {n} 0) (< {n} {2 ^ w}))"
  | _ => none

private def andAll (cs : List String) : String := if cs.isEmpty then "true" else s!"(and {" ".intercalate cs})"

/-- The ghost query of `s` with the ghosts `gs` and the entry condition `entry` (an SMT term over the variables of `s`). -/
def ghostQuery (s : Sys) (gs : List Ghost) (entry : Tm) : GhostQuery := Id.run do
  let mut taken := s.names
  let fresh (taken : List String) (b : String) : String × List String :=
    let n := freshName taken b
    (n, n :: taken)
  let mut gvs : List GhostVars := []
  for g in gs do
    match g with
    | .index .. =>
      let (x, t) := fresh taken "g"
      taken := t
      gvs := gvs ++ [{ ghost := g, vars := [x] }]
    | .perm arrs =>
      let mut vs : List String := []
      for b in arrs.map (fun _ => "v0") ++ ["p", "q", "p1", "q1"] do
        let (x, t) := fresh taken b
        taken := t
        vs := vs ++ [x]
      gvs := gvs ++ [{ ghost := g, vars := vs }]
  let kindOf (n : String) : Option Kind := ((s.state ++ s.params).find? (·.name == n)).map (·.kind)
  let sizeOf (v : String) : Tm := match kindOf v with
    | some (.array _ n) => n
    | _ => .num 0
  -- the ghost variables, by role
  let perms := gvs.filterMap (·.perm?)
  let gState := perms.flatMap fun pv => [pv.q, pv.q1]
  let gFrame := gvs.flatMap fun g => match g.perm?, g.ghost, g.vars with
    | some pv, _, _ => pv.arrays.map (·.2) ++ [pv.p, pv.p1]
    | none, .index .., [x] => [x]
    | none, _, _ => []
  let stateNames := s.state.map (·.name) ++ gState
  let frameNames := s.params.map (·.name) ++ gFrame
  let args := stateNames ++ frameNames
  let isArr (n : String) : Bool := (kindOf n matches some (.array ..)) ||
    perms.any fun pv => pv.arrays.any (·.2 == n)
  let sorted (ns : List String) : String := " ".intercalate (ns.map fun n => s!"({n} {if isArr n then "(Array Int Int)" else "Int"})")
  let hv := s.havoc.map (·.var)
  let all := sorted args ++ (if hv.isEmpty then "" else " " ++ " ".intercalate (hv.map fun v => s!"({v.name} {srtOf v.kind})"))
  let dom := andAll ((s.state ++ s.params ++ hv).filterMap (fun v => domOf v.name v.kind) ++
    gvs.flatMap fun g => match g.ghost, g.vars with
      | .index .., [x] => [s!"(>= {x} 0)"]
      | _, _ => [])
  let inv (ns : List String) : String := s!"(inv {" ".intercalate ns})"
  -- the size and the moves of a `perm` ghost are those of its first array
  let first (pv : PermVars) : String := (pv.arrays.head?.map (·.1)).getD ""
  let init := andAll ([entry.text] ++
    perms.flatMap fun pv =>
      let n := (sizeOf (first pv)).text
      pv.arrays.map (fun (v, v0) => s!"(= {v0} {v})") ++
        [s!"(<= 0 {pv.p})", s!"(< {pv.p} {n})", s!"(<= 0 {pv.p1})", s!"(< {pv.p1} {n})", s!"(= {pv.q} {pv.p})",
         s!"(= {pv.q1} {pv.p1})"])
  let nextOf (p : Path) (n : String) : String :=
    match perms.find? (fun pv => pv.q == n || pv.q1 == n) with
    | some pv =>
      let v := first pv
      let ss := ((p.next.lookup v).bind (storesOn v)).getD []
      (trackTo v ss (.var n)).text
    | none => ((p.next.lookup n).map Tm.text).getD n
  let stepClause (p : Path) : String :=
    s!"(assert (forall ({all}) (=> {andAll ([dom, inv args] ++ p.pc.map Tm.text)} {inv (stateNames.map (nextOf p) ++ frameNames)})))"
  let viol := gvs.map fun g => match g.perm?, g.ghost, g.vars with
    | some pv, _, _ =>
      let moved := pv.arrays.map fun (v, v0) => s!"(not (= (select {v} {pv.q}) (select {v0} {pv.p})))"
      s!"(or {" ".intercalate moved} (< {pv.q} 0) (>= {pv.q} {(sizeOf (first pv)).text}) (and (not (= {pv.p} {pv.p1})) (= {pv.q} {pv.q1})))"
    | none, .index v i x, [gx] =>
      s!"(and (<= 0 {gx}) (< {gx} {i}) (not (= (select {v} {gx}) {(x.subst i (.var gx)).text})))"
    | none, _, _ => "false"
  let bad := s!"(or {" ".intercalate viol})"
  let text := "\n".intercalate ([
      "(set-logic HORN)",
      s!"(declare-fun inv ({" ".intercalate (args.map fun n => if isArr n then "(Array Int Int)" else "Int")}) Bool)",
      s!"(assert (forall ({all}) (=> {andAll [dom, init]} {inv args})))"] ++
    s.paths.map stepClause ++
    [ s!"(assert (forall ({all}) (=> {andAll [dom, inv args, bad]} false)))",
      "(check-sat)", "(get-model)", ""])
  pure { sys := s, ghosts := gvs, args,
         query := { which := .z3, text, funs := [("inv", "Bool")], arity := args.length } }

/-! ## The answers -/

/-- A `define-fun` of an answer: `(define-fun name ((p sort) ...) sort body)`. The names of the parameters are those of the
solver (`x!0` for z3); the body is the S-expression (`let`, `and`, ... as the solver prints them), for the parser of the way
back. -/
structure Def where
  name : String
  params : List (String × Sexp)
  sort : Sexp
  body : Sexp
  deriving BEq, Repr, Inhabited

private def defOf? : Sexp → Option Def
  | .list [.atom "define-fun", .atom name, .list ps, sort, body] => do
    let params ← ps.mapM fun | .list [.atom p, s] => some (p, s) | _ => none
    some { name, params, sort, body }
  | _ => none

/-- The `define-fun` of a model of z3 (`sat` and then `( (define-fun ...) ... )`) or of a solution of cvc5 (the same list). The
answers of the other forms (`sat`, `unsat`, `infeasible`, `(error ...)`) have no definition. -/
def readModel (out : String) : Except String (List Def) := do
  let xs ← Sexp.parseAll out
  let defs := xs.flatMap fun
    | .list ys => if ys.all (defOf? · |>.isSome) then ys.filterMap defOf? else (defOf? (.list ys)).toList
    | _ => []
  pure defs

/-- What a run says. -/
inductive Result where
  /-- Spacer `sat` (the fuel is safe), or a solution of `synth-inv` or of the ranking query: the functions of the query. -/
  | solved (defs : List Def)
  /-- Spacer `unsat` (a path to a bad state: the fuel is not enough), or cvc5 `infeasible` (no function in the grammar). -/
  | infeasible
  /-- No answer: `timeout`, or what the solver says. -/
  | unknown (why : String)
  /-- The solver did not run, or the answer is not understood. -/
  | failed (why : String)
  deriving BEq, Repr, Inhabited

/-- The result of the text that the solver printed. An empty answer is a time limit: cvc5 prints nothing at its limit. -/
def Query.result (q : Query) (out : String) : Result :=
  match Sexp.parseAll out with
  | .error e => .failed s!"cannot read the answer: {e}"
  | .ok [] => .unknown "timeout"
  | .ok (first :: _) =>
    match first with
    | .atom "unsat" | .atom "infeasible" => .infeasible
    | .atom "unknown" | .atom "timeout" => .unknown (if (out.splitOn "timeout").length > 1 then "timeout" else "incomplete")
    | .atom "sat" | .list _ =>
      match readModel out with
      | .error e => .failed s!"cannot read the answer: {e}"
      | .ok defs =>
        let found : Option (List (String × String × Def)) :=
          q.funs.mapM fun (n, srt) => (defs.find? (·.name == n)).map fun d => (n, srt, d)
        match found with
        | none => .failed s!"the answer does not define {", ".intercalate (q.funs.map (·.1))}"
        | some fs =>
          match fs.find? fun ((_, srt, d) : String × String × Def) => d.params.length != q.arity || d.sort != .atom srt with
          | some (n, srt, d) =>
            .failed s!"{n} has {d.params.length} parameters (the query has {q.arity}) or a sort other than {srt}"
          | none => .solved (fs.map (·.2.2))
    | _ => .failed s!"unexpected answer: {out.take 200}"

/-! ## The cache -/

/-- The key of an answer: the hash of the solver, its version and the text of the query. -/
def cacheKey (w : Which) (version text : String) : String := toString (hash s!"{w.name}\n{version}\n{text}")

private def cacheFile (dir : String) (w : Which) (key : String) : String := s!"{dir}/{w.name}-{key}.json"

/-- The answer of the cache, when the file is there and repeats the solver, the version and the key. -/
def cacheLoad (dir : String) (w : Which) (version text : String) : IO (Option String) := do
  let key := cacheKey w version text
  let path := cacheFile dir w key
  if !(← System.FilePath.pathExists path) then return none
  let some j := (Json.parse (← IO.FS.readFile path)).toOption | return none
  let field (k : String) : Option String := (j.getObjValAs? String k).toOption
  let ok := field "solver" == some w.name && field "version" == some version && field "hash" == some key
  if !ok then return none
  return (j.getObjValAs? String "answer").toOption

/-- Writes the answer, over a file that is there. -/
def cacheStore (dir : String) (w : Which) (version text answer : String) : IO Unit := do
  let key := cacheKey w version text
  IO.FS.createDirAll dir
  let j := Json.mkObj [("solver", w.name), ("version", version), ("hash", key), ("answer", answer)]
  IO.FS.writeFile (cacheFile dir w key) (j.pretty 120 ++ "\n")

/-! ## The runners -/

structure Config where
  /-- The commands of the solvers (a path is fine). -/
  z3 : String := "z3"
  cvc5 : String := "cvc5"
  /-- The directory of the cache; none: no cache. -/
  cache : Option String := none
  /-- The time limit of a query, and of the queries of a site, in milliseconds. -/
  queryMs : Nat := 20000
  siteMs : Nat := 60000
  deriving Repr, Inhabited

def Config.cmd (c : Config) : Which → String
  | .z3 => c.z3
  | .cvc5 => c.cvc5

/-- The record of one run: for the ledger. -/
structure Run where
  result : Result
  solver : String
  /-- The first line of `--version` of the solver that ran, or `pinnedVersion` when the cache answered with no solver. -/
  version : String
  /-- The key of the query (see `cacheKey`). -/
  hash : String
  /-- The time of the solver process: 0 when the cache answered. -/
  ms : Nat
  cached : Bool
  deriving Repr, Inhabited

/-- The first line of `cmd --version`; none when the command does not run. -/
def probeVersion (cmd : String) : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd, args := #["--version"] }
    if o.exitCode != 0 then return none
    return (o.stdout.splitOn "\n").head?.map (·.trimAscii.toString)
  catch _ => return none

/-- z3 on a text, under its own limit (`-T`, in seconds) and a hard limit of `timeout`. The stdout and the time. -/
def runZ3 (cmd text : String) (limitMs : Nat) : IO (String × Nat) := do
  let secs := (limitMs + 999) / 1000
  let (h, path) ← IO.FS.createTempFile
  h.putStr text
  h.flush
  let t0 ← IO.monoMsNow
  let out ← try
      let o ← IO.Process.output { cmd := "timeout", args := #["-k", "1", toString (secs + 2), cmd, "-smt2", s!"-T:{secs}", path.toString] }
      pure o.stdout
    catch _ => pure ""
  let ms := (← IO.monoMsNow) - t0
  try IO.FS.removeFile path catch _ => pure ()
  return (out, ms)

/-- Runs a query: the cache first, then the solver. -/
def runQuery (cfg : Config) (q : Query) (limitMs : Nat := cfg.queryMs) : IO Run := do
  let cmd := cfg.cmd q.which
  let live ← probeVersion cmd
  let version := live.getD q.which.pinnedVersion
  let key := cacheKey q.which version q.text
  let mk (result : Result) (ms : Nat) (cached : Bool) : Run :=
    { result, solver := q.which.name, version, hash := key, ms, cached }
  if let some dir := cfg.cache then
    if let some out ← cacheLoad dir q.which version q.text then
      return mk (q.result out) 0 true
  if live.isNone then
    return mk (.failed s!"cannot run `{cmd}` (is it on the PATH?), and the cache has no answer") 0 false
  let (out, ms) ← match q.which with
    | .z3 => runZ3 cmd q.text limitMs
    | .cvc5 => do
      let t0 ← IO.monoMsNow
      let out ← Lift.Inv.Gen.runCvc5 q.text limitMs none cmd
      pure (out, (← IO.monoMsNow) - t0)
  let result := q.result out
  if let some dir := cfg.cache then
    match result with
    | .solved _ | .infeasible => cacheStore dir q.which version q.text out
    | _ => pure ()
  return mk result ms false

/-- The queries of one site, in order, within `cfg.siteMs`: each has at most `cfg.queryMs` and what is left of the site. A
query that finds nothing left is not run (`unknown "site budget"`). An answer of the cache costs no time. -/
def runSite (cfg : Config) (qs : List Query) : IO (List Run) := do
  let mut left := cfg.siteMs
  let mut out : Array Run := #[]
  for q in qs do
    if left == 0 then
      let skipped : Run :=
        { result := .unknown "site budget", solver := q.which.name, version := "", hash := "", ms := 0, cached := false }
      out := out.push skipped
    else
      let r ← runQuery cfg q (min cfg.queryMs left)
      left := left - min left r.ms
      out := out.push r
  return out.toList

end Skel.Discover.Smt
