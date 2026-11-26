import Skel.Discover.Smt.Ts
import Skel.Test.DiscoverSite

/-! The tests of `Skel/Discover/Smt/Ts.lean` (suite `discoversmt`): `lake exe skel-test --only discoversmt`. Each check is
a value that must hold; a check that does not hold prints one `FAIL` line, and the suite gives the number of failed
checks. `sysOf?` runs on each site when this module is built (`sys%`). The agreement checks evaluate the step on a random
state and the paths of the system on the same state (`evalTm`, and `Lift.Inv.Gen.Loop.eval` for the text of `toTS`): the
step is `cont s'` iff exactly one path holds and gives `s'`, and the step exits iff no path holds and an exit holds. The
fixed checks draw 300 states (seeds `17 .. 316`, as the spike); the property draws `max cases 200` states from `seed`. -/

namespace DiscoverSmtTests

open Lean Skel.Discover Skel.Discover.Smt Lift.Smt DiscoverSiteTests

/-! ## The sites -/

/-- `twoPhase` of the spike (`scratch/inv-s0/Spike.lean`). -/
def twoPhase : Nat → Nat × Bool → Option Nat
  | 0, _ => none
  | n + 1, (k, b) => if k = 0 then some 0 else if b then twoPhase n (k - 1, false) else twoPhase n (k, true)

/-- A `String` state: outside the fragment. -/
def strLoop : Nat → String → Nat
  | 0, _ => 0
  | n + 1, s => if s.length = 0 then 0 else strLoop n (s.drop 1).toString

/-- A product of two state variables: outside the fragment. -/
def prodLoop : Nat → Nat × Nat → Nat
  | 0, _ => 0
  | n + 1, (a, b) => if a = 0 then b else prodLoop n (a - 1, a * b)

/-- The state of `ghostLoop`: a field with the name of the step counter of the fuel query. -/
structure GSt where
  steps : Nat
  fuel0 : Fin 4
  deriving Repr

/-- A loop whose state names clash with the ghost names. -/
def ghostLoop : Nat → GSt → Nat
  | 0, _ => 0
  | n + 1, s => if s.steps = 0 then s.fuel0.val else ghostLoop n { steps := s.steps - 1, fuel0 := s.fuel0 + 3 }

/-- A state of a small inductive type and a `Nat`, with an `Option` in the next state. -/
def statusLoop : Nat → Status × Nat → Option Nat
  | 0, _ => none
  | n + 1, (s, k) =>
    match s with
    | .ok => if k = 0 then some 0 else statusLoop n (if k % 2 = 0 then .stop else .spent, k - 1)
    | .stop => statusLoop n (.ok, k / 2)
    | .spent => if k > 3 then none else statusLoop n (.ok, 2 * k)

/-- An `Option` state. -/
def optLoop : Nat → Option Nat → Bool
  | 0, _ => false
  | n + 1, s =>
    match s with
    | none => true
    | some k => if k = 0 then false else optLoop n (if k % 3 = 0 then none else some (k - 1))

/-- An `Array` state with `push` and `size`. -/
def arrLoop : Nat → Array Nat × Nat → Nat
  | 0, _ => 0
  | n + 1, (a, k) => if k = 0 then a.size else if h : 0 < a.size then arrLoop n (a.set 0 (a[0] + k) h, k - 1)
    else arrLoop n (a.push k, k - 1)

/-- A call of a recursive function in the step: outside the fragment. -/
def sumAll : Nat → Nat × List Nat → Nat
  | 0, _ => 0
  | n + 1, (acc, xs) => if acc > 100 then acc else sumAll n (acc + xs.sum, xs.tail)

open Elab Term Meta in
/-- `sys% f`: `sysOf? f`, run when the term is elaborated. -/
elab "sys% " f:ident : term => do
  match ← sysOf? f.getId with
  | .ok s => mkAppOptM ``Except.ok #[some (toTypeExpr SolverError), some (toTypeExpr Sys), some (toExpr s)]
  | .error e => mkAppOptM ``Except.error #[some (toTypeExpr SolverError), some (toTypeExpr Sys), some (toExpr e)]

def countDownSys : Except SolverError Sys := sys% DiscoverSiteTests.countDown
def vecLoopSys : Except SolverError Sys := sys% DiscoverSiteTests.vecLoop
def branchLoopSys : Except SolverError Sys := sys% DiscoverSiteTests.branchLoop
def sumTwoSys : Except SolverError Sys := sys% DiscoverSiteTests.sumTwo
def twoPhaseSys : Except SolverError Sys := sys% DiscoverSmtTests.twoPhase
def ghostLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.ghostLoop
def strLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.strLoop
def prodLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.prodLoop
def statusLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.statusLoop
def optLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.optLoop
def arrLoopSys : Except SolverError Sys := sys% DiscoverSmtTests.arrLoop
def sumAllSys : Except SolverError Sys := sys% DiscoverSmtTests.sumAll

#def_step ghostStep DiscoverSmtTests.ghostLoop
#def_step statusStep DiscoverSmtTests.statusLoop
#def_step optStep DiscoverSmtTests.optLoop
#def_step arrStep DiscoverSmtTests.arrLoop

/-- The D2 sites of `Skel/Test/DiscoverSite.lean` that have no site, with the results of `sysOf?`. -/
def noSiteSys : List (String × Except SolverError Sys) :=
  [ ("twoCalls", sys% DiscoverSiteTests.twoCalls), ("notTail", sys% DiscoverSiteTests.notTail),
    ("sameState", sys% DiscoverSiteTests.sameState), ("sumJoint", sys% DiscoverSiteTests.sumJoint),
    ("notLoop", sys% DiscoverSiteTests.notLoop), ("halves", sys% DiscoverSiteTests.halves),
    ("noSuchFunction", sys% DiscoverSiteTests.noSuchFunction) ]

/-! ## The agreement of a system with the step -/

/-- Two values are equal; two arrays are equal at the positions `0 .. 63`. -/
def same : V → V → Bool
  | .arr es d, .arr es' d' => (List.range 64).all fun i => (es.lookup (i : Int)).getD d == (es'.lookup (i : Int)).getD d'
  | a, b => a == b

/-- The outcome of the step on one state: the next values of the state variables, or an exit. -/
abbrev Outcome := Option (List (String × V))

/-- `s` agrees with the step on the state of `env`, whose outcome is `out`. -/
def agrees (s : Sys) (env : List (String × V)) (out : Outcome) : Bool :=
  let look (n : String) : Option V := env.lookup n
  let holds (pc : List Tm) : Bool := pc.all fun c => evalTm look c == some (.bool true)
  let live := s.paths.filter (holds ·.pc)
  match out with
  | none => live.isEmpty && s.exits.any holds
  | some next => match live with
    | [p] => !(s.exits.any holds) && next.all fun (n, v) =>
        match evalTm look ((p.next.lookup n).getD (.var n)) with
        | some w => same v w
        | none => false
    | _ => false

/-- The value of a `Nat`. -/
def nat (n : Nat) : V := .int n

/-- The array of a vector. -/
def arrOf (v : Vector Nat 8) : V := .arr ((List.range 8).map fun (j : Nat) => ((j : Int), ((v.toArray.getD j 0 : Nat) : Int))) 0

/-- The names of the havoc variables of `s`. -/
def havocs (s : Sys) : List String := s.havoc.map (·.var.name)

/-- The environment of the head of a list: each havoc variable has the head. -/
def withHead (s : Sys) (xs : List Nat) (env : List (String × V)) : List (String × V) :=
  env ++ (havocs s).map (·, nat (xs.headD 0))

def countDownEnv (s : Cnt) : List (String × V) := [("k", nat s.k), ("acc", nat s.acc)]
def countDownOut (s : Cnt) : Outcome := match countDownStep s with
  | .cont s' => some (countDownEnv s') | _ => none

def vecEnv (lim : Nat) (s : VSt) : List (String × V) := [("lim", nat lim), ("v", arrOf s.v), ("i", nat s.i)]
def vecOut (lim : Nat) (s : VSt) : Outcome := match vecLoopStep lim s with
  | .cont s' => some ((vecEnv lim s').drop 1) | _ => none

def branchEnv (st : List Nat × Fin 5) : List (String × V) := [("fst_len", nat st.1.length), ("snd", nat st.2.val)]
def branchOut (st : List Nat × Fin 5) : Outcome := match branchLoopStep st with
  | .cont st' => some (branchEnv st') | _ => none

def sumEnv (st : Nat × List Nat) : List (String × V) := [("fst", nat st.1), ("snd_len", nat st.2.length)]
def sumOut (st : Nat × List Nat) : Outcome := match sumTwoStep st with
  | .cont st' => some (sumEnv st') | _ => none

/-- The step of `twoPhase`, as `siteOf?` gives it (the definition of the spike). -/
def twoPhaseStep (st : Nat × Bool) : Step (Nat × Bool) (Option Nat) :=
  if st.1 = 0 then .exit (some 0) else if st.2 = true then .cont (st.1 - 1, false) else .cont (st.1, true)

def twoEnv (st : Nat × Bool) : List (String × V) := [("fst", nat st.1), ("snd", nat (if st.2 then 1 else 0))]
def twoOut (st : Nat × Bool) : Outcome := match twoPhaseStep st with
  | .cont st' => some (twoEnv st') | _ => none

def statusTag : Status → Nat | .ok => 0 | .stop => 1 | .spent => 2

def statusEnv (st : Status × Nat) : List (String × V) := [("fst_tag", nat (statusTag st.1)), ("snd", nat st.2)]
def statusOut (st : Status × Nat) : Outcome := match statusStep st with
  | .cont st' => some (statusEnv st') | _ => none

/-- The payload of `none` is not part of the state: only the tag is compared. -/
def optEnv : Option Nat → List (String × V)
  | none => [("tag", nat 0)]
  | some k => [("tag", nat 1), ("some_val", nat k)]
def optOut (s : Option Nat) : Outcome := match optStep s with
  | .cont s' => some (optEnv s') | _ => none

def arrOfArray (a : Array Nat) : V := .arr ((List.range a.size).map fun (j : Nat) => ((j : Int), ((a.getD j 0 : Nat) : Int))) 0

def arrEnv (st : Array Nat × Nat) : List (String × V) :=
  [("fst", arrOfArray st.1), ("fst_size", nat st.1.size), ("snd", nat st.2)]
def arrOut (st : Array Nat × Nat) : Outcome := match arrStep st with
  | .cont st' => some (arrEnv st') | _ => none

def drawStatus (g : StdGen) : (Status × Nat) × StdGen :=
  let (t, g) := randNat g 0 2; let (k, g) := randNat g 0 9
  ((match t with | 0 => .ok | 1 => .stop | _ => .spent, k), g)

def drawOpt (g : StdGen) : Option Nat × StdGen :=
  let (t, g) := randNat g 0 1; let (k, g) := randNat g 0 9; (if t == 0 then none else some k, g)

def drawArr (g : StdGen) : (Array Nat × Nat) × StdGen :=
  let (len, g) := randNat g 0 4
  let (xs, g) := (List.range len).foldl (fun (acc, g) _ => let (x, g) := randNat g 0 9; (acc ++ [x], g)) ([], g)
  let (k, g) := randNat g 0 5
  ((xs.toArray, k), g)

def ghostEnv (s : GSt) : List (String × V) := [("steps", nat s.steps), ("fuel0", nat s.fuel0.val)]
def ghostOut (s : GSt) : Outcome := match ghostStep s with
  | .cont s' => some (ghostEnv s') | _ => none

def drawTwo (g : StdGen) : (Nat × Bool) × StdGen :=
  let (k, g) := randNat g 0 20; let (b, g) := randNat g 0 1; ((k, b == 1), g)

def drawGhost (g : StdGen) : GSt × StdGen :=
  let (k, g) := randNat g 0 20; let (f, g) := randNat g 0 3; (⟨k, Fin.ofNat 4 f⟩, g)

/-- `s` agrees with the step on the state that `g` draws, for each site of the fragment by name. -/
def agreeOn (site : String) (s : Sys) (g : StdGen) : Bool :=
  match site with
  | "countDown" => let ((_, x), _) := drawCnt g; agrees s (countDownEnv x) (countDownOut x)
  | "vecLoop" => let ((_, lim, x), _) := drawVSt g; agrees s (vecEnv lim x) (vecOut lim x)
  | "branchLoop" => let ((_, x), _) := drawPair g; agrees s (withHead s x.1 (branchEnv x)) (branchOut x)
  | "sumTwo" => let ((_, (xs, c)), _) := drawPair g; agrees s (withHead s xs (sumEnv (c.val, xs))) (sumOut (c.val, xs))
  | "twoPhase" => let (x, _) := drawTwo g; agrees s (twoEnv x) (twoOut x)
  | "ghostLoop" => let (x, _) := drawGhost g; agrees s (ghostEnv x) (ghostOut x)
  | "statusLoop" => let (x, _) := drawStatus g; agrees s (statusEnv x) (statusOut x)
  | "optLoop" =>
    -- the payload variable of `none` has some value: a random one
    let (x, g) := drawOpt g; let (junk, _) := randNat g 0 9
    agrees s (optEnv x ++ [("some_val", nat junk)]) (optOut x)
  | "arrLoop" => let (x, _) := drawArr g; agrees s (arrEnv x) (arrOut x)
  | _ => false

/-- The sites of the fragment and their systems. -/
def fragmentSites : List (String × Except SolverError Sys) :=
  [ ("countDown", countDownSys), ("vecLoop", vecLoopSys), ("branchLoop", branchLoopSys), ("sumTwo", sumTwoSys),
    ("twoPhase", twoPhaseSys), ("ghostLoop", ghostLoopSys), ("statusLoop", statusLoopSys), ("optLoop", optLoopSys),
    ("arrLoop", arrLoopSys) ]

/-- `countDown` with a wrong next value: `acc + 1`, not `acc + 2`. -/
def countDownWrongSys : Except SolverError Sys :=
  countDownSys.map fun s => { s with paths := s.paths.map fun p =>
    { p with next := p.next.map fun (n, t) => if n == "acc" then (n, .app "+" [.var "acc", .num 1]) else (n, t) } }

/-- The number of the states `seed .. seed + n - 1` on which `site` does not agree (all `n` when it has no system). -/
def disagree (site : String) (r : Except SolverError Sys) (seed n : Nat) : Nat :=
  match r with
  | .ok s => ((List.range n).filter fun i => !agreeOn site s (mkStdGen (seed + i))).length
  | .error _ => n

/-! ## The agreement of the text of `toTS` with the step (the evaluator of `Lift.Inv.Gen.Loop`) -/

/-- The truth of the SMT text `c` in `env`. -/
def textHolds (env : List (String × Int)) (c : String) : Bool :=
  match Lift.Inv.Gen.SExp.parseAll c with
  | .ok [e] => match Lift.Inv.Gen.Loop.eval env e with
    | some (.bool b) => b
    | _ => false
  | _ => false

/-- The integer of the SMT text `t` in `env`. -/
def textInt (env : List (String × Int)) (t : String) : Option Int :=
  match Lift.Inv.Gen.SExp.parseAll t with
  | .ok [e] => match Lift.Inv.Gen.Loop.eval env e with
    | some (.int n) => some n
    | _ => none
  | _ => none

/-- The `TS` agrees with the step: the integer variables of `env`, each havoc of the `TS` at `hv`. -/
def tsAgrees (t : Lift.Inv.Gen.Loop.TS) (env : List (String × Int)) (hv : Int) (out : Option (List (String × Int))) :
    Bool :=
  let env := env ++ t.havoc.map (·.name, hv)
  let live := t.paths.filter fun p => p.pc.all (textHolds env)
  match out, live with
  | none, [] => true
  | some next, [p] => next.all fun (n, v) => textInt env ((p.next.lookup n).getD n) == some v
  | _, _ => false

/-- The integer values of an environment with no array. -/
def ints (env : List (String × V)) : List (String × Int) :=
  env.filterMap fun | (n, .int v) => some (n, v) | _ => none

def tsAgreeOn (site : String) (t : Lift.Inv.Gen.Loop.TS) (g : StdGen) : Bool :=
  match site with
  | "countDown" => let ((_, x), _) := drawCnt g; tsAgrees t (ints (countDownEnv x)) 0 ((countDownOut x).map ints)
  | "vecLoop" =>
    let ((_, lim, x), _) := drawVSt g
    let hv : Int := if h : x.i < 8 then x.v[x.i] else 0
    tsAgrees t (ints (vecEnv lim x)) hv ((vecOut lim x).map ints)
  | "branchLoop" => let ((_, x), _) := drawPair g; tsAgrees t (ints (branchEnv x)) (x.1.headD 0) ((branchOut x).map ints)
  | "twoPhase" => let (x, _) := drawTwo g; tsAgrees t (ints (twoEnv x)) 0 ((twoOut x).map ints)
  | _ => false

def tsDisagree (site : String) (r : Except SolverError Sys) (seed n : Nat) : Nat :=
  match r.bind Sys.toTS with
  | .ok t => ((List.range n).filter fun i => !tsAgreeOn site t (mkStdGen (seed + i))).length
  | .error _ => n

/-! ## The checks -/

/-- The text of an `outOfFragment` error contains `p`. -/
def outOfFragmentWith (r : Except SolverError Sys) (p : String) : Bool :=
  match r with
  | .error (.outOfFragment w) => has w p
  | _ => false

def isOk : Except SolverError Sys → Bool | .ok _ => true | .error _ => false

/-- A random list of names, some of the form `b_k`. -/
def drawNames (g : StdGen) : List String × StdGen :=
  let (len, g) := randNat g 0 6
  (List.range len).foldl (fun (acc, g) _ =>
    let (k, g) := randNat g 0 4
    (acc ++ [if k == 0 then "b" else s!"b_{k}"], g)) ([], g)

def fixedChecks : List (String × Bool) :=
  let spike := [("countDown", countDownSys), ("vecLoop", vecLoopSys), ("branchLoop", branchLoopSys),
    ("twoPhase", twoPhaseSys)]
  spike.map (fun (n, r) => (s!"{n}: the system agrees with the step on 300 states", disagree n r 17 300 == 0)) ++
  spike.map (fun (n, r) => (s!"{n}: the text of toTS agrees with the step on 300 states", tsDisagree n r 17 300 == 0)) ++
  [ ("a String state: outOfFragment that names String", outOfFragmentWith strLoopSys "String"),
    ("a product of two variables: outOfFragment that names the product",
      outOfFragmentWith prodLoopSys "product of two variables"),
    ("branchLoop: the head of the list is a havoc, marked",
      match branchLoopSys with
      | .ok s => s.havoc.length == 1 && s.havoc.all (has ·.why "head of a list")
      | .error _ => false),
    ("sumTwo: the head of the list is a havoc, marked",
      match sumTwoSys with
      | .ok s => s.havoc.length == 1 && s.havoc.all (has ·.why "head of a list")
      | .error _ => false),
    ("a call of a recursive function: outOfFragment that names it", outOfFragmentWith sumAllSys "recursive function"),
    ("a wrong system (acc + 1) fails the agreement check on some state", disagree "countDown" countDownWrongSys 17 300 > 0),
    ("statusLoop: the Status is a tag in [0, 3)",
      match statusLoopSys with
      | .ok s => s.state.contains { name := "fst_tag", kind := .scalar (.fin 3) }
      | .error _ => false),
    ("statusLoop: the TS bounds the tag in each path and the entry",
      match statusLoopSys.bind Sys.toTS with
      | .ok t => t.paths.all (·.pc.contains "(< fst_tag 3)") && t.entries == [(["(< fst_tag 3)"], [])]
      | .error _ => false),
    ("countDown: no havoc", match countDownSys with | .ok s => s.havoc.isEmpty | .error _ => false),
    ("vecLoop: the vector is an array of size 8, lim a parameter",
      match vecLoopSys with
      | .ok s => s.state.any (· == { name := "v", kind := .array .nat (.num 8) }) &&
          s.params == [{ name := "lim", kind := .scalar .nat }]
      | .error _ => false),
    ("vecLoop: the TS has the element as a havoc and no array",
      match vecLoopSys.bind Sys.toTS with
      | .ok t => t.havoc.length == 1 && t.state.map (·.name) == ["i"] && t.frame.map (·.name) == ["lim"]
      | .error _ => false),
    ("ghostLoop: the ghost names steps and fuel0 are fresh",
      match ghostLoopSys with
      | .ok s => s.fresh "steps" != "steps" && !s.names.contains (s.fresh "steps") &&
          !s.names.contains (s.fresh "fuel0") && s.fresh "ghost" == "ghost"
      | .error _ => false),
    ("countDown, vecLoop, branchLoop, sumTwo of D2: a system",
      [countDownSys, vecLoopSys, branchLoopSys, sumTwoSys].all isOk) ] ++
  noSiteSys.map fun (n, r) => (s!"{n} of D2: the named error of siteExprOf?",
    match r with | .error (.site _) => true | _ => false)

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  fragmentSites.map (fun (n, r) =>
    (s!"{n}: the system agrees with the step on random states", disagree n r seed (max cases 200) == 0)) ++
  [ ("freshName gives a name not taken",
      ((List.range (max cases 200)).all fun i =>
        let (taken, _) := drawNames (mkStdGen (seed + i))
        let f := freshName taken "b"
        !taken.contains f && (taken.contains "b" || f == "b"))) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversmt`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversmt" then return 0
  let mut failed := 0
  for (name, ok) in fixedChecks ++ propertyChecks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversmt: {name}"
  return failed

end DiscoverSmtTests
