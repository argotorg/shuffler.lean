import Skel.Discover.Site

/-! The tests of `Skel/Discover/Site.lean` (suite `discoversite`): `lake exe skel-test --only discoversite`. Each check
is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed
checks. A property draws `max cases 200` cases: the case `i` is drawn by the generator of seed `seed + i`.

The test functions are below. `siteOf?` runs on each of them when this module is built (`site_json%`), and the suite
reads the JSON of the result. `#def_step` parses the step text of a site and elaborates it as a definition, so the
suite runs the step text that `siteOf?` gives: the step equals one unfolding of the function on random states. -/

namespace DiscoverSiteTests

open Lean Skel.Gen Skel.Discover

/-! ## The test functions -/

/-- The state of the count-down. -/
structure Cnt where
  k : Nat
  acc : Nat
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/-- A count-down on a record state, through `Option`. -/
def countDown : Nat → Cnt → Option Nat
  | 0, _ => none
  | n + 1, s => if s.k = 0 then some s.acc else countDown n { s with k := s.k - 1, acc := s.acc + 2 }

/-- The state of the vector loop. -/
structure VSt where
  v : Vector Nat 8
  i : Nat
  deriving Repr, BEq

/-- One element of the vector loop: an error above `lim`, else the successor. -/
def bump (lim x : Nat) : Except String Nat := if x > lim then .error "big" else .ok (x + 1)

/-- A loop over a `Vector`, with a constant parameter before the fuel, a `match` on the fuel in the body, and a `do`
bind of `Except` before the call. -/
def vecLoop (lim : Nat) (fuel : Nat) (s : VSt) : Except String VSt :=
  match fuel with
  | 0 => .error "fuel"
  | n + 1 =>
    if h : s.i < 8 then do
      let x ← bump lim s.v[s.i]
      vecLoop lim n { s with v := s.v.set s.i x h, i := s.i + 1 }
    else .ok s

/-- A status type. -/
inductive Status where
  | ok | stop | spent
  deriving Repr, BEq

/-- A class of an element: `none` for a multiple of 3, else whether it is even. -/
def classify (x : Nat) : Option Bool := if x % 3 = 0 then none else some (x % 2 = 0)

/-- A loop on a pair state with a `List` and a `Fin`, a status result, and two calls in two branches of a `match`. -/
def branchLoop : Nat → List Nat × Fin 5 → Status × Nat
  | 0, _ => (.spent, 0)
  | n + 1, (xs, c) =>
    match xs with
    | [] => (.ok, c.val)
    | x :: rest =>
      match classify x with
      | none => (.stop, x)
      | some true => branchLoop n (rest, c + 1)
      | some false => branchLoop n (rest, c)

/-- Two recursive calls on one path: no one-step function. -/
def twoCalls : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => twoCalls n s + twoCalls n (s + 1)

/-- A call that is not in a tail position. -/
def notTail : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => notTail n (s + 1) + 1

/-- A call that gives every argument unchanged: no state. -/
def sameState : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, s => if s > 3 then some s else sameState n s

/-- Two state arguments, so the state is a pair; a `match` on the fuel, then a `match` on the list. -/
def sumTwo (fuel acc : Nat) (xs : List Nat) : Nat :=
  match fuel with
  | 0 => acc
  | n + 1 => match xs with
    | [] => acc
    | x :: rest => sumTwo n (acc + x) rest

/-- A `match` on the fuel and the list at once, whose `n + 1` cases the list decides: a reported limit. -/
def sumJoint : Nat → Nat → List Nat → Nat
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | n + 1, acc, x :: rest => sumJoint n (acc + x) rest

/-- A function with no recursion. -/
def notLoop (k s : Nat) : Nat := k + s

/-- A recursion on a `Nat` that is not structural on a fuel. -/
def halves (k : Nat) : Nat := if h : k = 0 then 0 else halves (k / 2) + 1
termination_by k
decreasing_by omega

/-! ## The results of `siteOf?`, computed when this module is built -/

/-- The JSON of a result: `{"ok": site}`, `{"shape": what}`, `{"noFunction": name}`, or `{"other": repr}`. -/
def resultJson : Except GenError LoopSite → Json
  | .ok s => Json.mkObj [("ok", toJson s)]
  | .error (.shape _ w) => Json.mkObj [("shape", w)]
  | .error (.noFunction n) => Json.mkObj [("noFunction", n)]
  | .error e => Json.mkObj [("other", reprStr e)]

open Elab Term in
/-- `site_json% f`: the JSON text of `siteOf? f`, run when the term is elaborated. -/
elab "site_json% " f:ident : term => do
  let r ← siteOf? f.getId
  pure (mkStrLit (resultJson r).compress)

open Elab Command in
/-- `#def_step d f`: the definition `d` whose value is the step text of `siteOf? f`, parsed and elaborated. -/
elab "#def_step " d:ident f:ident : command => do
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  match ← liftTermElabM (siteOf? fn) with
  | .error e => throwError "siteOf? {fn}: {repr e}"
  | .ok site =>
    match Parser.runParserCategory (← getEnv) `term site.step with
    | .error msg => throwError "the step text does not parse: {msg}\n{site.step}"
    | .ok stx => elabCommand (← `(def $d := $(⟨stx⟩)))

def countDownJson : String := site_json% DiscoverSiteTests.countDown
def vecLoopJson : String := site_json% DiscoverSiteTests.vecLoop
def branchLoopJson : String := site_json% DiscoverSiteTests.branchLoop
def twoCallsJson : String := site_json% DiscoverSiteTests.twoCalls
def notTailJson : String := site_json% DiscoverSiteTests.notTail
def sameStateJson : String := site_json% DiscoverSiteTests.sameState
def sumTwoJson : String := site_json% DiscoverSiteTests.sumTwo
def sumJointJson : String := site_json% DiscoverSiteTests.sumJoint
def notLoopJson : String := site_json% DiscoverSiteTests.notLoop
def halvesJson : String := site_json% DiscoverSiteTests.halves
def missingJson : String := site_json% DiscoverSiteTests.noSuchFunction

#def_step countDownStep DiscoverSiteTests.countDown
#def_step vecLoopStep DiscoverSiteTests.vecLoop
#def_step branchLoopStep DiscoverSiteTests.branchLoop
#def_step sumTwoStep DiscoverSiteTests.sumTwo

/-! ## The checks of the sites -/

/-- The site of a JSON result, when it is `{"ok": site}` and the site parses. -/
def siteOfJson (s : String) : Option LoopSite :=
  match Json.parse s with
  | .ok j => match j.getObjVal? "ok" with
    | .ok o => (fromJson? o).toOption
    | .error _ => none
  | .error _ => none

/-- The value of the key `k` of a JSON result, when it is a string. -/
def errOfJson (k s : String) : Option String :=
  match Json.parse s with
  | .ok j => (j.getObjValAs? String k).toOption
  | .error _ => none

/-- `t` contains `p`. -/
def has (t p : String) : Bool := (t.splitOn p).length > 1

/-- The fields of a site that `siteOf?` fills from the function, other than the step text. -/
def fieldsAre (s : Option LoopSite) (fn stateTy : String) (params : List (String × String)) : Bool :=
  match s with
  | some s => s.fn == fn && s.kind == .fueled && s.stateTy == stateTy && s.params == params &&
      s.fuelExpr == none && s.entry == "True" && s.exitResult == none && has s.step "Skel.Discover.Step.cont"
  | none => false

def siteChecks : List (String × Bool) :=
  [ ("countDown: a site with the record state and no parameter",
      fieldsAre (siteOfJson countDownJson) "DiscoverSiteTests.countDown" "DiscoverSiteTests.Cnt" []),
    ("vecLoop: a site with the parameter lim before the fuel",
      fieldsAre (siteOfJson vecLoopJson) "DiscoverSiteTests.vecLoop" "DiscoverSiteTests.VSt" [("lim", "Nat")]),
    ("branchLoop: a site with the pair state, two tail calls in two branches",
      fieldsAre (siteOfJson branchLoopJson) "DiscoverSiteTests.branchLoop" "List Nat × Fin 5" []),
    ("the step text of vecLoop binds Except through Step.bindExcept",
      ((siteOfJson vecLoopJson).map (has ·.step "Skel.Discover.Step.bindExcept")) == some true),
    ("twoCalls: GenError.shape that names two calls",
      (errOfJson "shape" twoCallsJson).map (has · "two recursive calls") == some true),
    ("twoCalls: no site", siteOfJson twoCallsJson == none),
    ("notTail: GenError.shape that names the tail position",
      (errOfJson "shape" notTailJson).map (has · "not in a tail position") == some true),
    ("sumTwo: a site with the pair of the two state arguments",
      fieldsAre (siteOfJson sumTwoJson) "DiscoverSiteTests.sumTwo" "Nat × List Nat" []),
    ("sameState: GenError.shape that names the missing state",
      (errOfJson "shape" sameStateJson).map (has · "no state argument") == some true),
    ("sumJoint (a match on the fuel and the list at once): GenError.shape that names the missing fuel",
      (errOfJson "shape" sumJointJson).map (has · "no fuel argument") == some true),
    ("notLoop: GenError.shape that names the missing fuel",
      (errOfJson "shape" notLoopJson).map (has · "no fuel argument") == some true),
    ("halves: GenError.shape that names the missing fuel",
      (errOfJson "shape" halvesJson).map (has · "no fuel argument") == some true),
    ("a missing constant: GenError.noFunction with its name",
      errOfJson "noFunction" missingJson == some "DiscoverSiteTests.noSuchFunction") ]

/-! ## The step equals one unfolding -/

/-- Two results are equal when both are values or both are errors, and the two are equal. -/
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- One unfolding of `f` at the fuel `n + 1` from `x` equals the step: the call on the next state, or the exit value. A
step never gives `fault` for a fueled site. -/
def unfoldsOnce {σ R : Type} [BEq R] (f : Nat → σ → R) (step : σ → Step σ R) (n : Nat) (x : σ) : Bool :=
  match step x with
  | .cont x' => f (n + 1) x == f n x'
  | .exit r => f (n + 1) x == r
  | .fault => false

/-- A random count-down state and fuel. -/
def drawCnt (g : StdGen) : (Nat × Cnt) × StdGen :=
  let (n, g) := randNat g 0 25
  let (k, g) := randNat g 0 20
  let (a, g) := randNat g 0 100
  ((n, ⟨k, a⟩), g)

/-- A random vector state, bound and fuel. -/
def drawVSt (g : StdGen) : (Nat × Nat × VSt) × StdGen :=
  let (n, g) := randNat g 0 10
  let (lim, g) := randNat g 0 12
  let (i, g) := randNat g 0 9
  let (xs, g) := (List.range 8).foldl (fun (acc, g) _ => let (x, g) := randNat g 0 12; (acc ++ [x], g)) ([], g)
  let v : Vector Nat 8 := Vector.ofFn fun j => xs.getD j.val 0
  ((n, lim, ⟨v, i⟩), g)

/-- A random list-and-index state and fuel. -/
def drawPair (g : StdGen) : (Nat × (List Nat × Fin 5)) × StdGen :=
  let (n, g) := randNat g 0 8
  let (len, g) := randNat g 0 6
  let (xs, g) := (List.range len).foldl (fun (acc, g) _ => let (x, g) := randNat g 0 9; (acc ++ [x], g)) ([], g)
  let (c, g) := randNat g 0 4
  ((n, (xs, Fin.ofNat 5 c)), g)

/-- A wrong step of the count-down: it adds 1, not 2. The check must refute it on some case. -/
def countDownWrong (s : Cnt) : Step Cnt (Option Nat) :=
  if s.k = 0 then .exit (some s.acc) else .cont { s with k := s.k - 1, acc := s.acc + 1 }

/-- The number of the cases `0 .. max cases 200 - 1` on which `ok` fails. -/
def failures (seed cases : Nat) (ok : StdGen → Bool) : Nat :=
  ((List.range (max cases 200)).filter fun i => !ok (mkStdGen (seed + i))).length

def stepChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("countDown: the step text equals one unfolding",
      failures seed cases (fun g => let ((n, x), _) := drawCnt g; unfoldsOnce countDown countDownStep n x) == 0),
    ("vecLoop: the step text equals one unfolding",
      failures seed cases (fun g =>
        let ((n, lim, x), _) := drawVSt g; unfoldsOnce (vecLoop lim) (vecLoopStep lim) n x) == 0),
    ("branchLoop: the step text equals one unfolding",
      failures seed cases (fun g => let ((n, x), _) := drawPair g; unfoldsOnce branchLoop branchLoopStep n x) == 0),
    ("sumTwo: the step text equals one unfolding",
      failures seed cases (fun g =>
        let ((n, (xs, c)), _) := drawPair g
        unfoldsOnce (fun k (s : Nat × List Nat) => sumTwo k s.1 s.2) sumTwoStep n (c.val, xs)) == 0),
    ("a wrong step fails the unfolding check on some case",
      failures seed cases (fun g => let ((n, x), _) := drawCnt g; unfoldsOnce countDown countDownWrong n x) > 0) ]

/-! ## The JSON codec -/

/-- A random string over a set of characters that includes quotes, a backslash, a newline and non-ASCII letters. -/
def drawStr (g : StdGen) : String × StdGen :=
  let cs := "ab_ \"\\\n:σ→×{}[]0".toList
  let (len, g) := randNat g 0 8
  (List.range len).foldl (fun (s, g) _ => let (i, g) := randNat g 0 (cs.length - 1); (s.push (cs.getD i 'a'), g))
    ("", g)

/-- A random optional string. -/
def drawOpt (g : StdGen) : Option String × StdGen :=
  let (b, g) := randNat g 0 1
  if b == 0 then (none, g) else let (s, g) := drawStr g; (some s, g)

/-- A random site. -/
def drawSite (g : StdGen) : LoopSite × StdGen :=
  let (fn, g) := drawStr g
  let (k, g) := randNat g 0 2
  let (head, g) := drawStr g
  let kind : LoopKind := match k with | 0 => .fueled | 1 => .wf | _ => .machine head
  let (stateTy, g) := drawStr g
  let (np, g) := randNat g 0 3
  let (params, g) := (List.range np).foldl
    (fun (acc, g) _ => let (a, g) := drawStr g; let (b, g) := drawStr g; (acc ++ [(a, b)], g)) ([], g)
  let (step, g) := drawStr g
  let (fuelExpr, g) := drawOpt g
  let (entry, g) := drawStr g
  let (exitResult, g) := drawOpt g
  ({ fn, kind, stateTy, params, step, fuelExpr, entry, exitResult }, g)

/-- A random step over `Nat` states and `String` results. -/
def drawStep (g : StdGen) : Step Nat String × StdGen :=
  let (k, g) := randNat g 0 2
  let (n, g) := randNat g 0 1000
  let (s, g) := drawStr g
  (match k with | 0 => .cont n | 1 => .exit s | _ => .fault, g)

/-- A fixed site, for the checks of a JSON that lacks a key. -/
def site0 : LoopSite :=
  { fn := "f", kind := .machine "h", stateTy := "S", params := [("p", "Nat")], step := "fun s => .fault",
    fuelExpr := some "2 * s.n", entry := "True", exitResult := none }

/-- The JSON of `site0` with the value of each key changed by `f` (`none` drops the key). -/
def edited (f : String → Json → Option Json) : Json :=
  match toJson site0 with
  | .obj kvs => Json.mkObj (kvs.toList.filterMap fun (k, v) => (f k v).map (k, ·))
  | j => j

/-- The JSON of `site0` without the key `k`. -/
def without (k : String) : Json := edited fun k' v => if k' == k then none else some v

def jsonChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("a site: fromJson (toJson s) = s",
      failures seed cases (fun g => let (s, _) := drawSite g; (fromJson? (toJson s) : Except String LoopSite) == .ok s)
        == 0),
    ("a site: the round trip through the compressed text",
      failures seed cases (fun g =>
        let (s, _) := drawSite g
        ((Json.parse (toJson s).compress).bind fromJson? : Except String LoopSite) == .ok s) == 0),
    ("a step: fromJson (toJson s) = s",
      failures seed cases (fun g =>
        let (s, _) := drawStep g; (fromJson? (toJson s) : Except String (Step Nat String)) == .ok s) == 0),
    ("the sites of the test functions round trip",
      [countDownJson, vecLoopJson, branchLoopJson].all fun t =>
        match siteOfJson t with
        | some s => (fromJson? (toJson s) : Except String LoopSite) == .ok s
        | none => false),
    ("a site without the key step does not parse",
      ((fromJson? (without "step") : Except String LoopSite) matches .error _)),
    ("a site without the key kind does not parse",
      ((fromJson? (without "kind") : Except String LoopSite) matches .error _)),
    ("a site with a kind of another type does not parse",
      ((fromJson? (edited fun k v => some (if k == "kind" then Json.num 3 else v)) : Except String LoopSite)
        matches .error _)),
    ("the JSON of site0 with no change parses to site0",
      (fromJson? (edited fun _ v => some v) : Except String LoopSite) == .ok site0) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversite`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversite" then return 0
  let mut failed := 0
  for (name, ok) in siteChecks ++ stepChecks seed cases ++ jsonChecks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversite: {name}"
  return failed

end DiscoverSiteTests
