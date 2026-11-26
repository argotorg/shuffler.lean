import Skel.Lean.Refute
import Skel.Discover.Machine
import Skel.Discover.Cover
import Skel.Discover.Targets
import Skel.Discover.Prompt
import Skel.TempDir

/-! The tests of a loop whose body calls a callee that is given by its L3 spec (suite `discovercall`, task DISC-CALL):
`lake exe skel-test --only discovercall`. A check that does not hold prints one `FAIL` line.

- The toy (`cBlocks`): a loop over `i < n` whose body calls a callee on `i` and adds its result to `acc`. The callee has
  machine blocks (`incBlocks`: `x + 1`) and an L3 spec (`incSpec`). `wrongSpec` differs from the machine code at `x = 3`.
- The refuter runs `Skel.Refute.inline cBlocks incSpec`: a good invariant passes with each edge covered, a wrong one is refuted;
  with `wrongSpec` the good invariant is refuted (the run uses the spec, not the machine code).
- The negative: `refuteCallee` compares the spec runner with the run of the machine blocks of the callee: `incSpec` passes,
  `wrongSpec` is `real`.
- The pool of the machine step (`machineStepExpr`) of the toy, run in a Lean process: with the runner it has the counter
  features, and the inlined blocks `inline cBlocks incRun` have the same pool; with no runner, or a runner that is not defined,
  it is the named error.
- The edges of the pass of `mapInPlace` at `LBB30_1` (`Cover.passEdges`): each call block of the pass has the edge to its
  continuation; a function with no unit names the cause of the unit after the call in a loop.
- The prompt of the proposer of a site with a call (`promptText`) has the callee, its L3 spec and the rule that a call goes on
  with the result of the spec; a site with no call has no such section. -/

namespace DiscoverCallTests

open Skel Skel.Refute Skel.Discover Coordinator.Dst Lift.Sem

/-! ## The toy -/

inductive CL where
  | head | body | done
  deriving DecidableEq, Repr

structure CS where
  i : Nat
  n : Nat
  acc : Nat

/-- The loop: `head` tests `i < n`, `body` calls the callee on `i` and goes on at `head` with the sum, `done` returns `acc`. -/
def cBlocks : Blocks CL CS Nat Unit (fun _ => Nat) (fun _ => Nat) where
  step
    | .head, x => .ok (if x.i < x.n then .goto .body x else .goto .done x)
    | .body, x => .ok (.call () x.i fun y => (.head, { x with i := x.i + 1, acc := x.acc + y }))
    | .done, x => .ok (.ret x.acc)

inductive IL where
  | entry
  deriving DecidableEq, Repr

/-- The machine blocks of the callee: `x + 1`. -/
def incBlocks : Leaf IL Nat Nat where
  step
    | .entry, x => .ok (.ret (x + 1))

/-- The run of the machine blocks of the callee. -/
def incMachine (_ : Unit) (x : Nat) : Res Nat := incBlocks.run (fun f => f.elim) 2 .entry x

/-- The L3 spec of the callee. -/
def incSpec (_ : Unit) (x : Nat) : Res Nat := .ok (x + 1)

/-- A spec that disagrees with the machine code at `x = 3`. -/
def wrongSpec (_ : Unit) (x : Nat) : Res Nat := .ok (if x = 3 then 7 else x + 1)

def sumTo (i : Nat) : Nat := ((List.range i).map (· + 1)).sum

def cOut (_ : Unit) (x : CS) : Nat := x.acc + (sumTo x.n - sumTo x.i)
def cMeasure (_ : Unit) (x : CS) : Nat := x.n - x.i
def cGood (_ : Unit) (x : CS) : Bool := x.i ≤ x.n && x.acc == sumTo x.i
/-- The wrong invariant: the sum is the index. It holds at `i ≤ 1` only. -/
def cWrong (_ : Unit) (x : CS) : Bool := x.i ≤ x.n && x.acc == x.i

def cAdmitted (g : Rng) : Unit × CS × Nat :=
  let n := ((g.stream 0).natIn 0 6).1
  ((), ⟨0, n, 0⟩, sumTo n)

def cFree (g : Rng) : Unit × CS :=
  let n := ((g.stream 0).natIn 0 6).1
  let i := ((g.stream 1).natIn 0 n).1
  let acc := if ((g.stream 2).bool).1 then sumTo i else ((g.stream 3).natIn 0 30).1
  ((), ⟨i, n, acc⟩)

def cEdges : List (String × Edge CL) :=
  [("head->body", (.head, some .body)), ("head->done", (.head, some .done)), ("body->head", (.body, some .head)),
   ("done->ret", (.done, none))]

def refuteWith (run : Unit → Nat → Res Nat) (I : Unit → CS → Bool) : CovFound :=
  refuteLoopCov cEdges (inline cBlocks run) .head 8 I cMeasure cOut cAdmitted cFree 7 40

def isRefuted : CovFound → Bool
  | .found (.real ..) | .found (.cti ..) => true
  | _ => false

def pureChecks : List (String × Bool) :=
  [ ("a good invariant passes on the loop with the spec runner, each edge covered", refuteWith incSpec cGood == .found (.pass 40)),
    ("the good invariant passes on the loop with the machine runner", refuteWith incMachine cGood == .found (.pass 40)),
    ("a wrong invariant is refuted", isRefuted (refuteWith incSpec cWrong)),
    ("with the wrong spec the good invariant is refuted: the loop runs the spec", isRefuted (refuteWith wrongSpec cGood)),
    ("the spec agrees with the machine callee on the samples",
      refuteCallee (fun g => ((g.stream 0).natIn 0 9).1) id (incSpec ()) (incMachine ()) 7 40 == .pass 40),
    ("a spec that disagrees with the machine callee is real",
      refuteCallee (fun g => ((g.stream 0).natIn 0 9).1) id (wrongSpec ()) (incMachine ()) 7 40 matches .real ..) ]

/-! ## The pool of the machine step -/

/-- The model text of the toy for the pool file, with the runner `incRun` (the spec). -/
def poolModel : String := "
inductive CL where
  | head | body | done

structure CS where
  i : Nat
  n : Nat
  acc : Nat

def cBlocks : Blocks CL CS Nat Unit (fun _ => Nat) (fun _ => Nat) where
  step
    | .head, x => .ok (if x.i < x.n then .goto .body x else .goto .done x)
    | .body, x => .ok (.call () x.i fun y => (.head, { x with i := x.i + 1, acc := x.acc + y }))
    | .done, x => .ok (.ret x.acc)

def incRun (_ : Unit) (x : Nat) : Res Nat := .ok (x + 1)

def cLeaf : Leaf CL CS Nat := Skel.Refute.inline cBlocks incRun
"

def poolOf (dir : System.FilePath) (name : String) (callee : Option String) (blocks : String := "cBlocks") :
    IO (Except String Skel.Discover.Pool) :=
  runPool (poolFile ["Lift.Sem.Blocks", "Skel.Lean.Refute"] "DiscoverCallPool" "Lift.Sem" poolModel blocks "head" callee)
    (dir / s!"{name}.lean") 120000

def hasErr (p : Except String Skel.Discover.Pool) (t : String) : Bool :=
  match p with
  | .error e => (e.splitOn t).length > 1
  | .ok _ => false

def poolChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discovercall-pool"
  let ok ← poolOf dir "withRun" (some "incRun")
  let none_ ← poolOf dir "noRun" none
  let bad ← poolOf dir "badRun" (some "nowhere")
  let leaf ← poolOf dir "leaf" none "cLeaf"
  let feats := match ok with
    | .ok p => p.features.map (·.1 : Feature × Nat → Feature)
    | .error _ => []
  pure
    [ (s!"the pool of a pass with a call and a runner has the features of the state: {repr feats} {match ok with | .error e => e | .ok _ => ""}",
        feats.contains (Feature.field ["st", "n"]) && feats.contains (Feature.field ["st", "i"])),
      ("the pool of the inlined blocks (a Leaf) is the pool of the blocks with the runner", leaf.toOption.isSome && leaf.toOption == ok.toOption),
      ("a pass with a call and no runner is the named error", hasErr none_ "a call in the pass with no runner of the callee"),
      (s!"a runner that is not defined is an error that names it: {match bad with | .error e => e | .ok _ => "ok"}", hasErr bad "nowhere") ]

/-! ## The edges of a call -/

open Skel.Gen in
/-- Each call block of the pass of `mapInPlace` at `LBB30_1` has the edge to its continuation. -/
def edgeChecks : List (String × Bool) :=
  match Skel.Discover.Targets.blocksOfFn "mapInPlace" with
  | none => [("the blocks of mapInPlace", false)]
  | some bs =>
    let es := Cover.passEdges bs "LBB30_1"
    let calls := bs.filterMap fun b => match b.term with
      | .exit (.call _ k) => (bs.find? (·.offset == k)).map fun t => (b.name.s, t.name.s)
      | _ => none
    let onPass := calls.filter fun (a, _) => es.any (·.2.2 == some a)
    let failed := Skel.Discover.Upper.failedWithBlocks "mapInPlace" "the cause" bs
    [ ("the pass of mapInPlace at LBB30_1 has a call block", !onPass.isEmpty),
      ("a call in a loop of a function with no unit names the cause of the unit after the call",
        failed.any fun r => r.error.any fun e => e.startsWith "unsupported: call in loop" && (e.splitOn "no-unit: the cause").length > 1),
      ("each call block of the pass has the edge to its continuation",
        onPass.all fun (a, k) => es.any fun (_, x, y) => x == a && y == some k) ]

/-! ## The prompt of a site with a call -/

def toySite (callees : List CalleeSpec) : LoopSite :=
  { fn := "toyCall", kind := .machine "head", stateTy := "CS", params := [],
    step := "fun (st : CS) => match Skel.Refute.stepTo blocksP Lbl.head 8 Lbl.head st with | .head y => Skel.Discover.Step.cont y | .ret r => Skel.Discover.Step.exit r | .fail _ => Skel.Discover.Step.fault",
    fuelExpr := none, entry := "True", exitResult := none, callees }

def incCallee : CalleeSpec :=
  { name := "toyInc", run := "incSpec", text := "def incSpec (_ : Unit) (x : Nat) : Res Nat := .ok (x + 1)" }

def promptOf (cs : List CalleeSpec) : String :=
  promptText { site := toySite cs, features := [], rows := [], passed := [], rejected := [] }

def has (t p : String) : Bool := (t.splitOn p).length > 1

def promptChecks : List (String × Bool) :=
  let p := promptOf [incCallee]
  [ ("the prompt of a site with a call has the section of the callees", has p "## Callees"),
    ("the prompt names the callee and its spec constant", has p "callee: toyInc, L3 spec: incSpec"),
    ("the prompt has the text of the spec", has p incCallee.text),
    ("the prompt says that the call goes on with the result of the spec", has p "goes on with the result of its L3 spec"),
    ("the prompt of a site with no call has no section of the callees", !has (promptOf []) "## Callees"),
    ("the JSON of a site keeps its callees",
      (Lean.fromJson? (Lean.toJson (toySite [incCallee])) : Except String LoopSite).toOption == some (toySite [incCallee])) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discovercall" then return 0
  let io ← poolChecks
  let mut failed := 0
  for (name, ok) in pureChecks ++ edgeChecks ++ promptChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discovercall: {name}"
  return failed

end DiscoverCallTests
