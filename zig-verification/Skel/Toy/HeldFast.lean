import Skel.Toy.Held
import Lift.Toys.Fast.Code

/-! The held run at ReleaseFast (task AF2-F; the second optimisation level, R-E, `Lift/Toys/Fast/{Code,L1}.lean`). It is
`Skel/Toy/Held.lean` with the target, the code and the check header of the ReleaseFast build of the toys, and nothing
else: the toys, the callees, the hints (`Hints.none`), the block source, the ladder, the checker and the table are those of
`run held`. No hand text is changed, which is what the criterion 6 of D15 measures: the generators have to give a proof of
the same toys at the other optimisation level without a change of a hand input. The ledger is written as for `run held`,
in `.skel/runs/<time>-heldfast`; it has the first lines of the first error of each failed check. The check files of `fn` are
in the namespace `Skel.Gen.HeldFast.<fn>`. -/

namespace Skel.Toy.HeldFast

open Skel Skel.Gen
open Skel.Toy.Held (functions ladderOf tableLines answers refresh noRefute noAsk loggedChecker summaryLine utcStamp logLines)

/-- The module of the L1 of the ReleaseFast unit. -/
def l1 : String := "Lift.Toys.Fast.L1"

/-- The imports of the check files: those of `run held` with the L1 module and the site lemmas of the ReleaseFast unit. -/
def imports : List String :=
  Skel.Toy.Held.imports.map fun m =>
    if m == "Lift.Toys.L1" then l1 else if m == "Skel.Gen.Sites.Toys" then "Skel.Gen.Sites.ToysFast" else m

/-- The interface of each callee of `fn`, with the entry PCs of the ReleaseFast unit (`Held.interfacesIn`). -/
def calleesOf (fn : String) : List Callee :=
  Skel.Toy.Held.interfacesIn Lift.Toys.Fast.Code.code Skel.Toy.Held.source (fun f => s!"Lift.Toys.Fast.{f}PC")
    functions.length fn

/-- The target of `fn`: the step of `Lift.Toys.Fast.L1`, the code from `toyCountPC` to `toyEndPC`, and the entry PC of `fn`. -/
def targetOf (fn : String) : Target :=
  { step := s!"{l1}.step", lo := "Lift.Toys.Fast.toyCountPC", hi := "Lift.Toys.Fast.toyEndPC",
    entryPC := s!"Lift.Toys.Fast.{fn}PC", imports := imports, callees := calleesOf fn }

/-- The generation of `fn` in `Lift.Toys.Fast.Code` alone: as `Held.generateOwn`. -/
def generateOwn (fn : String) : Except GenError Generated :=
  generate (targetOf fn) Hints.none .storeChain Lift.Toys.Fast.Code.code Skel.Toy.Held.source fn

/-- The generation of `fn` in `Lift.Toys.Fast.Code`, with the text of its callees in front of its model: as
`Held.generateOf`. -/
def generateOf (fn : String) : Except GenError Generated := do
  let g ← generateOwn fn
  pure { g with modelText := Skel.Toy.Held.calleeTextIn generateOwn functions.length fn ++ g.modelText }

/-- The header of the check files of `fn`: its own namespace, and the namespace `Lift.Toys.Fast` for the entry PCs. -/
def headerOf (fn : String) : Header :=
  { imports := imports, namespace_ := s!"Skel.Gen.HeldFast.{fn}",
    opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Toys.Fast", "Lift.Spike"] }

/-- The file of a candidate of `fn`: as `Held.renderOf`, with the header of the ReleaseFast unit. -/
def renderOf (fn : String) (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (c : Candidate) : LeanFile :=
  match c with
  | .proof _ text =>
    let h := headerOf fn
    { name := s!"{h.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
      text := Skel.checkFile h g.modelText (answers l ob) ob text }
  | .triple _ _ | .ask _ => { name := "", text := "", limitMs := cfg.limitMs }

/-- The step function of the run of `fn`. -/
def stepFn (fn : String) (cfg : Config) (g : Generated) (ladders : Ladders) : Ledger → Event → Ledger × Action :=
  fun l ev =>
    let (l', a) := Skel.step cfg ladders (renderOf fn cfg g l) l ev
    (l', refresh (renderOf fn cfg g) l' a)

/-- The run of `fn`: as `Held.runFn`, with the generation, the check files and the step function of the ReleaseFast unit. -/
def runFn (dir : System.FilePath) (cfg : Config) (fn : String) :
    IO (Except GenError (List (String × String)) × Nat) := do
  match generateOf fn with
  | .error e =>
    logLines dir (tableLines fn (.error e))
    pure (.error e, 0)
  | .ok g =>
    let report ← drive (loggedChecker dir cfg.gate) noRefute (fun _ _ => pure ()) noAsk
      (stepFn fn cfg g (ladderOf g)) (Ledger.init g.obligations) .start
    logLines dir [Report.render report]
    pure (.ok (report.rows.map fun r => (r.id.name, Skel.Toy.Held.rowRung r)), report.rows.foldl (fun n r => n + r.attempts) 0)

/-- The functions `fns` of the run: each is run with `runFn` below `dir` and its table is printed, then the summary line is
printed and logged in `dir/ledger.txt`. -/
def runFns (dir : System.FilePath) (cfg : Config) (fns : List String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut results : List (Except GenError (List (String × String)) × Nat) := []
  for fn in fns do
    let r ← runFn dir cfg fn
    IO.println fn
    for line in tableLines fn r.1 do
      IO.println line
    IO.println ""
    results := results ++ [r]
  let summary := summaryLine results ((← IO.monoMsNow) - t0)
  logLines dir [summary]
  IO.println summary
  IO.println s!"run directory: {dir}"

/-- `run held --fast`: runs each function of `Held.functions` at ReleaseFast in `.skel/runs/<time>-heldfast`, with its ledger.
The status is 0 when the run completes: open rows and generation failures are results. -/
def runHeldFast (cfg : Config) : IO UInt32 := do
  runFns (".skel" / "runs" / s!"{← utcStamp}-heldfast") cfg functions
  return 0

end Skel.Toy.HeldFast
