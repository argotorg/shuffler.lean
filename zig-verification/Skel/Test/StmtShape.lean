import Skel.IntQ
import Skel.Full.Driver
import Lift.Shuffler.Internal.Proposed.Layout

/-! The tests of the binders of the proposed statements (suite `stmtshape`, task STMT-SHAPE): `lake exe skel-test --only
stmtshape`, from the repository root. No paid call.

The upper chain (`Skel.Gen.binderOf`, `Skel/Gen/UpperPlan.lean`) takes a binder of the type `BitVec 64` or `List (BitVec 64)`
only. The template of INT-Q (`Skel.IntQ.fill`) writes one `BitVec 64` binder for each field of `Layout.Env` that the holes read,
and no binder `e : Layout.Env`.

Checks:
* `envFields` and `layoutReads` are the fields of `Layout.Env` and the fields that each function of `Layout` reads, as Lean
  elaborates them.
* The fields that the holes read: none for workspaceSize; self, spills, pad for isSpilled; self, data, mapping for permute (the
  accepted reply of DeepSeek, `tools/shuffler-pilot/intq-replies-run/`). A use of `e` that the rule does not know reads each field.
* Negative: the fields that no hole reads have no binder, and the statement names them.
* `#stmt_shape` reads the filled template of the good isSpilled reply and of the DeepSeek replies of workspaceSize and permute,
  and each binder passes `binderOf`.
* The committed statements of workspaceSize and isSpilled give their upper rows on the path of `skel full`.
* `post` gives the result in the form of the moved statements, `Encode.encode t = [r]`, with `t` the result field; it has the
  memory clause only when WRITTEN is not `[]` (permute). -/

namespace StmtShapeTests

open Lean Elab Term Meta in
/-- The fields of `Layout.Env` with their widths, and, for each definition of `Layout` with a parameter of the type `Env`, the
fields whose projections its value names: what Lean elaborates, to compare with the tables of `Skel.IntQ`. -/
elab "layout_tables%" : term => do
  let env ← getEnv
  let envName := ``Lift.Shuffler.Internal.Proposed.Layout.Env
  let pre := `Lift.Shuffler.Internal.Proposed.Layout
  let fields := getStructureFields env envName
  let widths ← fields.toList.mapM fun f => do
    let some ci := env.find? (envName ++ f) | throwError "no projection {f}"
    let ty ← forallTelescope ci.type fun _ b => whnfR b
    let some n ← (evalNat ty.appArg!).run | throwError "field {f}: not BitVec n"
    pure (f.toString, n)
  let some idx := env.getModuleIdxFor? envName | throwError "no module of Env"
  let names := env.header.moduleData[idx.toNat]!.constNames.toList
  let defs := names.filter fun c => c.getPrefix == pre && !c.isInternal
  let reads ← defs.filterMapM fun c => do
    let some ci := env.find? c | pure none
    let some v := ci.value? | pure none
    unless ci.type.getUsedConstants.contains envName do return none
    let used := v.getUsedConstants
    pure (some (c.getString!, (fields.toList.filter fun f => used.contains (envName ++ f)).map (·.toString)))
  let sorted := reads.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  return toExpr (widths, sorted)

def elaborated : List (String × Nat) × List (String × List String) := layout_tables%

def isErr {α ε : Type} (e : Except ε α) : Bool := match e with | .ok _ => false | .error _ => true

def holesOf (dir : System.FilePath) (n : String) : IO Skel.IntQ.Holes := do
  IO.ofExcept ((Skel.IntQ.parseHoles (← IO.FS.readFile (dir / s!"{n}.reply"))).mapError IO.userError)

def good : System.FilePath := "tools/shuffler-pilot/intq-replies"
def run' : System.FilePath := "tools/shuffler-pilot/intq-replies-run"

def allFields : List String := Skel.IntQ.envFields.map (·.1)

def pureChecks : IO (List (String × Bool)) := do
  let ws ← holesOf run' "WorkspaceSize"
  let sp ← holesOf good "IsSpilled"
  let pm ← holesOf run' "Permute"
  let odd := { sp with args := "[⟨.W64, Lift.Shuffler.Internal.Proposed.Layout.Env.self e⟩]" }
  let sorted := Skel.IntQ.layoutReads.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  pure
    [ ("envFields is the list of the fields of Layout.Env with their widths", Skel.IntQ.envFields == elaborated.1),
      ("layoutReads is the list of the fields that each function of Layout reads", sorted == elaborated.2),
      ("workspaceSize reads no field", Skel.IntQ.envReads ws == []),
      ("isSpilled reads self, spills and pad", Skel.IntQ.envReads sp == ["self", "spills", "pad"]),
      ("permute reads self, data and mapping", Skel.IntQ.envReads pm == ["self", "data", "mapping"]),
      ("a use of e that the rule does not know reads each field", Skel.IntQ.envReads odd == allFields),
      ("a name that has e in it is no use of e",
        Skel.IntQ.envReads { ws with args := "[⟨.W64, e2⟩, ⟨.W64, x.e⟩, ⟨.W64, BitVec.ofNat 64 e_1⟩]" } == []) ]

/-- The shape of the filled template of the holes `h` for the target `n`, as `#stmt_shape` reads it. -/
def shapeOf (dir : System.FilePath) (ps : List (Skel.IntQ.Target × Except String Skel.IntQ.PromptIn)) (n : String)
    (h : Skel.IntQ.Holes) : IO (Except String Skel.Gen.StmtShape) := do
  let some p := (ps.find? fun (t, _) => Skel.IntQ.stmtName t.label == n).bind (·.2.toOption)
    | return .error s!"no target {n}"
  let (infos, errs) ← Skel.IntQ.runLean dir s!"{n}Shape.lean" (Skel.IntQ.shapeText p.ctx h)
  if let some e := errs.head? then return .error e
  match (infos.filterMap fun t => (Lean.Json.parse t >>= Skel.Gen.Shape.parse).toOption).head? with
  | some sh => return .ok sh
  | none => return .error "no shape"

def binderNames (r : Except String Skel.Gen.StmtShape) : Option (List String) :=
  r.toOption.map fun sh => sh.binders.map (·.name.s)

def passesBinders (r : Except String Skel.Gen.StmtShape) : Bool :=
  match r with
  | .ok sh => !isErr (sh.binders.mapM Skel.Gen.binderOf)
  | .error _ => false

/-- The upper rows of the committed statement of `label`, on the path of `skel full` (`Skel.Full.main`): the shapes of
`runShapes`, the hint records of `types.json` and `specOf`. -/
def upperOf (dir : System.FilePath) (label : String) : IO (Except String Nat) := do
  let proposed := ["WorkspaceSize", "IsSpilled"]
  let srcs := Skel.Gen.Derived.shuffler.map fun (l, _) => (l, Skel.Full.sourceOf l proposed)
  let u := Skel.Full.shufflerUnit fun l => ((srcs.lookup l).map (·.2)).getD ""
  let some f := u.fns.find? (·.entry == label) | return .error s!"no function {label}"
  let src := ((srcs.lookup label).map (·.1)).getD .none
  let modOf (g : Skel.Report.Level3.PFn) : String := (((srcs.lookup g.entry).bind (·.1.module?))).getD ""
  let (shapes, _) ← Skel.Report.Level3.runShapes dir [f] modOf 600000
  let records := (Lean.Json.parse (← IO.FS.readFile "Lift/LLVM/data/shuffler/types.json")).bind Skel.Gen.ZigHint.records
  let shapeOf (g : Skel.Report.Level3.PFn) := (shapes.lookup g.short).getD (.error "no statement shape")
  let spec := Skel.Full.specOf u f src (some (Skel.Report.Level3.stmtConstOf modOf f)) shapeOf
    (Skel.Report.Level3.hintFor records)
  pure ((spec.input [] none).upper.map (·.generated.obligations.length))

def leanChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "stmtshape"
  let ps ← Skel.IntQ.promptInputs
  let ws ← shapeOf dir ps "WorkspaceSize" (← holesOf run' "WorkspaceSize")
  let sp ← shapeOf dir ps "IsSpilled" (← holesOf good "IsSpilled")
  let pm ← shapeOf dir ps "Permute" (← holesOf run' "Permute")
  let wsUp ← upperOf dir "solidity_shuffler_workspaceSize"
  let spUp ← upperOf dir ".Lshuffler.Emission.isSpilled"
  let some wsP := (ps.find? fun (t, _) => Skel.IntQ.stmtName t.label == "WorkspaceSize").bind (·.2.toOption)
    | throw (IO.userError "no WorkspaceSize target")
  let wsText := Skel.IntQ.fill wsP.ctx (← holesOf run' "WorkspaceSize") "check"
  let rows (r : Except String Nat) : Bool := match r with | .ok n => n > 0 | .error _ => false
  let spText := Skel.IntQ.fill (← IO.ofExcept ((ps.find? fun (t, _) => Skel.IntQ.stmtName t.label == "IsSpilled").bind
    (·.2.toOption) |>.elim (.error "no IsSpilled target") .ok)).ctx (← holesOf good "IsSpilled") "check"
  let pmP ← IO.ofExcept ((ps.find? fun (t, _) => Skel.IntQ.stmtName t.label == "Permute").bind (·.2.toOption)
    |>.elim (.error "no Permute target") .ok)
  let pmText := Skel.IntQ.fill pmP.ctx (← holesOf run' "Permute") "check"
  let moved ← IO.FS.readFile "Lift/Shuffler/Internal/IsRetainedStatement.lean"
  let has (t s : String) : Bool := (t.splitOn s).length > 1
  pure
    [ ("#stmt_shape reads workspaceSize with no binder", binderNames ws == some []),
      ("#stmt_shape reads isSpilled with the binders self, spills, pad", binderNames sp == some ["self", "spills", "pad"]),
      ("#stmt_shape reads permute with the binders self, data, mapping", binderNames pm == some ["self", "data", "mapping"]),
      ("each binder of the three shapes passes binderOf", passesBinders ws && passesBinders sp && passesBinders pm),
      ("negative: the statement has no binder of the type Layout.Env", (wsText.splitOn "∀ e : Layout.Env").length == 1),
      ("negative: the statement names the fields that no hole reads",
        (wsText.splitOn "self, target, spills, data, trace, mapping, pad").length > 1),
      ("the upper rows of workspaceSize are generated", rows wsUp),
      ("the upper rows of isSpilled are generated", rows spUp),
      ("the moved statements give the result as Encode.encode y = [r]", has moved "Encode.encode y = [r]"),
      ("post gives the result as Encode.encode of the result field = [r], with no memory clause when WRITTEN is []",
        has wsText "∃ y, run = some y ∧ Encode.encode (result y) = [r]\n" &&
        has spText "∃ y, run st slot = some y ∧ Encode.encode (result st slot y) = [r]\n" && !has spText "r = result"),
      ("post has the memory clause when WRITTEN is not []",
        has pmText "Encode.encode (result st permutation y) = [r] ∧ ∀ o ∈ written st permutation e y, Mem.has policy m o") ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "stmtshape" then return 0
  let mut failed := 0
  for (name, ok) in (← pureChecks) ++ (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  stmtshape: {name}"
  return failed

end StmtShapeTests
