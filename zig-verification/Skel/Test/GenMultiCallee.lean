import Skel.TempDir
import Skel.Gen.Generate
import Skel.Gen.Derived.Level2z
import Skel.Io
import Skel.Full.Driver
import Lift.Level2z.Code
import Skel.Test.CallMem.Code
import Skel.Test.GenUpperCall
import Skel.Test.GenUpperResult
import Skel.Test.GenL2CallBlk

/-! The tests of a function that calls more than one callee (suite `multicallee`, task MULTI-CALLEE):
`lake exe skel-test --only multicallee`.

The toy `two` (`Skel/Test/CallMem/Code.lean`) calls `put` (memory in its result) and then `inc` (no memory). Its model
has one callee type `Cal` with one constructor for each callee (`Cal.In`, `Cal.Out`, `Cal.model`); each call block uses
the interface of its callee.

Pure checks: `two` generates, with `.call .c0` for `put` and `.call .c1` for `inc`, and its `decompiles_l2` text has no
`fail`. Negative: a call to a function that is not in the callees of the target is `GenError.callee` with its name. The
shuffler functions that stopped at the second callee generate. CallLoop (level 2: `l2zWrap` and `l2zPtrStore`)
generates.

IO checks (Lean): `put`, `inc` and `two` (block rows by `lift_block`, `decompiles_l2`) are accepted with the standard
axioms; the model of `two` that passes `rbx` to `inc` (not the loaded word) is rejected. CallLoop: `decompiles_l2` with
the block rows and the `decompiles_l2` of each callee as hypotheses is accepted. A caller that discards callee memory is
rejected. Store lemmas preserve mapped input words, including a store with width zero. -/

namespace GenMultiCalleeTests

open Skel Skel.Gen

def has (s part : String) : Bool := (s.splitOn part).length > 1

def replaceAll (s old new : String) : String := new.intercalate (s.splitOn old)

def detOf (g : Generated) : String := ((g.det.find? (·.1.name == "decompiles_l2")).map (·.2)).getD ""

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

def accepted : Outcome → Bool
  | .accepted axs => axs.all standard.contains
  | _ => false

def failed : Outcome → Bool
  | .failed _ => true
  | _ => false

/-! ## The toy `two` -/

def code : Executable := Skel.Test.CallMem.Code.code

def names : String → Option (String × String)
  | ".Lcm.put" => some ("putPC", "Put")
  | ".Lcm.inc" => some ("incPC", "Inc")
  | _ => none

def target (fn : String) (cs : List Callee) : Target :=
  { step := "Skel.Test.CallMem.L1.step", lo := "putPC", hi := "callMemEndPC", entryPC := s!"{fn}PC", imports := [],
    callees := cs }

def callees (fn : String) : Except GenError (List Callee) := calleesFrom code .table names 3 fn

def gen (fn : String) : Except GenError Generated := do
  generate (target fn (← callees fn)) Hints.none .storeChain code .table fn

def pureToy : List (String × Bool) :=
  [ ("calleesFrom two: put (memory) then inc (no memory)",
      match callees "two" with
      | .ok [p, i] => p.name == ".Lcm.put" && p.mem && i.name == ".Lcm.inc" && !i.mem && i.inputs == [.rdi]
      | _ => false),
    ("generate two: one callee type Cal with c0 (put) and c1 (inc)",
      match gen "two" with
      | .ok g => has g.modelText "inductive Cal where\n  | c0\n  | c1" && has g.modelText "| .c0 => Put.In2" &&
          has g.modelText "| .c1 => Inc.In2" && has g.modelText "| .c0 => UInt64 × DataMem" &&
          has g.modelText "| .c1 => UInt64\n" && has g.modelText ".call .c0 ⟨" && has g.modelText ".call .c1 ⟨" &&
          has g.modelText "Blocks Lbl (St In2 DataMem) (UInt64 × DataMem) Cal Cal.In Cal.Out" &&
          has g.modelText "blocks.Returns (fun c => (Cal.model c).returns) .entry (init a) r"
      | .error _ => false),
    ("generate two: the det text of decompiles_l2 has no fail and names the callee family",
      match gen "two" with
      | .ok g => let d := detOf g; d != "" && !has d "fail" && has d "Decompiles.ofBlocks blocks Cal.model"
      | .error _ => false),
    ("negative: a call of inc with no callee inc in the target is GenError.callee .Lcm.inc",
      match callees "two" with
      | .ok cs =>
        match generate (target "two" (cs.filter (·.name != ".Lcm.inc"))) Hints.none .storeChain code .table "two" with
        | .error (.callee ".Lcm.inc") => true
        | _ => false
      | .error _ => false),
    ("put and inc generate with no callee type (one callee or none: the text of before)",
      match gen "put", gen "inc" with
      | .ok p, .ok i => !has p.modelText "inductive Cal" && !has i.modelText "inductive Cal"
      | _, _ => false) ]

def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Skel.Test.CallMem.L1",
    "Lift.Spike.Sites", "Lift.Tactic.Block", "Lift.Sem.StackRoom", "Lift.Spike.Sites.Stack", "Lift.Tactic.FrameMem",
    "Lift.Sem.CallMem"]

/-- The text of a generated function: its model, its block rows (`lift_block`) and `decompiles_l2` with the text `det`. -/
def partText (g : Generated) (model : String) : String :=
  let rows := g.obligations.filterMap fun o =>
    match o.origin with
    | .block l => some s!"theorem {l} : {o.statement} := by intros; first | lift_block"
    | _ => none
  model ++ "\n" ++ "\n\n".intercalate rows ++
    "\n\n" ++ detTheorem "decompiles_l2" "" "Decompiles Skel.Test.CallMem.L1.step l2" (detOf g) ++ "\n"

def toyFile (put inc two : Generated) (twoModel : String) : String :=
  "\n".intercalate (imports.map (s!"import " ++ ·)) ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike\n\nnamespace MultiCall\n\nnamespace Put\n\n" ++
    partText put put.modelText ++ "\nend Put\n\nnamespace Inc\n\n" ++ partText inc inc.modelText ++ "\nend Inc\n\n" ++
    partText two twoModel ++ "\nend MultiCall\n\n#print axioms MultiCall.decompiles_l2\n"

def runFile (name const text : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"multicallee-{name}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") const 300000).1

/-- The model of `two` that passes `rbx` to `inc` (the pointer, not the loaded word). -/
def badArg (m : String) : String :=
  match m.splitOn ".call .c1 ⟨x.input.policy, " with
  | [a, b] =>
    match b.splitOn "⟩" with
    | _ :: rest => a ++ ".call .c1 ⟨x.input.policy, " ++ "m1, x.rbx⟩" ++ "⟩".intercalate rest
    | [] => m
  | _ => m

def toyChecks : IO (List (String × Bool × String)) := do
  match gen "put", gen "inc", gen "two" with
  | .ok p, .ok i, .ok t =>
    let ok ← runFile "two" "MultiCall.decompiles_l2" (toyFile p i t t.modelText)
    let bad := badArg t.modelText
    let mut' ← runFile "two-mut" "MultiCall.decompiles_l2" (toyFile p i t bad)
    pure [ ("two: Lean accepts put, inc and two (rows, decompiles_l2) with the standard axioms", accepted ok, s!"{repr ok}"),
      ("mutation: the model of two that passes rbx to inc is rejected", bad != t.modelText && failed mut', s!"{repr mut'}") ]
  | _, _, _ => pure [("generate put, inc and two", false, "")]

/-! ## The upper chain of `two` (MULTI-CALLEE2)

At L2⁺ the model of `two` has the callee family `CalP` over `Cal`: `put` (memory) is called up to a permutation of the heap
(`CallArm.callee`), `inc` (no memory) by its `l2p.returns` (`Inc.refines_l2p`). The units of both callees give their rows. -/

/-- The callee units of `two`: `put` with the shape of `putCall`'s callee, `inc` with a value shape (`ResSpec.vres x`). -/
def twoUnits : Except GenError (List Callee × List CalleeUnit) := do
  let cs ← callees "two"
  let some p := cs.find? (·.name == ".Lcm.put") | throw (.callee ".Lcm.put")
  let some i := cs.find? (·.name == ".Lcm.inc") | throw (.callee ".Lcm.inc")
  pure (cs, [⟨p, target "put" []⟩,
    ⟨i, target "inc" []⟩])

def twoUpper (units : List CalleeUnit → List CalleeUnit := id) (modules : List (String × String) := []) :
    Except GenError Upper := do
  let (cs, us) ← twoUnits
  generateUpper (target "two" cs) .storeChain code .table "Skel.Test.CallMem.Code.code" "two" (← GenUpperCallTests.toyShape 16)
    GenUpperCallTests.hint ⟨[], [], "Two", []⟩ none (units us) modules

/-- The rows of `two` that the Lean check proves. -/
def twoRows : List String :=
  ["Put.entry", "Put.decompiles_l2", "Put.refines_l2p", "Put.shape", "Inc.entry", "Inc.decompiles_l2", "Inc.refines_l2p"] ++
    ["block.entry", "block.o9", "block.o17", "decompiles_l2", "refines_l2p", "above_l2p"]

/-- The rows of `two` with the callee modules: the callee rows, the L2 rows, `refines_l2p` and `above_l2p`. -/
def twoRow (n : String) : Bool :=
  n.startsWith "Put." || n.startsWith "Inc." || n.startsWith "block." || ["decompiles_l2", "refines_l2p", "above_l2p"].contains n

/-- The contract of `inc` in the negative: the result of `inc` one more than the L2 result. -/
def looseInc : String := "(hInc : Lift.Sem.Refines Inc.SimIn (fun _ _ r r' => r = r' + 1) Inc.l2p.returns Inc.l2.returns)"

/-- The check file of the upper chain of `two`: each row of `twoRows` with its `det` text (a block row: the block rung).
`loose`: the negative, where `refines_l2p` of `two` takes the callee row of `inc` as the binder `looseInc`. -/
def twoFile (loose : Bool := false) : Except GenError String := do
  let g := (← twoUpper).generated
  let thms ← twoRows.filterMapM fun n => do
    let some o := g.obligations.find? (·.id.name == n) | pure none
    let d ← match o.origin, g.det.find? (·.1 == o.id) with
      | .block _, _ => pure "by intros; first | lift_block_split | lift_block"
      | _, some (_, d) => pure d
      | _, none => throw (.shape 0 s!"no det text of {n}")
    if loose && n == "refines_l2p" then
      pure (some s!"theorem refines_l2p {looseInc} : {o.statement} := {replaceAll d "Inc.refines_l2p" "hInc"}")
    else pure (some (Skel.theoremText (Skel.Driver.answerName o) o.statement d))
  pure ("\n".intercalate (GenUpperCallTests.toyImports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ GenUpperResultTests.specText ++ "\nnamespace TwoCheck\n\n" ++
    g.modelText ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend TwoCheck\n\n#print axioms TwoCheck.refines_l2p\n#print axioms TwoCheck.above_l2p\n")

/-! ## The callee module (MULTI-CALLEE2, d)

With the module of the closed callee rows (the argument `modules` of `generateUpper`, FULL-DRV's `Lift/Shuffler/Proved/<F>.lean`), the caller's
chain has only the rows `F.refines_l2p` and `F.shape` of the callee and the L2⁺ texts of `F`; the G1 model and the G1 rows of
`F` come from the module. The Lean check puts the text of each module (the G1 model and the closed G1 rows, as
`Skel/Full/Module.lean` writes it) in the namespace `TwoMod.<F>` of the same file, in place of the import. -/

/-- The module namespaces of the callees of `two`, by label. -/
def mods : List (String × String) := [(".Lcm.put", "TwoMod.Put"), (".Lcm.inc", "TwoMod.Inc")]

def twoUpperMod : Except GenError Upper := twoUpper id mods

/-- The text of the module of the callee `fn` (`put` or `inc`): its G1 model and its G1 rows with their `det` texts. -/
def moduleOf (fn ns : String) : Except GenError String := do
  let g ← gen fn
  let thms := g.obligations.map fun o =>
    let d := match o.origin with
      | .block _ => "by intros; first | lift_block_split | lift_block"
      | _ => detOf g
    Skel.theoremText (Skel.Driver.answerName o) o.statement d
  pure (s!"namespace {ns}\n\n{g.modelText}\n\n" ++ "\n\n".intercalate thms ++ s!"\n\nend {ns}\n")

/-- The check file of `two` with the callee modules: the module texts, then the chain of `two` (its rows and the callee rows
`Put.refines_l2p`, `Put.shape`, `Inc.refines_l2p`). -/
def twoModFile : Except GenError String := do
  let g := (← twoUpperMod).generated
  let thms ← (g.obligations.filter (twoRow ·.id.name)).mapM fun o => do
    let d ← match o.origin, g.det.find? (·.1 == o.id) with
      | .block _, _ => pure "by intros; first | lift_block_split | lift_block"
      | _, some (_, d) => pure d
      | _, none => throw (.shape 0 s!"no det text of {o.id.name}")
    pure (Skel.theoremText (Skel.Driver.answerName o) o.statement d)
  pure ("\n".intercalate (GenUpperCallTests.toyImports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ GenUpperResultTests.specText ++
    (← moduleOf "put" "TwoMod.Put") ++ (← moduleOf "inc" "TwoMod.Inc") ++ "\nnamespace TwoMod.Two\n\n" ++
    g.modelText ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend TwoMod.Two\n\n#print axioms TwoMod.Two.refines_l2p\n#print axioms TwoMod.Two.above_l2p\n")

def pureModule : List (String × Bool) :=
  [ ("with the callee modules: the callee rows of two are Put.refines_l2p, Put.shape and Inc.refines_l2p only",
      match twoUpperMod with
      | .ok u => let ns := u.generated.obligations.map (·.id.name)
        (ns.filter fun n => n.startsWith "Put." || n.startsWith "Inc.") == ["Put.refines_l2p", "Put.shape", "Inc.refines_l2p"]
      | .error _ => false),
    ("with the callee modules: the texts of two hold no G1 text of put or inc, and export the names of the modules",
      match twoUpperMod, gen "put", gen "inc" with
      | .ok u, .ok p, .ok i =>
        let t := u.generated.modelText
        !has t p.modelText && !has t i.modelText && has t "export TwoMod.Put (" && has t "export TwoMod.Inc (" &&
          !(u.generated.det.any fun (id, _) => id.name == "Put.decompiles_l2" || id.name == "Put.entry")
      | _, _, _ => false) ]

def pureUpper : List (String × Bool) :=
  [ ("generateUpper of two: the rows of put and inc come first, then the rows of two",
      match twoUpper with
      | .ok u => let ns := u.generated.obligations.map (·.id.name)
        ns.contains "Put.refines_l2p" && ns.contains "Put.shape" && ns.contains "Inc.refines_l2p" &&
          !ns.contains "Inc.shape" && ns.contains "refines_l2p" && ns.contains "above_l2p" &&
          !u.noText.any (·.1.name == "refines_l2p")
      | .error _ => false),
    ("generateUpper of two: refines_l2p depends on Put.refines_l2p, Put.shape and Inc.refines_l2p",
      match twoUpper with
      | .ok u =>
        let deps := ((u.generated.obligations.find? (·.id.name == "refines_l2p")).map fun o => o.deps.map (·.name)).getD []
        deps.contains "Put.refines_l2p" && deps.contains "Put.shape" && deps.contains "Inc.refines_l2p"
      | .error _ => false),
    ("generateUpper of two: the L2+ model has the callee family CalP over Cal",
      match twoUpper with
      | .ok u => has u.generated.modelText "def CalP.rel" && has u.generated.modelText "Blocks Lbl (St In2p Heap) (UInt64 × Heap) Cal CalP.In CalP.Out"
      | .error _ => false),
    ("negative: generateUpper of two with no unit of inc is an error that names inc",
      match twoUpper (·.filter (·.callee.name != ".Lcm.inc")) with
      | .error (.unsupported _ w) => has w ".Lcm.inc"
      | _ => false) ]

def upperChecks : IO (List (String × Bool × String)) := do
  match twoFile, twoFile true with
  | .ok text, .ok bad =>
    let ok ← runFile "two-upper" "TwoCheck.above_l2p" text
    let neg ← runFile "two-upper-loose" "TwoCheck.refines_l2p" bad
    pure [ ("two: Lean accepts the rows of put and inc, the L2 rows, refines_l2p and above_l2p with the standard axioms",
        accepted ok, s!"{repr ok}"),
      ("negative: refines_l2p of two with a contract of inc that does not match is rejected", bad != text && failed neg,
        s!"{repr neg}") ]
  | _, _ => pure [("the check file of the upper chain of two", false, "")]

def moduleChecks : IO (List (String × Bool × String)) := do
  match twoModFile with
  | .ok text =>
    let ok ← runFile "two-module" "TwoMod.Two.above_l2p" text
    pure [("with the callee modules: Lean accepts refines_l2p and above_l2p of two with the standard axioms", accepted ok, s!"{repr ok}")]
  | .error e => pure [("the check file of two with the callee modules", false, s!"{repr e}")]

/-! ## A callee with memory called from two blocks (MULTI-CALLEE2, c)

`twice` calls `put` from the entry block and from the block after the first call, both at the depth 16: the kept bytes of the
two calls are equal, so one restricted model of `put` serves both. `twoDepth` calls `put` at the depths 16 and 24: the error
names the callee. -/

def twiceUpper : Except GenError Upper := do
  let cs ← callees "twice"
  let some p := cs.find? (·.name == ".Lcm.put") | throw (.callee ".Lcm.put")
  generateUpper (target "twice" cs) .storeChain code .table "Skel.Test.CallMem.Code.code" "twice" (← GenUpperCallTests.toyShape 16)
    GenUpperCallTests.hint ⟨[], [], "Twice", []⟩ none [⟨p, target "put" []⟩]

/-- The check file of `twice`: the rows of `put`, the L2 rows, `decompiles_l2`, `refines_l2p` and `above_l2p`. -/
def twiceFile : Except GenError String := do
  let g := (← twiceUpper).generated
  let thms ← (g.obligations.filter (twoRow ·.id.name)).mapM fun o => do
    let d ← match o.origin, g.det.find? (·.1 == o.id) with
      | .block _, _ => pure "by intros; first | lift_block_split | lift_block"
      | _, some (_, d) => pure d
      | _, none => throw (.shape 0 s!"no det text of {o.id.name}")
    pure (Skel.theoremText (Skel.Driver.answerName o) o.statement d)
  pure ("\n".intercalate (GenUpperCallTests.toyImports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ "\nnamespace TwiceCheck\n\n" ++
    g.modelText ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend TwiceCheck\n\n#print axioms TwiceCheck.decompiles_l2\n#print axioms TwiceCheck.refines_l2p\n" ++
    "#print axioms TwiceCheck.above_l2p\n")

def pureTwice : List (String × Bool) :=
  [ ("twice (put called from two blocks at one depth) generates, and its decompiles_l2 text has no fail",
      match gen "twice" with
      | .ok g => let d := detOf g; d != "" && !has d "fail"
      | .error _ => false),
    ("twice has an upper chain with the texts of refines_l2p and above_l2p",
      match twiceUpper with
      | .ok u => !u.noText.any fun (i, _) => i.name == "refines_l2p" || i.name == "above_l2p"
      | .error _ => false),
    ("negative: twoDepth (put called at two depths) is GenError.callee .Lcm.put",
      match gen "twoDepth" with
      | .error (.callee ".Lcm.put") => true
      | _ => false) ]

def twiceChecks : IO (List (String × Bool × String)) := do
  match twiceFile with
  | .ok text =>
    let ok ← runFile "twice" "TwiceCheck.above_l2p" text
    pure [("twice: Lean accepts the rows of put, the L2 rows, decompiles_l2, refines_l2p and above_l2p with the standard axioms",
      accepted ok, s!"{repr ok}")]
  | .error e => pure [("the check file of twice", false, s!"{repr e}")]

/-! ## CallLoop (level 2) -/

def l2code : Executable := Lift.Level2z.Code.code

def l2src : BlockSource := .derived Skel.Gen.Derived.level2z

def short (l : String) : String := (l.splitOn ".").getLastD l

/-- The callees as `calleesFrom` gives them; the derived parts of level2z are keyed by the short name of the label. -/
def calleesL : Nat → String → Except GenError (List Callee)
  | 0, _ => pure []
  | fuel + 1, entry => do
    let bs ← blocksFrom l2code l2src (short entry)
    let called := (bs.flatMap fun b => match b.term with
      | .exit (.call f _) => [f] | _ => []).eraseDups
    called.mapM fun f => do
      let sub ← calleesL fuel f
      let cbs ← blocksFrom l2code l2src (short f)
      let ff ← frameFacts (sub.map fun c => (c.name, c.room)) cbs
      pure ⟨f, short f, (modelVars cbs sub ff).inputs, s!"Lift.Level2z.{short f}PC", ff.room, (modelVars cbs sub ff).mem, stackArgCount ff cbs, some (heapWritesOf cbs sub)⟩

def l2target (fn : String) (cs : List Callee) : Target :=
  { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
    entryPC := s!"Lift.Level2z.{fn}PC", imports := [], callees := cs }

def l2gen (fn : String) : Except GenError Generated := do
  generate (l2target fn (← calleesL 6 fn)) Hints.none .storeChain l2code l2src fn

def l2imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMem", "Lift.Tactic.FrameMemLemmas", "Lift.Sem.CallMem", "Lift.Level2z.L1", "Lift.Spike.Sites",
    "Lift.Tactic.Block", "Lift.Tactic.Compose", "Lift.Spike.Sites.Stack"]


/-- The model texts of the callees of `fn`, the deepest first, each in its namespace (a callee once). -/
partial def calleeModels (fn : String) (done : List String) : Except GenError (String × List String) := do
  let cs ← calleesL 6 fn
  cs.foldlM (init := ("", done)) fun (acc, d) c => do
    if d.contains c.model then return (acc, d)
    let (sub, d') ← calleeModels c.model d
    let g ← l2gen c.model
    pure (acc ++ sub ++ s!"namespace {c.model}\n\n{g.modelText}\nend {c.model}\n\n", d' ++ [c.model])

/-- The check file of `decompiles_l2` of `fn`: the block rows and the `decompiles_l2` of each callee are hypotheses. -/
def l2File (fn : String) (g : Generated) : Except GenError String := do
  let cs ← calleesL 6 fn
  let det := cs.foldl (fun d c => replaceAll d s!"{c.model}.decompiles_l2" s!"hc_{c.model}") (detOf g)
  let rows := (g.obligations.filter (·.origin matches .block _)).filterMap fun o =>
    match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  let calleeHyps := cs.map fun c => s!"(hc_{c.model} : Decompiles Lift.Level2z.L1.step {c.model}.l2)"
  pure ("\n".intercalate (l2imports.map ("import " ++ ·)) ++ "\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Level2z\n\n" ++
    (← calleeModels fn []).1 ++ s!"namespace MultiCallL2.{fn}\n\n{g.modelText}\n" ++
    detTheorem "decompiles_l2" (" ".intercalate (rows ++ calleeHyps)) "Decompiles Lift.Level2z.L1.step l2" det ++ "\n\n" ++
    s!"end MultiCallL2.{fn}\n\n#print axioms MultiCallL2.{fn}.decompiles_l2\n")

def pureCallLoop : List (String × Bool) :=
  [ ("CallLoop generates (callees l2zWrap and l2zPtrStore)", (l2gen "l2zCallLoop").toOption.isSome),
    ("CallLoop: decompiles_l2 has a generated proof for its callees with stack rooms",
      match l2gen "l2zCallLoop" with
      | .ok g => let d := detOf g; d != "" && !has d "fail"
      | .error _ => false) ]

/-- CallLoop in Lean: its generated proof uses the block rows and callee theorems as hypotheses. -/
def callLoopChecks : IO (List (String × Bool × String)) := do
  match l2gen "l2zCallLoop" with
  | .error _ => pure [("CallLoop generates (Lean check)", false, "")]
  | .ok g =>
    match l2File "l2zCallLoop" g with
    | .error _ => pure [("CallLoop: the check file", false, "")]
    | .ok text =>
      let o ← runFile "callloop" "MultiCallL2.l2zCallLoop.decompiles_l2" text
      pure [("CallLoop: Lean accepts the generated decompiles_l2 proof with its block and callee rows as hypotheses",
        accepted o, s!"{repr o}")]

/-- A caller that discards the memory returned by a callee cannot use the generated proof. -/
def causeChecks : IO (List (String × Bool × String)) := do
  match l2gen "l2zCallLoop" with
  | .error _ => pure [("CallLoop memory mutation: generation", false, "")]
  | .ok g =>
    let stale := replaceAll g.modelText "mem := r.2" "mem := m1"
    match l2File "l2zCallLoop" { g with modelText := stale } with
    | .error e => pure [("CallLoop memory mutation: check file", false, s!"{repr e}")]
    | .ok text =>
      let o ← runFile "callloop-stale-memory" "MultiCallL2.l2zCallLoop.decompiles_l2" text
      pure [("negative: CallLoop that discards callee memory is rejected",
        stale != g.modelText && failed o, s!"{repr o}")]

/-- Mapping facts use the production store lemma. A lost input word violates the predicate. -/
def mappedChecks : IO (List (String × Bool × String)) := do
  let text := "module\npublic import Lift.Sem.SysV\npublic import Lift.Sem.MappedMemory\npublic import Kraken.Mem\nimport all Kraken.Mem\n\n@[expose] public section\n\nopen Lift.P2.Total Lift.Sem\nnamespace MappedCheck\n" ++
    "theorem keeps (m : DataMem) (a : BitVec 64) (n : Nat) (v : Int) : SysV.MappedMemory m (Mem.storeInt m a n v) := SysV.MappedMemory.storeInt m a n v\n" ++
    "theorem zero (m : DataMem) (a : BitVec 64) (v : Int) : SysV.MappedMemory m (Mem.storeInt m a 0 v) := SysV.MappedMemory.storeInt m a 0 v\n" ++
    "theorem lost : ¬ SysV.MappedMemory (Mem.storeInt ({} : DataMem) 0 8 7) ({} : DataMem) := by\n" ++
    "  intro h\n  have hm : Mem.loadInt (Mem.storeInt ({} : DataMem) 0 8 7) 0 8 ≠ none := by simp [Mem.loadInt_storeInt_64]\n" ++
    "  have hn := h 0 8 hm\n  have he : Mem.loadInt ({} : DataMem) (0 : BitVec 64) 8 = none := by simp [Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]\n  exact hn he\n" ++
    "end MappedCheck\n#print axioms MappedCheck.keeps\n#print axioms MappedCheck.zero\n#print axioms MappedCheck.lost\n"
  let o ← runFile "mapped-memory" "MappedCheck.lost" text
  pure [("memory mapping: stores keep input words, including width zero; lost words are rejected", accepted o, s!"{repr o}")]

/-! ## The shuffler functions that stopped at the second callee -/

def six : List String := [".Lshuffler.Emission.isAvailable", ".Lshuffler.Emission.produce", ".Lshuffler.Emission.removeSurplus",
  ".Lshuffler.MappingBuilder.mapWildcardSlotCopies", ".Lshuffler.MappingBuilder.mapClosestCopies", ".Lshuffler.Planner.classify"]

def pureShuffler : List (String × Bool) :=
  let u := Skel.Full.shufflerUnit (fun _ => "")
  six.map fun l =>
    (s!"{l} generates (no stop at a second callee)",
      match u.fns.find? (·.entry == l) with
      | some f => (Skel.Report.Level3.generateOwn u f).toOption.isSome
      | none => false)

/-- The callee models used by a shuffler proof, in dependency order. -/
partial def shufflerModels (u : Skel.Report.Level3.PUnit) (f : Skel.Report.Level3.PFn) (done : List String) :
    Except GenError (String × List String) := do
  (Skel.Report.Level3.calleesOf u f).foldlM (init := ("", done)) fun (acc, d) c => do
    if d.contains c.model then return (acc, d)
    let some cf := u.fnOfLabel c.name | throw (.callee c.name)
    let (sub, d') ← shufflerModels u cf d
    let g ← Skel.Report.Level3.generateOwn u cf
    pure (acc ++ sub ++ s!"namespace {c.model}\n\n{g.modelText}\nend {c.model}\n\n", d' ++ [c.model])

/-- The actual generated proof, with its direct block and callee rows as hypotheses. -/
def shufflerFile (u : Skel.Report.Level3.PUnit) (f : Skel.Report.Level3.PFn) : Except GenError String := do
  let g ← Skel.Report.Level3.generateOwn u f
  let cs := Skel.Report.Level3.calleesOf u f
  let det := cs.foldl (fun d c => replaceAll d s!"{c.model}.decompiles_l2" s!"hc_{c.model}") (detOf g)
  let rows := g.obligations.filterMap fun o => match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  let calleeHyps := cs.map fun c => s!"(hc_{c.model} : Decompiles Lift.Shuffler.L1.step {c.model}.l2)"
  pure ("\n".intercalate ((Skel.Report.Level3.l2Imports u).map ("import " ++ ·)) ++
    "\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Shuffler\n\nnamespace MultiCallShuffler\n\n" ++
    (← shufflerModels u f []).1 ++ s!"namespace {f.short}\n\n{g.modelText}\n" ++
    detTheorem "decompiles_l2" (" ".intercalate (rows ++ calleeHyps)) "Decompiles Lift.Shuffler.L1.step l2" det ++
    s!"\nend {f.short}\nend MultiCallShuffler\n#print axioms MultiCallShuffler.{f.short}.decompiles_l2\n")

/-- Stack-room callees, entry argument copies, equality branches, and dead partial writes after calls. -/
def shufflerChecks : IO (List (String × Bool × String)) := do
  let u := Skel.Full.shufflerUnit (fun _ => "")
  ["produce", "mapWildcardSlotCopies", "mapClosestCopies", "buildBottomUp"].mapM fun suffix => do
    let some f := u.fns.find? (fun f => f.entry.endsWith ("." ++ suffix))
      | pure (s!"shuffler {suffix}: function exists", false, "")
    match shufflerFile u f with
    | .error e => pure (s!"shuffler {suffix}: generation", false, s!"{repr e}")
    | .ok text =>
      let o ← runFile s!"shuffler-{suffix}" s!"MultiCallShuffler.{f.short}.decompiles_l2" text
      pure (s!"shuffler {suffix}: Lean accepts the generated proof with its block and callee rows as hypotheses",
        accepted o, s!"{repr o}")

/-- Model-only modules of all callees in dependency order. The flag removes the production interface to test the boundary. -/
partial def interfaceModules (u : Skel.Report.Level3.PUnit) (f : Skel.Report.Level3.PFn)
    (withInterface : Bool) (done : List String) : Except GenError (String × List String) := do
  (Skel.Report.Level3.calleesOf u f).foldlM (init := ("", done)) fun (acc, d) c => do
    if d.contains c.model then return (acc, d)
    let some cf := u.fnOfLabel c.name | throw (.callee c.name)
    let (sub, d') ← interfaceModules u cf withInterface d
    let g ← Skel.Report.Level3.generateOwn u cf
    let text ← if withInterface then
        Skel.Full.interfaceText (Skel.Report.Level3.targetOf u cf) u.code (.derived u.derived) cf.entry
      else pure ""
    let h : Header := ⟨[], s!"NestedInterfaces.{c.model}",
      ["Lift.P2.Total", "Lift.Sem", "Lift.Sem.Bridge", "Lift.Shuffler", "Lift.Spike"]⟩
    pure (acc ++ sub ++ Skel.Full.moduleText h g [] text, d' ++ [c.model])

/-- The actual callee model text and each row type. No row theorem is supplied as a fact. -/
def nestedInterfaceFile (withInterface : Bool) : Except GenError String := do
  let u := Skel.Full.shufflerUnit (fun _ => "")
  let some f := u.fnOfLabel ".Lshuffler.Planner.classify" | throw (.callee ".Lshuffler.Planner.classify")
  let t := Skel.Report.Level3.targetOf u f
  let bs ← blocksFrom u.code (.derived u.derived) f.entry
  let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨f.entry, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩
  let mods := t.callees.map fun c => (c.name, s!"NestedInterfaces.{c.model}")
  let crs ← calleeRowsOf t s .storeChain u.code (.derived u.derived) u.codeName
    (Skel.Full.fullCalleeUnits u f) mods
  let rows := crs.flatMap fun c => c.rows.map fun o =>
    let ns := ".".intercalate (o.id.name.splitOn ".").dropLast
    s!"namespace {ns}\nexample (_h : {o.statement}) : True := True.intro\nend {ns}\n"
  let imports := Skel.Report.Level3.l2Imports u ++ ["Lift.Sem.Bridge", "Lift.Sem.CallArm"]
  pure ("\n".intercalate (imports.map ("import " ++ ·)) ++ "\n" ++
    (← interfaceModules u f withInterface []).1 ++
    "\nnamespace NestedInterfaces.caller\nopen Lift.P2.Total Lift.Sem Lift.Sem.Bridge Lift.Shuffler Lift.Spike\n" ++
    "\n\n".intercalate (crs.map (·.text)) ++ "\n" ++ String.join rows ++
    "theorem contextTypes : True := True.intro\nend NestedInterfaces.caller\n" ++
    "#print axioms NestedInterfaces.caller.contextTypes\n")

def nestedInterfaceChecks : IO (List (String × Bool × String)) := do
  match nestedInterfaceFile true, nestedInterfaceFile false with
  | .ok good, .ok bad =>
    let pos ← runFile "nested-interfaces" "NestedInterfaces.caller.contextTypes" good
    let neg ← runFile "nested-no-interfaces" "NestedInterfaces.caller.contextTypes" bad
    pure [("nested callee model definitions and row types elaborate with the production module interfaces", accepted pos, reprStr pos),
      ("negative: nested callee row types fail without module interfaces", failed neg, reprStr neg)]
  | .error e, _ | _, .error e => pure [("nested callee interfaces generate", false, reprStr e)]

/-- The non-module entry used by discovery and the pilot, with all production callee row types. -/
def nestedInlineFile (withDescendants : Bool) : Except GenError String := do
  let u := Skel.Full.shufflerUnit (fun _ => "")
  let some f := u.fnOfLabel ".Lshuffler.Planner.classify" | throw (.callee ".Lshuffler.Planner.classify")
  let t := Skel.Report.Level3.targetOf u f
  let bs ← blocksFrom u.code (.derived u.derived) f.entry
  let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨f.entry, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩
  let units := Skel.Report.Level3.calleeUnits u f
  let units := if withDescendants then units else units.filter fun c => t.callees.any (·.name == c.callee.name)
  let crs ← calleeRowsOf t s .storeChain u.code (.derived u.derived) u.codeName units
  let rows := crs.flatMap fun c => c.rows.map fun o =>
    let ns := ".".intercalate (o.id.name.splitOn ".").dropLast
    s!"namespace {ns}\nexample (_h : {o.statement}) : True := True.intro\nend {ns}\n"
  let imports := Skel.Report.Level3.l2Imports u ++ ["Lift.Sem.Bridge", "Lift.Sem.CallArm"]
  pure ("\n".intercalate (imports.map ("import " ++ ·)) ++
    "\nnamespace NestedInline\nopen Lift.P2.Total Lift.Sem Lift.Sem.Bridge Lift.Shuffler Lift.Spike\n" ++
    "\n\n".intercalate (crs.map (·.text)) ++ "\n" ++ String.join rows ++
    "theorem contextTypes : True := True.intro\nend NestedInline\n#print axioms NestedInline.contextTypes\n")

def nestedInlineChecks : IO (List (String × Bool × String)) := do
  let missing := match nestedInlineFile false with
    | .error (.unsupported _ why) => has why "descendant callee .Lshuffler.Planner.isRetained"
    | _ => false
  let neg := ("negative: missing descendant metadata gives its callee name", missing, "")
  match nestedInlineFile true with
  | .error e => pure [("non-module nested callee models generate", false, reprStr e), neg]
  | .ok text =>
    let pos ← runFile "nested-inline" "NestedInline.contextTypes" text
    pure [("non-module nested callee model definitions and row types elaborate", accepted pos, reprStr pos), neg]

/-- A low-byte write after a call keeps unknown high bits; a full literal write does not. -/
def pureFlow : List (String × Bool) :=
  let bs : List Block :=
    [⟨⟨"entry", by decide⟩, 0, [], [], .exit (.call "callee" 1), []⟩,
     ⟨⟨"partialWrite", by decide⟩, 1, [],
       [(.rcx, .replaceLow .b8 (.reg .rcx) (.lit 7)), (.rdx, .lit 8), (.rsi, .reg .rcx)], .exit (.goto 2), []⟩,
     ⟨⟨"done", by decide⟩, 2, [], [], .exit .ret, []⟩]
  let s : Summary := ⟨"flow", bs, ⟨[.rcx, .rdx], [.rcx, .rdx, .rsi], false⟩, ⟨[], 0⟩, some false⟩
  let fact r := ((flows s).lookup 2).bind (fun f => f.regs.lookup r) |>.map (·.x)
  [("flow: a partial write does not restore a caller-saved register fact", fact .rcx == some false),
   ("flow: a full literal write restores a register fact", fact .rdx == some true),
   ("flow: a copy of an unknown register does not create a register fact", fact .rsi == some false)]


/-- A use of the unknown caller-saved bits after a partial write. -/
inductive LiveReadUse where
  | result | branch | store | loadAddress | keptFlag | calleeArg
  deriving DecidableEq

/-- The generated proof text of the existing post-call fixture. -/
def liveReadTextOf (s : Summary) : Except GenError String := do
  let t := GenL2CallBlkTests.target
  let fr ← frameText .storeChain (t.callees.map fun c => (c.name, c.room)) s true
  pure (decompilesProof t s fr)

def liveReadRefused (s : Summary) (name : String) : Bool :=
  match liveReadTextOf s with
  | .error _ => false
  | .ok text => (text.splitOn
      s!"{name} =>\n    fail \"decompiles_l2: the case of this block is not generated: a read of a register with no fact after a call").length > 1

/-- The partial write stays fixed. Each variant adds a use of the unknown bits. -/
def liveReadSummary (use : LiveReadUse) : Except GenError Summary := do
  let s ← GenL2CallBlkTests.summaryAfter
    [(.rcx, .replaceLow .b8 (.reg .rcx) (.lit 7))]
  let bs := s.blocks.map fun b =>
    if b.offset == 9 && use == .result then
      { b with regs := b.regs.map fun (r, v) => (r, if r == .rax then .reg .rcx else v) }
    else if b.offset == 5 then
      match use with
      | .result => b
      | .branch => { b with term := .branch (.eq (.reg .rcx) (.lit 7)) (.goto 9) (.goto 9) }
      | .store => { b with accesses := [.store 0 (.reg .rbx) .W64 (.reg .rcx)] }
      | .loadAddress => { b with accesses := [.load 0 (.reg .rcx) .W64] }
      | .keptFlag => { b with flags := [(.zf, .eq (.reg .rcx) (.lit 7))] }
      | .calleeArg =>
        { b with
          accesses := [.store 0 (GenUpperRoomTests.below 8) .W64 (.retAddr 9)]
          regs := b.regs ++ [(.rdi, .reg .rcx), (.rsp, .sub (.reg .rsp) (.lit 8))]
          term := .exit (.call "F" 9) }
    else b
  GenUpperCallTests.synthWith "After" GenL2CallBlkTests.target.callees bs

def liveReadChecks : Except GenError (List (String × Bool)) := do
  let bad ← GenL2CallBlkTests.summaryBad
  let checks := [("live rcx-to-rax write is refused", liveReadRefused bad "o5"),
    ("unknown return is refused", liveReadRefused bad "o9")]
  let uses : List (LiveReadUse × String) :=
    [(.result, "live partial output"), (.branch, "branch"), (.store, "store"),
     (.loadAddress, "load address"), (.keptFlag, "kept flag"), (.calleeArg, "callee argument")]
  let checks ← uses.foldlM (init := checks) fun acc (use, name) => do
    let s ← liveReadSummary use
    pure (acc ++ [(s!"negative: {name} reads remain required", liveReadRefused s "o5")])
  let dead ← GenL2CallBlkTests.summaryAfter
    [(.rcx, .replaceLow .b8 (.reg .rcx) (.lit 7))]
  let text ← liveReadTextOf dead
  pure (checks ++ [("dead partial output needs no missing fact", (text.splitOn "fail").length == 1)])

def pureLiveReads : List (String × Bool) :=
  match liveReadChecks with
  | .ok checks => checks
  | .error _ => [("live-read control fixtures generate", false)]

def pureChecks : List (String × Bool) :=
  pureToy ++ pureUpper ++ pureModule ++ pureTwice ++ pureCallLoop ++ pureShuffler ++ pureFlow ++ pureLiveReads

/-- Gives the number of failed checks. The suite runs when `only` is none or `multicallee`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "multicallee" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  multicallee: {name}"
  for (name, ok, msg) in (← toyChecks) ++ (← upperChecks) ++ (← moduleChecks) ++ (← twiceChecks) ++ (← callLoopChecks) ++
      (← causeChecks) ++ (← mappedChecks) ++ (← shufflerChecks) ++ (← nestedInterfaceChecks) ++ (← nestedInlineChecks) do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  multicallee: {name}\n{msg}"
  return n

end GenMultiCalleeTests
