import Skel.TempDir
import Skel.Gen.Derived.Pilot
import Skel.Gen.Generate
import Skel.Io
import Skel.Test.GenVars
import Lift.Level3.Code
import Skel.Test.CallMem.Code

/-! The tests of a callee with memory in its result (suite `callmem`, task PIL-CALL): `lake exe skel-test --only callmem`.

The real pair is the pilot `mapInPlace`, which calls `map`; `map` stores through a register, so its result has memory.

Pure checks:
* `calleesFrom` finds the callee of `mapInPlace` from the call target: `map`, with the inputs of its model (`rax`, `rdx`,
  `rsi`, `rdi`), room 0 and memory.
* Negative: a call target that is not a function of the unit is `GenError.callee`; a callee with memory that two blocks
  call is `GenError.callee` (`checkBlocks`).
* `generate` of `mapInPlace` is `ok`; its model passes the memory and `rsp` of the call to `map`, goes on with the memory of
  the result, and uses `map` restricted to the results that keep the caller's 40 bytes (`Kept`).

IO checks (Lean): the check file has the model of `map` with its block rows as hypotheses of its `decompiles_l2`, the model
of `mapInPlace`, and `Decompiles` of the restricted callee model. Lean must accept it with the standard axioms. Mutation:
the model of `mapInPlace` with the callee result type `UInt64` and `rax := r` (the text before PIL-CALL) is rejected.

The check files import the modules of `imports`; build them first. -/

namespace GenCallMemTests

open Skel Skel.Gen
open GenVarsTests (mkIdent)

def code : Executable := Lift.Level3.Code.code

def src : BlockSource := .derived Skel.Gen.Derived.pilot

def mapLabel : String := ".Lshuffler.MappingBuilder.map"

def mapInPlaceLabel : String := ".Lshuffler.MappingBuilder.mapInPlace"

/-- The functions of the unit that the tests name: the PC constant and the model namespace of each label. -/
def names : String → Option (String × String)
  | ".Lshuffler.MappingBuilder.map" => some ("Lift.Level3.mappingMapPC", "mappingMap")
  | _ => none

def targetOf (pc : String) (cs : List Callee) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := s!"Lift.Level3.{pc}", imports := [], callees := cs }

def calleesOfMapInPlace : Except GenError (List Callee) := calleesFrom code src names 3 mapInPlaceLabel

def genMapInPlace : Except GenError Generated := do
  generate (targetOf "mapInPlacePC" (← calleesOfMapInPlace)) Hints.none .storeChain code src mapInPlaceLabel

def genMap : Except GenError Generated := generate (targetOf "mappingMapPC" []) Hints.none .storeChain code src mapLabel

def has (s part : String) : Bool := (s.splitOn part).length > 1

/-- Two blocks that call the callee `f` with memory. -/
def twoCalls : List Block :=
  [ ⟨mkIdent "entry", 0, [.store 0 (.sub (.reg .rsp) (.lit 8)) .W64 (.retAddr 5)], [(.rsp, .sub (.reg .rsp) (.lit 8))],
      .exit (.call "f" 5), []⟩,
    ⟨mkIdent "o5", 5, [.store 0 (.sub (.reg .rsp) (.lit 8)) .W64 (.retAddr 10)], [(.rsp, .sub (.reg .rsp) (.lit 8))],
      .exit (.call "f" 10), []⟩,
    ⟨mkIdent "o10", 10, [.load 0 (.reg .rsp) .W64], [(.rsp, .add (.reg .rsp) (.lit 8))], .exit .ret, []⟩ ]

def memF : Callee := ⟨"f", "F", [.rdi], "fPC", 0, true, 0, none⟩

def pureChecks : List (String × Bool) :=
  [ ("calleesFrom mapInPlace: map, inputs rax rdx rsi rdi, room 0, memory",
      match calleesOfMapInPlace with
      | .ok [c] => c.name == mapLabel && c.model == "mappingMap" && c.inputs == [.rax, .rdx, .rsi, .rdi] &&
          c.entryPC == "Lift.Level3.mappingMapPC" && c.room == 0 && c.mem
      | _ => false),
    ("calleesFrom: a call target that is not a function of the unit is GenError.callee",
      match calleesFrom code src (fun _ => none) 3 mapInPlaceLabel with
      | .error (.callee l) => l == mapLabel
      | _ => false),
    ("checkBlocks and checkMemCalls: a callee with memory that two blocks call at one depth passes (MULTI-CALLEE2)",
      match (do checkBlocks (targetOf "pc" [memF]) twoCalls
                checkMemCalls (targetOf "pc" [memF]) twoCalls (← frameFacts [("f", 0)] twoCalls) : Except GenError Unit) with
      | .ok () => true
      | _ => false),
    ("checkBlocks: the same two calls of a callee with no memory pass",
      match checkBlocks (targetOf "pc" [{ memF with mem := false }]) twoCalls with
      | .ok () => true
      | _ => false),
    ("generate mapInPlace: the model passes memory and rsp to map and goes on with the memory of the result",
      match genMapInPlace with
      | .ok g => has g.modelText "(fun _ => mappingMap.In2) (fun _ => UInt64 × DataMem)" &&
          has g.modelText ".call () ⟨x.input.policy, m1, x.input.sp - 24 - 8, x.rax, x.r14, x.r14, x.rbx⟩" &&
          has g.modelText "mem := r.2, rax := r.1" &&
          has g.modelText "(mappingMap.l2.restrict fun y r => Kept y.sp 40 y.mem r.2).returns"
      | .error _ => false) ]

def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMemLemmas", "Lift.Sem.CallMem", "Lift.Level3.L1", "Lift.Spike.Sites", "Lift.Tactic.Compose"]

/-- The `det` text of `decompiles_l2` of a generated function. -/
def detOf (g : Generated) : String :=
  ((g.det.find? (·.1.name == "decompiles_l2")).map (·.2)).getD ""

/-- The check file: `map` in its namespace (its block rows as hypotheses of its `decompiles_l2`), the model `model` of
`mapInPlace`, and `Decompiles` of the restricted callee model, from the `decompiles_l2` of `map`. -/
def fileOf (map : Generated) (model : String) : String :=
  let rows := (map.obligations.filter (·.origin matches .block _)).filterMap fun o =>
    match o.origin with
    | .block l => some (l, o.statement)
    | _ => none
  let binders := " ".intercalate (rows.map fun (l, st) => s!"({l} : {st})")
  let args := " ".intercalate (rows.map (·.1))
  "\n".intercalate (imports.map (s!"import " ++ ·)) ++
    "\n\nnamespace CallMem\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Level3\n\nnamespace mappingMap\n\n" ++ map.modelText ++
    "\n" ++ detTheorem "decompiles_l2" binders "Decompiles Lift.Level3.L1.step l2" (detOf map) ++ "\n\nend mappingMap\n\n" ++
    model ++
    s!"\ntheorem callee_decompiles {binders} :\n    Decompiles Lift.Level3.L1.step (mappingMap.l2.restrict fun y r => Kept y.sp 40 y.mem r.2) :=\n" ++
    s!"  (mappingMap.decompiles_l2 {args}).restrict _\n\nend CallMem\n\n#print axioms CallMem.callee_decompiles\n"

/-- Runs Lean on a check file. -/
def runFile (name text : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"callmem-{name}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") "CallMem.callee_decompiles" 300000).1

/-- The model text before PIL-CALL: the callee result `UInt64`, `rax := r`, the memory of the state kept. -/
def oldModel (m : String) : String :=
  ((m.replace "(fun _ => UInt64 × DataMem)" "(fun _ => UInt64)").replace "mem := r.2, rax := r.1" "mem := m1, rax := r")

def ioChecks : IO (List (String × Bool × String)) := do
  match genMap, genMapInPlace with
  | .ok map, .ok g =>
    let standard := ["Classical.choice", "Quot.sound", "propext"]
    let ok ← runFile "ok" (fileOf map g.modelText)
    let okRes := match ok with
      | .accepted axs => axs.all standard.contains
      | _ => false
    let old ← runFile "old" (fileOf map (oldModel g.modelText))
    let oldRes := match old with
      | .failed _ => oldModel g.modelText != g.modelText
      | _ => false
    pure [ ("Lean accepts the models of map and mapInPlace and the restricted callee Decompiles with the standard axioms",
        okRes, s!"{repr ok}"),
      ("mutation: the model with the callee result UInt64 (before PIL-CALL) is rejected", oldRes, s!"{repr old}") ]
  | _, _ => pure [("generate map and mapInPlace", false, "")]

/-! ## The synthetic pair (`Skel/Test/CallMem/Code.lean`)

`put` stores one word; `putCall` calls it and reads the word back; `putBad` passes its `rsp`, so `put` writes the word of
the saved `rbx`: the generator refuses it (`GenError.frame`). The check file has `put` (model, block rows proved by
`lift_block`, `decompiles_l2`) in the namespace `Put`, then `putCall` in the same form. The Lean side of the negative case
(a result that writes a kept byte is not a result of the restricted model) is `Lift/Sem/Test/CallMem.lean`. -/

def synthCode : Executable := Skel.Test.CallMem.Code.code

def synthNames : String → Option (String × String)
  | ".Lcm.put" => some ("putPC", "Put")
  | _ => none

def synthTarget (fn : String) (cs : List Callee) : Target :=
  { step := "Skel.Test.CallMem.L1.step", lo := "putPC", hi := "callMemEndPC", entryPC := s!"{fn}PC", imports := [],
    callees := cs }

def synthGen (fn : String) : Except GenError Generated := do
  let cs ← calleesFrom synthCode .table synthNames 3 fn
  generate (synthTarget fn cs) Hints.none .storeChain synthCode .table fn

def synthImports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Skel.Test.CallMem.L1",
    "Lift.Spike.Sites", "Lift.Tactic.Block", "Lift.Sem.StackRoom", "Lift.Spike.Sites.Stack", "Lift.Tactic.FrameMem",
    "Lift.Sem.CallMem"]

/-- The text of a generated function: its model, its block rows (`lift_block`) and `decompiles_l2` with the text `det`. -/
def partText (g : Generated) (det : String) : String :=
  let rows := g.obligations.filterMap fun o =>
    match o.origin with
    | .block l => some s!"theorem {l} : {o.statement} := by intros; lift_block"
    | _ => none
  g.modelText ++ "\n" ++ "\n\n".intercalate rows ++ "\n\n" ++ detTheorem "decompiles_l2" "" "Decompiles Skel.Test.CallMem.L1.step l2" det ++ "\n"

def synthFile (callee caller : Generated) (callerDet : String) : String :=
  "\n".intercalate (synthImports.map (s!"import " ++ ·)) ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike\n\nnamespace CallMem\n\nnamespace Put\n\n" ++
    partText callee (detOf callee) ++ "\nend Put\n\n" ++ partText caller callerDet ++
    "\nend CallMem\n\n#print axioms CallMem.decompiles_l2\n"

def runSynth (name text : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"callmem-{name}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") "CallMem.decompiles_l2" 300000).1

/-- The `Kept` facts of the proof replaced by the facts of the memory at the call (the proof text with no `Kept.readRam`):
the text that a caller of a callee with no memory has. -/
def dropKept (p : String) : String :=
  match p.splitOn "(Kept.readRam hkept " with
  | [] | [_] => p
  | first :: rest => first ++ String.join (rest.map fun r =>
      -- `(k := n) (by decide) (by simp only [hsp]; bv_omega) (` then the inner proof
      match r.splitOn "bv_omega) (" with
      | _ :: tail => "(" ++ "bv_omega) (".intercalate tail
      | [] => r)

def synthChecks : IO (List (String × Bool × String)) := do
  let badErr := match synthGen "putBad" with
    | .error (.frame 0 "rsp is the value of a register") => true
    | _ => false
  match synthGen "put", synthGen "putCall" with
  | .ok put, .ok call =>
    let standard := ["Classical.choice", "Quot.sound", "propext"]
    let accepted (o : Outcome) := match o with
      | .accepted axs => axs.all standard.contains
      | _ => false
    let failed (o : Outcome) := match o with
      | .failed _ => true
      | _ => false
    let ok ← runSynth "putCall" (synthFile put call (detOf call))
    let mut' := dropKept (detOf call)
    let mutRes ← runSynth "putCall-mut" (synthFile put call mut')
    pure [ ("putCall: Lean accepts put and putCall (rows by lift_block, decompiles_l2) with the standard axioms",
        accepted ok, s!"{repr ok}"),
      ("putCall: the proof has no fail", !(detOf call).contains "fail", ""),
      ("negative: putBad (put writes the word of the saved rbx through rdi := rsp) is the named GenError.frame", badErr, ""),
      ("mutation: the proof of putCall without Kept.readRam is rejected", mut' != detOf call && failed mutRes,
        s!"{repr mutRes}") ]
  | _, _ => pure [("generate put and putCall", false, "")]

/-- Gives the number of failed checks. The suite runs when `only` is none or `callmem`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "callmem" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callmem: {name}"
  for (name, ok, msg) in (← ioChecks) ++ (← synthChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callmem: {name}\n{msg}"
  return failed

end GenCallMemTests
