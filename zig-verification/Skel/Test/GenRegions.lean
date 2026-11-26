import Skel.Test.GenL2Loops
import Skel.Test.GenMultiCallee
import Lift.Sem.Cut

namespace GenRegionsTests

open Skel Skel.Gen Lift.Sem Lift.P2.Total

/-- Two passes with an entry branch and a return before either pass. -/
def flow : Leaf Nat Nat Nat where
  step l s := match l with
    | 0 => if s = 0 then .ok (.ret 7) else .ok (.goto 1 (s + 1))
    | 1 => if s < 3 then .ok (.goto 2 s) else .ok (.goto 3 s)
    | 2 => .ok (.goto 1 (s + 1))
    | 3 => if s < 5 then .ok (.goto 4 s) else .ok (.ret s)
    | 4 => .ok (.goto 3 (s + 1))
    | 5 => .stuck "fault"
    | _ => .noFuel

def heads (l : Nat) : Bool := l == 1 || l == 3

def noRun (f : Empty) : Empty.elim f → Res (Empty.elim f) := f.elim

def runFlow (l s : Nat) : Res (CutExit Nat Nat Nat) :=
  (flow.cut heads).run noRun 20 (.block l) s

def nextIs (run : Res (CutExit Nat Nat Nat)) (l s : Nat) : Bool :=
  match run with | .ok (.next k t) => k == l && t == s | _ => false

def retIs (run : Res (CutExit Nat Nat Nat)) (r : Nat) : Bool :=
  match run with | .ok (.ret v) => v == r | _ => false

abbrev callX : Bool → Type | true => Nat | false => Unit

abbrev callY : Bool → Type | true => Nat | false => Bool

def callFlow : Blocks Nat Nat Nat Bool callX callY where
  step l s := if l = 0 then .ok (.call true s fun n => (1, n + 2)) else .ok (.ret s)

def callRun (f : Bool) : callX f → Res (callY f) :=
  match f with | true => fun n => .ok (n + 1) | false => fun _ => .ok false

/-- The inner pass resets on each outer pass. Its rank includes the outer count. -/
def nested : Leaf Nat (Nat × Nat) Nat where
  step l s := if l = 0 then
      if s.1 = 0 then .ok (.ret 0) else .ok (.goto 1 (s.1, 2))
    else if s.2 = 0 then .ok (.goto 0 (s.1 - 1, 0))
    else .ok (.goto 1 (s.1, s.2 - 1))

def nestedI (l : Nat) (s : Nat × Nat) : Prop :=
  l = 0 ∨ (l = 1 ∧ 0 < s.1 ∧ s.2 ≤ 2)

def nestedRank (l : Nat) (s : Nat × Nat) : Nat :=
  if l = 0 then 4 * s.1 + 3 else 4 * s.1 + s.2

def nestedValid (l n m : Nat) : Bool :=
  match (nested.cut fun _ => true).run noRun 4 (.block l) (n, m) with
  | .ok e => @decide (e.Progress nestedI nestedRank (fun _ _ => 0) l (n, m))
      (by cases e <;> dsimp [CutExit.Progress, nestedI] <;> infer_instance)
  | _ => false

def cutChecks : List (String × Bool) :=
  [ ("nested passes satisfy one combined rank over 100 outer counts",
      (List.range 100).all fun n => nestedValid 0 n 0 &&
        (List.range 3).all fun m => nestedValid 1 (n + 1) m),
    ("entry branch returns before a head", retIs (runFlow 0 0) 7),
    ("entry retains the state at the first head", nextIs (runFlow 0 1) 1 2),
    ("a region executes its source before stopping", nextIs (runFlow 1 2) 1 3),
    ("a pass stops at a later head", nextIs (runFlow 1 3) 3 3),
    ("the later pass stops on its back edge", nextIs (runFlow 3 4) 3 5),
    ("the last pass returns its result", retIs (runFlow 3 5) 5),
    ("faults are retained", match runFlow 5 0 with | .stuck why => why == "fault" | _ => false),
    ("noFuel is retained", match runFlow 6 0 with | .noFuel => true | _ => false),
    ("typed call continuation retains its cut state",
      nextIs ((callFlow.cut fun l => l == 1).run callRun 10 (.block 0) 4) 1 7),
    ("a transition rejects equal ranks",
      !(@decide ((CutExit.next 1 2 : CutExit Nat Nat Nat).Progress (fun _ _ => True)
        (fun _ _ => 0) (fun _ _ => 5) 1 1) (by dsimp [CutExit.Progress]; infer_instance))),
    ("a transition rejects a changed output",
      !(@decide ((CutExit.next 1 2 : CutExit Nat Nat Nat).Progress (fun _ _ => True)
        (fun _ s => 3 - s) (fun _ s => s) 1 1) (by dsimp [CutExit.Progress]; infer_instance))),
    ("a transition rejects a false target invariant",
      !(@decide ((CutExit.next 1 2 : CutExit Nat Nat Nat).Progress (fun _ s => s < 2)
        (fun _ s => 3 - s) (fun _ _ => 5) 1 1) (by dsimp [CutExit.Progress]; infer_instance))) ]

def generationChecks : IO (List (String × Bool × String)) := do
  let hs ← GenL2LoopsTests.hints
  let mut out := []
  for fn in ["l2zTwoLoops", "l2zNest"] do
    let result : Except GenError Upper := do
      let some h := hs.lookup fn | throw (.shape 0 "no hint")
      GenL2LoopsTests.upperOf fn h
    match result with
    | .error e => out := out ++ [(fn, false, (repr e).pretty)]
    | .ok u =>
      let rows := u.generated.obligations
      let region := rows.find? (·.id.name == "regions")
      let refines := rows.find? (·.id.name == "refines_l3")
      let det := (u.generated.det.find? (·.1.name == "refines_l3")).map (·.2)
      out := out ++ [(s!"{fn}: local regions and composition are generated",
        region.any (fun r => r.claim == .loop &&
          (r.statement.splitOn "CutExit.Progress").length == 2) &&
        refines.any (fun r => r.deps.any (·.name == "regions")) &&
        det.any (fun d => (d.splitOn "cut_loop").length == 2) &&
        !(rows.any (·.id.name.startsWith "loop.")), "")]
      match region, refines, det with
      | some region, some refines, some det =>
        let mod := if fn == "l2zNest" then "Lift.Level2z.NestStatement" else "Lift.Level2z.TwoLoopsStatement"
        let hd := GenL2LoopsTests.header fn mod
        match GenL2LoopsTests.refinesFile hd u.generated.modelText region refines det with
        | none => out := out ++ [(s!"{fn}: composition file is generated", false, "")]
        | some text =>
          let o ← GenL2LoopsTests.runFile fn text s!"{hd.namespace_}.refines_l3"
          out := out ++ [(s!"{fn}: kernel accepts composition from the joint certificate",
            GenL2LoopsTests.accepted o, (repr o).pretty)]
          let bad := text.replace "hstart, hresult" "hstart, True.intro"
          let o' ← GenL2LoopsTests.runFile s!"{fn}-wrong-output" bad s!"{hd.namespace_}.refines_l3"
          out := out ++ [(s!"{fn}: composition rejects a missing result relation",
            bad != text && !(o' matches .accepted _), (repr o').pretty)]
      | _, _, _ => pure ()
  let fn := "l2zNest"
  let cr : Except GenError CalleeRows := do
    let s ← GenL2LoopsTests.realSummary fn
    let c : Callee :=
      { name := fn, model := "Nest", inputs := s.vars.inputs,
        entryPC := s!"Lift.Level2z.{fn}PC", room := s.frame.room, mem := s.vars.mem, stackArgs := 0 }
    calleeUpper .storeChain GenL2LoopsTests.code GenL2LoopsTests.src "Lift.Level2z.Code.code"
      ⟨c, GenL2LoopsTests.targetOf fn⟩
  out := out ++ [("a heap-only source keeps both callee interface rows",
    cr.toOption.any (fun r => r.rows.any (·.id.name == "Nest.shape") &&
      r.rows.any (·.id.name == "Nest.refines_l2p")),
    match cr with | .error e => (repr e).pretty | .ok _ => "")]
  let called : Except GenError CalleeRows := do
    let cs ← GenMultiCalleeTests.calleesL 6 "l2zCallLoop"
    let t := GenMultiCalleeTests.l2target "l2zCallLoop" cs
    let (s, _) ← summaryOf t .storeChain GenL2LoopsTests.code GenL2LoopsTests.src "l2zCallLoop"
    let c : Callee :=
      { name := "l2zCallLoop", model := "CallLoop", inputs := s.vars.inputs,
        entryPC := t.entryPC, room := s.frame.room, mem := s.vars.mem,
        stackArgs := 0, heap := some s.heapWrites }
    calleeUpper .storeChain GenL2LoopsTests.code GenL2LoopsTests.src "Lift.Level2z.Code.code" ⟨c, t⟩
  out := out ++ [("a missing deterministic callee proof retains its obligation",
    called.toOption.any (fun r => r.rows.any (·.id.name == "CallLoop.shape") &&
      r.noText.any (·.1.name == "CallLoop.shape") && !r.det.any (·.1.name == "CallLoop.shape")),
    match called with | .error e => (repr e).pretty | .ok _ => "")]
  match cr with
  | .error _ => pure ()
  | .ok r =>
    out := out ++ [("callee interfaces contain no L3 statement definitions",
      (r.text.splitOn "def SimArr").length == 1 && (r.text.splitOn "def l3").length == 1, "")]
    let hd := GenL2LoopsTests.header fn "Lift.Level2z.NestStatement"
    let typedRows := r.rows.zipIdx |>.map fun (o, i) => s!"theorem rowTyped{i} (h : {o.statement}) : True := True.intro"
    let text := "\n".intercalate ((hd.imports ++ ["Lift.Sem.CallArm"]).map fun m => s!"import {m}") ++
      "\nopen " ++ " ".intercalate hd.opens ++ s!"\nnamespace {hd.namespace_}\n" ++ r.text ++
      "\nnamespace Nest\n" ++ "\n".intercalate typedRows ++ "\nend Nest\n" ++
      s!"\ntheorem rowsTyped : True := True.intro\nend {hd.namespace_}\n" ++
      s!"#print axioms {hd.namespace_}.rowsTyped\n"
    let o ← GenL2LoopsTests.runFile "callee-rows-typed" text s!"{hd.namespace_}.rowsTyped"
    out := out ++ [("all retained callee rows have types accepted by Lean", GenL2LoopsTests.accepted o, (repr o).pretty)]
  return out

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genregions" then return 0
  let checks := cutChecks.map (fun (n, b) => (n, b, "")) ++ (← generationChecks)
  let mut failed := 0
  for (name, ok, msg) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genregions: {name}\n{msg}"
  return failed

end GenRegionsTests
