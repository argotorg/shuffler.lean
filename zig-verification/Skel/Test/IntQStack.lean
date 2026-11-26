import Skel.IntQ
import Skel.IntQ.Refute
import Skel.IntQ.Replay

/-! ABI checks for proposed contracts with eight integer arguments. -/

namespace IntQStackTests

open Skel Skel.IntQ Lift.Trusted Lift.P2.Total

def has (text part : String) : Bool := (text.splitOn part).length > 1

def entryChecks : List (String × Bool) :=
  let fn := Lift.Shuffler.Internal.Fns.workspaceSize
  let c : Refute.Case :=
    { pre := true, args := List.replicate 6 ⟨.W64, 0⟩, objs := [], junk := 0,
      stack := some (7, 8), expect := some (⟨.W64, 357672⟩, []) }
  let obj (value : BitVec 64) (write : Bool) : Object :=
    ⟨Lift.Shuffler.Test.Run.rsp0 + 8, [⟨.W64, value⟩], write⟩
  let m := (Refute.startOf fn c).data.dmem
  let changed := m.storeBytes (Lift.Shuffler.Test.Run.rsp0 + 8) [99]
  let writable := { c with objs := [obj 7 true] }
  [ ("eight arguments install both stack words", (Refute.stackObject c).any (Refute.hasObj m)),
    ("stack arguments admit an entry and run the production interpreter",
      (Refute.admissionIssue fn c).isNone && (Refute.checkCase fn 1000 c).isNone),
    ("equal read-only aliases of stack arguments are admitted",
      (Refute.admissionIssue fn { c with objs := [obj 7 false] }).isNone),
    ("equal writable aliases of stack arguments are admitted",
      (Refute.admissionIssue fn writable).isNone),
    ("negative: conflicting stack and object bytes are rejected",
      (Refute.admissionIssue fn { c with objs := [obj 9 false] }).isSome &&
      (Refute.admissionIssue fn { c with objs := [obj 9 true] }).isSome),
    ("negative: invalid stack aliases retain no model result",
      (Refute.withExpected fn { c with objs := [obj 9 false], expect := none }
        (fun _ => some (⟨.W64, 1⟩, []))).expect.isNone),
    ("negative: a stack argument outside writable objects is framed",
      (Refute.stackFrameIssue c changed).isSome),
    ("the stack frame allows writes inside writable objects",
      (Refute.stackFrameIssue writable changed).isNone),
    ("negative: the other stack word remains framed",
      (Refute.stackFrameIssue writable
        (m.storeBytes (Lift.Shuffler.Test.Run.rsp0 + 16) [99])).isSome),
    ("negative: eight register fields are still rejected",
      (Refute.admissionIssue fn { c with args := List.replicate 8 ⟨.W64, 0⟩ }).isSome),
    ("register calls have no stack argument object",
      (Refute.stackObject { c with stack := none }).isNone),
    ("unsupported ABI signatures are refused",
      supportedArgs [.W8, .W64] &&
      supportedArgs (List.replicate 8 .W64) &&
      !supportedArgs (List.replicate 7 .W64) &&
      !supportedArgs (List.replicate 9 .W64) &&
      !supportedArgs (List.replicate 6 .W64 ++ [.W8, .W64])) ]

def eightFields : String :=
  "[⟨.W64, 1⟩, ⟨.W64, 2⟩, ⟨.W64, 3⟩, ⟨.W8, 1⟩, ⟨.W64, 5⟩, ⟨.W64, 6⟩, ⟨.W64, 7⟩, ⟨.W64, 8⟩]"

def templateChecks : IO (List (String × Bool)) := do
  let inputs ← promptInputs
  let some (_, .ok input) := inputs.find? (fun (p : Target × Except String PromptIn) =>
      stmtName p.1.label == "PlannerRun")
    | throw (IO.userError "missing planner context")
  let c := input.ctx
  let h : Holes :=
    { room := 320, contract := "True", args := eightFields,
      objects := "[]", written := "[]", result := "⟨.W16, 0⟩" }
  let dir ← tempDir "intqstack"
  let (infos, errors) ← runLean dir "EightShape.lean" (shapeText c h)
  for error in errors do IO.eprintln s!"Call8 shape: {error}"
  let shapes := infos.filterMap fun t => (Lean.Json.parse t >>= Skel.Gen.Shape.parse).toOption
  let shapeOK := shapes.any fun sh =>
    sh.args.length == 6 && sh.call.stack.length == 2 && sh.call.name == "call8B" && sh.call.bytePermits
  let (_, shortErrors) ← runLean dir "ShortShape.lean"
    (shapeText c { h with args := eightFields.replace ", ⟨.W64, 8⟩" "" })
  let (_, widthErrors) ← runLean dir "WidthShape.lean"
    (shapeText c { h with args := eightFields.replace "⟨.W64, 7⟩" "⟨.W32, 7⟩" })
  let seven := { c with target := { c.target with sym :=
    { c.target.sym with args := List.replicate 7 .W64 } } }
  let reply := s!"=== ROOM\n320\n=== CONTRACT\nTrue\n=== ARGS\n{eightFields}\n=== OBJECTS\n[]\n=== WRITTEN\n[]\n=== RESULT\n⟨.W16, 0⟩\n=== END\n"
  let rejected ← check dir seven reply 0 1
  let some (_, .ok ws) := inputs.find? (fun (p : Target × Except String PromptIn) =>
      stmtName p.1.label == "WorkspaceSize")
    | throw (IO.userError "missing workspace context")
  let badRegisters := reply.replace "320" "0" |>.replace eightFields "[⟨.W64, 1⟩]"
  let badCount ← check dir ws.ctx badRegisters 0 1
  let anonymous := { c with target := { c.target with label := ".Lshuffler.Fixture.eight" } }
  return
    [ ("offline replay reproduces the complete old template before changing call permissions",
        (Replay.renderExisting c (Replay.exactTemplate c h) [reply]).toOption == some (fill c h "proposer")),
      ("offline replay preserves an already current template",
        (Replay.renderExisting c (fill c h "proposer") [reply]).toOption == some (fill c h "proposer")),
      ("negative: offline replay refuses an edited source contract",
        (Replay.renderExisting c (Replay.exactTemplate c { h with contract := "False" }) [reply]).toOption.isNone),
      ("negative: offline replay refuses edited output objects",
        (Replay.renderExisting c (Replay.exactTemplate c { h with written := "objects" }) [reply]).toOption.isNone),
      ("negative: offline replay refuses an incomplete saved reply",
        (Replay.renderExisting c (Replay.exactTemplate c h) ["=== CONTRACT\nTrue\n"]).toOption.isNone),
      ("eight-argument templates supply byte-range permissions with Call8B",
        has (fill c h "test") "fn.Call8B" && errors.isEmpty && shapeOK),
      ("the refuter supplies six registers and two stack words",
        has (refuteText c h 0 1) "stack := some" && has (refuteText c h 0 1) ").take 6"),
      ("negative: a missing ABI field fails elaboration", !shortErrors.isEmpty),
      ("negative: a stack word with the wrong width fails elaboration", !widthErrors.isEmpty),
      ("negative: unsupported ABI signatures fail before machine sampling",
        rejected.failure.any fun (stage, why) => stage == .shape && has why "unsupported ABI"),
      ("negative: register argument count must match the signature",
        badCount.failure.any fun (stage, why) => stage == .shape && has why "ABI signature"),
      ("Call8B selection uses the signature independently of the function name",
        has (fill anonymous h "test") "fn.Call8B") ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "intqstack" then return 0
  let checks := entryChecks ++ (← templateChecks)
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL  intqstack: {name}"
  return failed.length

end IntQStackTests
