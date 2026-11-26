import Skel.IntQ
import Skel.IntQ.Refute

/-! The tests of the proposer of the internal statements (suite `intq`, task INT-Q): `lake exe skel-test --only intq`, from the
repository root. No paid call: the asker is a fake asker of the stored replies of `tools/shuffler-pilot/intq-replies/` (good)
and `tools/shuffler-pilot/intq-replies-bad/` (wrong).

Checks:
* The targets: the functions of `Fns.fns` with no moved statement; each has a model function, a Zig source and a signature.
* The reply form: a good reply parses; a reply with no `=== END`, with a section missing, with `sorry`, or with a command
  is refused.
* The prompt: the same input gives the same text; a rejected proposal and its error are in the prompt of the retry.
* The dry run: one prompt for each target, with no ask.
* The good replies of workspaceSize and Emission.isSpilled pass the five filters, with the refuter verdict pass.
* Negative: the isSpilled reply with the result encoding swapped is refused by the refuter; the workspaceSize reply with the
  room 8 is refused by `checkRoom`.
* The retry: a wrong reply, then a good one, gives the statement after two asks, and the second prompt has the error.
* The module `Lift/Shuffler/Internal/Proposed/<N>Statement.lean` of each accepted ledger line is the filled template of a
  reply of its store (`asks/<N>.jsonl`) or of its good stored reply, and the ledger has one line for each target.
* INT-Q2: the targets are 22 by the rule (a `Fn`, no moved statement, no trusted statement). The prompt of isAvailable has the
  definition of `FlatShuffler.StackSlot` with its fields, fully qualified, and the namespace and the `open` lines of the
  template; the prompt of permuteAtLowestHeight has the constructors of `Lift.Shuffler.Zig.Exit`; each prompt names the
  `Encode` instances; no prompt names a module of the deny list. The binders of the template are fully qualified
  (isDemanded: `FlatShuffler.StackSlot`), and the template of each target elaborates with neutral holes. Rounds: two wrong
  replies, then a good one, give the statement after 3 asks; 5 wrong replies give "open for the final rung" after 5 asks
  (a sixth reply is not asked); a wrong reply and then no reply is "stopped" after 2 asks. The pool runs the jobs at the
  same time, at most N, and keeps their order. The refute file of the accepted permute reply of INT-Q-RUN elaborates: the
  verdict keeps the count and reason when no sample is in the contract. -/

namespace IntQTests

open Skel Skel.IntQ

def good : System.FilePath := "tools/shuffler-pilot/intq-replies"
def bad : System.FilePath := "tools/shuffler-pilot/intq-replies-bad"
/-- The accepted DeepSeek reply of permute of INT-Q-RUN (`Lift/Shuffler/Internal/Proposed/replies.jsonl`). -/
def run1 : System.FilePath := "tools/shuffler-pilot/intq2-replies"
/-- The first DeepSeek replies of INT-Q2 that the word filter refused (`end` in `Layout.pend`), and the accepted replies of the
planner functions, whose refute verdict was unknown (INT-Q3). -/
def q3 : System.FilePath := "tools/shuffler-pilot/intq3-replies"

def has (t s : String) : Bool := (t.splitOn s).length > 1

def isErr {α ε : Type} (e : Except ε α) : Bool := match e with | .ok _ => false | .error _ => true

def goodText : String :=
  "=== ROOM\n0\n=== CONTRACT\nTrue\n=== ARGS\n[]\n=== OBJECTS\n[]\n=== WRITTEN\n[]\n=== RESULT\n⟨.W64, y⟩\n=== END\n"

/-- The words of `badWords` that are words (letters, digits and `_` only), with no space. -/
def wordBad : List String := (badWords.map (·.trimAscii.toString)).filter fun w => w.all Lean.isIdRest

/-- A reply whose CONTRACT section is `c`. -/
def withContract (c : String) : String := goodText.replace "=== CONTRACT\nTrue" s!"=== CONTRACT\n{c}"

/-- Extra interface inputs precede the contract and do not change the L3 model inputs. -/
def withBinders (b : String) : String := goodText.replace "=== CONTRACT" s!"=== BINDERS\n{b}\n=== CONTRACT"

def binderChecks : List (String × Bool) :=
  [ ("typed extra pointers parse", !isErr (parseHoles (withBinders "plannedPtr : Ptr\nscratchPtr : Ptr"))),
    ("typed extra vectors and products parse", !isErr (parseHoles (withBinders
      "desired0 : Vector (BitVec 64) 1024\ntrace0 : Vector (BitVec 8 × BitVec 8 × BitVec 16 × BitVec 64) 10240"))),
    ("zero and maximum vector lengths parse", !isErr (parseHoles (withBinders "empty : Vector (BitVec 8) 0")) &&
      !isErr (parseHoles (withBinders "full : Vector (BitVec 8) 65536"))),
    ("negative: more than 64 extra inputs are refused", isErr (parseHoles (withBinders
      ("\n".intercalate ((List.range 65).map fun i => s!"input{i} : Ptr"))))),
    ("negative: duplicate extra inputs are refused", isErr (parseHoles (withBinders "x : Ptr\nx : BitVec 64"))),
    ("negative: malformed extra inputs are refused",
      ["let : Ptr", "if : Ptr", "x : Nat", "x : BitVec 7", "x : Vector (BitVec 64) n", "x : Vector (BitVec 64) 65537",
       "x y : Ptr", "x' : Ptr", "x : Ptr) (evil : Nat", "x : Ptr\n#eval 1", "x : Ptr -- comment",
       "x : Vector (BitVec 64) 1 := junk"].all fun b => isErr (parseHoles (withBinders b))),
    ("negative: a blank BINDERS section is refused", isErr (parseHoles (withBinders ""))) ]

/-- Entry boundary checks call the production admission guard and verdict. -/
def entryChecks : List (String × Bool) :=
  let fn := Lift.Shuffler.Internal.Fns.workspaceSize
  let obj (addr : BitVec 64) (bytes : List (BitVec 8)) (w : Bool) : Lift.Trusted.Object :=
    ⟨addr, bytes.map fun b => ⟨.W8, b⟩, w⟩
  let sample (objs : List Lift.Trusted.Object) : Refute.Case :=
    { pre := true, args := [], objs, expect := some (⟨.W64, 357672⟩, []), junk := 0 }
  let legal := sample [obj 0x1000000 [1, 2] true, obj 0x1000002 [3, 4] true]
  let overlap := sample [obj 0x1000000 [1, 2] true, obj 0x1000001 [2] false]
  let readonly := sample [obj 0x1000000 [1, 2] false, obj 0x1000001 [2] false]
  let conflict := sample [obj 0x1000000 [1, 2] false, obj 0x1000001 [3] false]
  let rsp := Lift.Shuffler.Test.Run.rsp0
  let pointerValues := (List.finRange 64).map fun i => (Refute.pointer i.val (Coordinator.Dst.Rng.ofSeed 1)).1.toNat
  [ ("entry ranges can be adjacent even when their source pointers alias", (Refute.admissionIssue fn legal).isNone &&
      Refute.verdict fn 1 1 (fun _ => legal) == "REFUTE pass 1 0"),
    ("read-only entry ranges can overlap with equal bytes", (Refute.admissionIssue fn readonly).isNone),
    ("negative: overlapping writable entry ranges are not admitted", (Refute.admissionIssue fn overlap).isSome),
    ("negative: conflicting read-only entry bytes are not admitted", (Refute.admissionIssue fn conflict).isSome),
    ("negative: an object that wraps past 2^64 is not admitted",
      (Refute.admissionIssue fn (sample [obj (-1) [1, 2] false])).isSome),
    ("an object can end exactly at 2^64", (Refute.admissionIssue fn (sample [obj (-2) [1, 2] false])).isNone),
    ("negative: an object cannot overlap the return word",
      (Refute.admissionIssue fn (sample [obj rsp [1] false])).isSome),
    ("objects can be adjacent to the stack room and return word",
      (Refute.admissionIssue fn (sample [obj (rsp - 1) [1] true, obj (rsp + 8) [2] true])).isNone),
    ("negative: an object cannot overlap nonempty stack room",
      (Refute.admissionIssue { fn with room := 8 } (sample [obj (rsp - 1) [1] true])).isSome),
    ("negative: fractional-word or wrapping stack room is not admitted",
      (Refute.admissionIssue { fn with room := 1 } legal).isSome &&
      (Refute.admissionIssue { fn with room := rsp.toNat + 1 } legal).isSome),
    ("negative: more than six arguments are not admitted",
      (Refute.admissionIssue fn { legal with args := List.replicate 7 ⟨.W64, 0⟩ }).isSome),
    ("zero requested samples give unknown with counts",
      has (Refute.verdict fn 0 1 (fun _ => legal)) "REFUTE unknown 0 0"),
    ("zero samples in the contract give unknown with counts",
      has (Refute.verdict fn 3 1 (fun _ => { legal with pre := false })) "REFUTE unknown 0 3"),
    ("invalid entry samples give unknown rather than a refutation",
      has (Refute.verdict fn 3 1 (fun _ => overlap)) "REFUTE unknown 0 3"),
    ("valid samples still run after a skipped invalid entry",
      let first := Coordinator.Dst.Rng.stream (Coordinator.Dst.Rng.ofSeed 1) 0
      Refute.verdict fn 2 1 (fun g => if g.state == first.state then overlap else legal) == "REFUTE pass 1 1"),
    ("unknown verdict parsing retains the counts and reason",
      parseVerdict "REFUTE unknown 0 3 no admissible entry" == some (.unknown "0 checked, 3 skipped: no admissible entry")),
    ("extra pointer regions are distinct and below the sampled stack",
      pointerValues.eraseDups.length == 64 && pointerValues.all fun p => 0x100000 ≤ p && p + 0x100000 < rsp.toNat),
    ("the 32-bit input sampler draws more than one value",
      ((List.range 16).map fun seed =>
        ((Refute.draw (Coordinator.Dst.Rng.ofSeed seed) : BitVec 32 × _).1)).eraseDups.length > 1) ]

def pureChecks : List (String × Bool) :=
  binderChecks ++ entryChecks ++
  [ ("there are targets, none of them moved", targets.length > 0 &&
      targets.all fun t => !(Lift.Shuffler.Internal.moved.map (·.entry)).contains t.label),
    ("the targets are the functions of Fns.fns with no moved statement and no trusted statement",
      targets.length + Lift.Shuffler.Internal.moved.length + trustedEntries.length == Lift.Shuffler.Internal.Fns.fns.length),
    ("the targets are 22 by the rule", targets.length == 22),
    ("negative: shuffle (a trusted statement) is not a target", !(targets.map (·.label)).contains "solidity_shuffler_shuffle"),
    ("negative: isRetained (a moved statement) is not a target",
      !(targets.map (·.label)).contains ".Lshuffler.Planner.isRetained"),
    ("the statement names of the targets are distinct", (targets.map (stmtName ·.label)).eraseDups.length == targets.length),
    ("a function with the short name of another has the name of its Fn constant",
      stmtName ".Lshuffler.Planner.run" == "PlannerRun" && stmtName ".Lshuffler.Emission.run" == "EmissionRun"),
    ("a good reply parses", (parseHoles ("reasoning\n" ++ goodText)).toOption ==
      some { room := 0, contract := "True", args := "[]", objects := "[]", written := "[]", result := "⟨.W64, y⟩" }),
    ("negative: a reply with no END is refused", isErr (parseHoles (goodText.replace "=== END\n" ""))),
    ("negative: a reply with no ARGS section is refused", isErr (parseHoles (goodText.replace "=== ARGS\n[]\n" ""))),
    ("negative: a reply with sorry is refused", isErr (parseHoles (goodText.replace "True" "sorry"))),
    ("negative: a reply with a command is refused", isErr (parseHoles (goodText.replace "True" "True\ntheorem t : False := x"))),
    ("a word of badWords inside a longer name is not a banned word (Layout.pend, st'.pend)",
      !isErr (parseHoles (withContract "Layout.pend e st true = x ∧ st'.pend = 0 ∧ pend < 1"))),
    ("a word of badWords inside a longer name is accepted, for each word",
      wordBad.length > 10 && wordBad.all fun w => !isErr (parseHoles (withContract s!"p{w} = x{w}s ∧ y.{w}x = 0"))),
    ("negative: a real end command is refused", isErr (parseHoles (withContract "True\nend Foo")) &&
      isErr (parseHoles (withContract "True\nend"))),
    ("negative: each word of badWords as a word of its own is refused",
      wordBad.all fun w => isErr (parseHoles (withContract s!"True ∧ ({w} x) = 0")) && isErr (parseHoles (withContract s!"True\n{w} x"))),
    ("negative: the symbols # and @[ are refused", isErr (parseHoles (withContract "True\n#eval 1")) &&
      isErr (parseHoles (withContract "True\n@[simp] x"))),
    ("negative: a blank section is refused", isErr (parseHoles (goodText.replace "=== WRITTEN\n[]" "=== WRITTEN\n "))),
    ("negative: a room that is not a number is refused", isErr (parseHoles (goodText.replace "ROOM\n0" "ROOM\neight"))),
    ("the short names and the statement names", shortOf "solidity_shuffler_workspaceSize" == "workspaceSize" &&
      stmtName ".Lshuffler.Emission.swapWith" == "SwapWith" && fnConstOf ".Lshuffler.Emission.swapWith" == "emissionSwapWith") ]

/-- Holes that elaborate for each target: no argument, no object, a 64-bit result. -/
def goodHoles : Holes := { room := 0, contract := "True", args := "[]", objects := "[]", written := "[]", result := "⟨.W64, 0⟩" }

/-- Template checks use a production target context. -/
def binderTemplateChecks (c : Ctx) : List (String × Bool) :=
  let reply := (withBinders "plannedPtr : Ptr\ncontents : Vector (BitVec 8 × BitVec 64) 4").replace "⟨.W64, y⟩" "⟨.W64, 0⟩"
  match parseHoles reply with
  | .error _ => [("extra interface template parses", false)]
  | .ok h =>
    let text := fill c h "binders"
    let refuter := refuteText c h 1 1
    let b := if c.binders.isEmpty then "" else " " ++ c.binders
    let extras := "(plannedPtr : BitVec 64) (contents : Vector ((BitVec 8 × BitVec 64)) 4)"
    [ ("extra interface binders are separate from run and the L3 call",
        has text s!"def run{b} : Option ({c.model.ret}) := some ({c.app c.model.const})" &&
        has text s!"abbrev C{b} {extras} : Prop" &&
        c.interfaceApp h "objects" == " ".intercalate ("objects" :: c.names ++ ["plannedPtr", "contents"])),
      ("extra inputs reach the contract, result and written objects in the refuter",
        has refuter "Skel.IntQ.Refute.pointer 0 g" && has refuter "Skel.IntQ.Refute.draw g : (Vector ((BitVec 8 × BitVec 64)) 4)" &&
        has refuter (c.interfaceApp h s!"{c.module}.C") && has refuter (c.interfaceApp h s!"{c.module}.written") &&
        has refuter (c.interfaceApp h s!"{c.module}.result")),
      ("negative: extra inputs cannot capture template, environment or model names",
        (["run", "e", "y", "g", "trace", "e_trace", "Field", "abiArgs", "stackArgs"] ++ c.names).all fun name =>
          match parseHoles (withBinders s!"{name} : Ptr") with
          | .error _ => true
          | .ok holes => isErr (validateInputs c holes)),
      ("six-section templates use only the original interface binders",
        c.interfaceBinders goodHoles == c.binders && c.interfaceApp goodHoles "objects" == c.app "objects") ]

/-- A caller-owned buffer remains unchanged across workspaceSize. The refuter checks these exact input bytes. -/
def bufferReply : String :=
  "=== ROOM\n0\n=== BINDERS\nplannedPtr : Ptr\ncontents : Vector (BitVec 8 × BitVec 64) 4\n=== CONTRACT\ncontents.toList.length = 4\n=== ARGS\n[]\n=== OBJECTS\n[⟨plannedPtr, contents.toList.flatMap (fun b => [⟨.W8, b.1⟩, ⟨.W64, b.2⟩]), true⟩]\n=== WRITTEN\n[⟨plannedPtr, contents.toList.flatMap (fun b => [⟨.W8, b.1⟩, ⟨.W64, b.2⟩]), true⟩]\n=== RESULT\n⟨.W64, y⟩\n=== END\n"

/-- Change only the claimed output bytes of the buffer. -/
def badBufferReply : String := bufferReply.replace
  "=== WRITTEN\n[⟨plannedPtr, contents.toList.flatMap (fun b => [⟨.W8, b.1⟩, ⟨.W64, b.2⟩]), true⟩]"
  "=== WRITTEN\n[⟨plannedPtr, contents.toList.flatMap (fun _ => [⟨.W8, 0⟩, ⟨.W64, 0⟩]), true⟩]"

/-- The errors of one Lean run of the bodies of the templates of `ps`, each with the neutral holes `goodHoles`. -/
def neutralErrors (dir : System.FilePath) (ps : List PromptIn) : IO (List String) := do
  let imports := (ps.flatMap (·.ctx.imports)).eraseDups
  let text := "\n".intercalate (imports.map ("import " ++ ·)) ++ "\n" ++
    String.join (ps.map fun p =>
      let h := if p.ctx.usesStack then
        { goodHoles with args := "[" ++ ", ".intercalate (p.ctx.target.sym.args.map fun w => s!"⟨{widthCtor w}, 0⟩") ++ "]" }
        else goodHoles
      fillBody p.ctx h "neutral")
  let (_, errs) ← runLean dir "Neutral.lean" text
  pure errs

def targetOf (n : String) (ps : List (Target × Except String PromptIn)) : Option PromptIn :=
  (ps.find? fun (t, _) => stmtName t.label == n).bind fun (_, p) => p.toOption

/-- Panic is an info diagnostic in Lean. The test checks that signal explicitly. -/
def delayedGuardText : String := "\n".intercalate
  [ "import Skel.IntQ.Refute",
    "import Lift.Shuffler.Internal.Fns",
    "open Lift.Trusted Lift.P2.Total Skel.IntQ.Refute",
    "def fn := Lift.Shuffler.Internal.Fns.workspaceSize",
    "def legal : Case := { pre := true, args := [], objs := [], expect := none, junk := 0 }",
    "def many : Case := { legal with args := List.replicate 7 ⟨.W64, 0⟩ }",
    "def overlap : Case := { legal with objs := List.replicate 2 ⟨0x1000000, [⟨.W8, 1⟩], true⟩ }",
    "def outside : Case := { legal with pre := false }",
    "def expected : Option (Field × List Object) := some (⟨.W64, 357672⟩, [])",
    "#eval IO.println ((withExpected fn many (fun _ => panic! \"model evaluated for seven arguments\")).expect.isNone)",
    "#eval IO.println ((withExpected fn overlap (fun _ => panic! \"model evaluated for overlapping objects\")).expect.isNone)",
    "#eval IO.println ((withExpected fn outside (fun _ => panic! \"model evaluated outside the contract\")).expect.isNone)",
    "#eval IO.println (match (withExpected fn legal (fun _ => expected)).expect with | some (r, []) => decide (r = (⟨.W64, 357672⟩ : Field)) | _ => false)", "" ]

def leanChecks : IO (List (String × Bool)) := do
  let dir ← tempDir "intq"
  let ps ← promptInputs
  let all := ps.filterMap (·.2.toOption)
  let prompts := all.map prompt
  let some ws := targetOf "WorkspaceSize" ps | throw (IO.userError "no WorkspaceSize target")
  let some sp := targetOf "IsSpilled" ps | throw (IO.userError "no IsSpilled target")
  let read (d : System.FilePath) (n : String) : IO String := IO.FS.readFile (d / s!"{n}.reply")
  let bufferGood ← check dir ws.ctx bufferReply 16 1
  let bufferBad ← check dir ws.ctx badBufferReply 16 1
  let namedEntry ← check dir ws.ctx (bufferReply.replace "plannedPtr" "entry") 1 1
  let delayed ← runLean dir "DelayedGuard.lean" delayedGuardText
  let panicSignal ← runLean dir "PanicSignal.lean" "import Skel.IntQ.Refute\n#eval (panic! \"guard signal control\" : Nat)\n"
  let reserved ← check dir ws.ctx (withBinders "run : Ptr") 1 1
    (fun _ => throw (IO.userError "a colliding binder reached Lean"))
  let wsGood ← check dir ws.ctx (← read good "WorkspaceSize") 64 1
  let spGood ← check dir sp.ctx (← read good "IsSpilled") 64 1
  let spBad ← check dir sp.ctx (← read bad "IsSpilled") 64 1
  let wsBad ← check dir ws.ctx (← read bad "WorkspaceSize") 64 1
  let retry ← propose (← seqAsker [← read bad "IsSpilled", ← read good "IsSpilled"]) dir sp 64 1
  let notReply := "no holes here"
  let third ← propose (← seqAsker [notReply, ← read bad "IsSpilled", ← read good "IsSpilled"]) dir sp 64 1
  let five ← propose (← seqAsker (List.replicate 5 notReply ++ [← read good "IsSpilled"])) dir sp 64 1
  let stopped ← propose (← seqAsker [notReply]) dir sp 64 1
  let some ia := targetOf "IsAvailable" ps | throw (IO.userError "no IsAvailable target")
  let some idm := targetOf "IsDemanded" ps | throw (IO.userError "no IsDemanded target")
  let some pal := targetOf "PermuteAtLowestHeight" ps | throw (IO.userError "no PermuteAtLowestHeight target")
  let some pm := targetOf "Permute" ps | throw (IO.userError "no Permute target")
  let pmRun ← check dir pm.ctx (← read run1 "Permute") 64 1
  let neutral ← neutralErrors dir all
  let stored3 (n : String) : IO String := IO.FS.readFile (q3 / s!"{n}.reply")
  let refused ← ["EmissionRun", "Generate", "Produce", "PermuteAtLowestHeight"].mapM fun n => do
    pure (n, parseHoles (← stored3 n))
  let some cl := targetOf "Classify" ps | throw (IO.userError "no Classify target")
  let some prod := targetOf "Produce" ps | throw (IO.userError "no Produce target")
  let prodCheck ← check dir prod.ctx (← stored3 "Produce") 64 1
  let some bbu := targetOf "BuildBottomUp" ps | throw (IO.userError "no BuildBottomUp target")
  let bbuRefute ← match parseHoles (← stored3 "BuildBottomUp") with
    | .ok h => runLean dir "BuildBottomUpRefute.lean" (refuteText bbu.ctx h 64 1) 120000
    | .error e => throw (IO.userError e)
  let planner ← ["IsDemanded", "Classify"].mapM fun n => do
    let some p := targetOf n ps | throw (IO.userError s!"no {n} target")
    pure (n, ← check dir p.ctx (← stored3 n) 64 1)
  let some pr := targetOf "PlannerRun" ps | throw (IO.userError "no PlannerRun target")
  let legacy ← match parseHoles (← stored3 "PlannerRun") with
    | .error e => throw (IO.userError e)
    | .ok h => runLean dir "PlannerRunLegacy.lean" (fill pr.ctx h "legacy" ["Skel.IntQ.Refute", "Skel.IntQ.RefuteDraw"] ++ "\n" ++
          "open Skel.IntQ.Refute Lift.Shuffler.Zig\n" ++
          s!"open {pr.ctx.module}\n" ++
          "#eval do\n" ++
          "  let g := Coordinator.Dst.Rng.ofSeed 1\n" ++
          "  let pl := { (draw g : Planner × _).1 with sourceSize := 0, targetSize := 0, reach := 2 }\n" ++
          "  let s := (draw g : PSt × _).1\n" ++
          "  let us := (draw g : (Nat → FlatShuffler.Flat.RunU) × _).1\n" ++
          "  let e := (env g).1\n" ++
          "  let abi := abiArgs pl false s us e\n" ++
          "  let c : Case := { pre := true, args := abi.toList.take 6, stack := some ((abi[6]).v, (abi[7]).v), objs := [], junk := 0, expect := some (⟨.W16, 0⟩, []) }\n" ++
          "  IO.println ((admissionIssue fn c).isNone && (checkCase fn 1000 c).isSome)\n")
  let badSp ← read bad "IsSpilled"
  let deny ← denyModules
  let poolLog ← IO.mkRef (0, 0)
  let job (i : Nat) : IO Nat := do
    poolLog.modify fun (cur, top) => (cur + 1, max top (cur + 1))
    IO.sleep 200
    poolLog.modify fun (cur, top) => (cur - 1, top)
    pure (i * i)
  let pooled ← pool 3 (List.range 7) job
  let (_, top) ← poolLog.get
  let allStages := [Stage.parse, .elaborate, .shape, .room, .refute]
  let passes (k : Checked) : Bool := k.failure.isNone && k.passed == allStages && match k.verdict with
    | some (.pass c _) => c > 0
    | _ => false
  let ledger ← IO.FS.readFile "Lift/Shuffler/Internal/Proposed/ledger.jsonl"
  let ledgerLines := (ledger.splitOn "\n").filter (· != "")
  -- The module of each accepted ledger line is the filled template of a reply of its store, or of its good stored reply.
  let acceptedOk ← all.filterMapM fun p => do
    let isAccepted := ledgerLines.any fun l => has l s!"\"label\":\"{p.ctx.target.label}\"" && has l "\"status\":\"accepted\""
    if !isAccepted then return none
    let f : System.FilePath := s!"Lift/Shuffler/Internal/Proposed/{p.ctx.name}Statement.lean"
    if !(← f.pathExists) then return some false
    let store : System.FilePath := s!"Lift/Shuffler/Internal/Proposed/asks/{p.ctx.name}.jsonl"
    let fromStore ← if ← store.pathExists then
        pure (((← IO.FS.readFile store).splitOn "\n").filterMap fun l =>
          ((Lean.Json.parse l).toOption.bind fun j => (j.getObjValAs? String "reply").toOption))
      else pure []
    let goodFile := good / s!"{p.ctx.name}.reply"
    let fromGood ← if ← goodFile.pathExists then pure [← IO.FS.readFile goodFile] else pure []
    let text ← IO.FS.readFile f
    return some ((fromStore ++ fromGood).any fun r => match parseHoles r with
      | .ok h => text == fill p.ctx h "proposer"
      | .error _ => false)
  pure <|
    binderTemplateChecks ws.ctx ++ binderTemplateChecks sp.ctx ++
    [ ("each target has a model function, a Zig source and a signature", all.length == targets.length && ps.length == targets.length),
      ("the prompt is a pure function of its input", all.map prompt == prompts),
      ("dry run: a prompt for each target, each with the label and the reply form", prompts.length == targets.length &&
        (all.zip prompts).all fun (p, t) => (t.splitOn p.ctx.target.label).length > 1 && (t.splitOn "=== END").length > 1),
      ("the prompt of a retry has the rejected reply and its error",
        let t := prompt { sp with rejected := [("REPLY-X", "ERROR-Y")] }
        (t.splitOn "REPLY-X").length > 1 && (t.splitOn "ERROR-Y").length > 1 && ((prompt sp).splitOn "ERROR-Y").length == 1),
      ("typed extra pointers and buffers pass the five filters", passes bufferGood && match bufferGood.verdict with
        | some (.pass n _) => n == 16
        | _ => false),
      ("negative: changed output bytes of an extra buffer are refused by the production refuter",
        bufferBad.failure.map (·.1) == some .refute && match bufferBad.verdict with
        | some (.real ..) => true
        | _ => false),
      ("negative: a colliding extra input stops before any Lean run", reserved.failure.map (·.1) == some .parse),
      ("the good workspaceSize reply passes the five filters", passes wsGood),
      ("the good isSpilled reply passes the five filters", passes spGood),
      ("negative: the isSpilled reply with the swapped result is refused by the refuter",
        spBad.failure.map (·.1) == some .refute && match spBad.verdict with | some (.real ..) => true | _ => false),
      ("negative: the workspaceSize reply with the room 8 is refused by checkRoom", wsBad.failure.map (·.1) == some .room),
      ("the retry: a wrong reply, then a good one, gives the statement after two asks",
        retry.module.isSome && retry.asks == 2 && retry.tries.length == 2 &&
          ((retry.prompts.getLastD "").splitOn "refute: refuted").length > 1),
      ("each accepted ledger line has its module, the filled template of a reply of its store or of its good reply",
        acceptedOk.length > 0 && acceptedOk.all id),
      ("the ledger has one line for each target", ledgerLines.length == targets.length &&
        targets.all fun t => ledgerLines.any fun l => (l.splitOn s!"\"label\":\"{t.label}\"").length > 1),
      ("the prompt of isAvailable has the definition of FlatShuffler.StackSlot with its fields",
        let t := prompt ia
        has t "### `FlatShuffler.StackSlot`" && has t "structure StackSlot where" &&
          ["payload : BitVec 32", "kind : BitVec 8", "valueOpcode : BitVec 8"].all fun f => has t s!"`FlatShuffler.StackSlot.{f}`"),
      ("the prompt of isAvailable has the fields of Lift.Shuffler.Zig.St and the signature of a callee",
        let t := prompt ia
        has t "`Lift.Shuffler.Zig.St.target : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize`" &&
          has t "`Lift.Shuffler.Zig.isSpilled : Lift.Shuffler.Zig.St → FlatShuffler.StackSlot → Bool`"),
      ("the prompt of isAvailable states the namespace and the open lines of the template",
        let t := prompt ia
        has t "namespace Lift.Shuffler.Internal.Proposed.IsAvailableStatement" &&
          ia.ctx.model.opens.all (has t) && has t "## The names in scope"),
      ("the prompt of permuteAtLowestHeight has the constructors of Lift.Shuffler.Zig.Exit",
        let t := prompt pal
        has t "### `Lift.Shuffler.Zig.Exit`" && has t "`Lift.Shuffler.Zig.Exit.returned" &&
          has t "`Lift.Shuffler.Zig.Exit.assertionExit" && !has t "Exit.ok"),
      ("compiler offsets behind pointers reach every detail level of the permuteAtLowestHeight prompt",
        (List.range 5).all fun level =>
          let t := promptAt pal level
          ["shuffler.Emission: size 120, alignment 8", "planned_mapping: offset 104, size 8",
           "scratch: offset 112, size 8", "shuffler.Scratch: size 74752, alignment 8",
           "permutation: offset 32768, size 8192", "holes: offset 40960, size 8192",
           "parked: offset 49152, size 8192"].all (has t)),
      ("negative: a scalar signature has no compiler record layouts", ws.recordLayouts.isEmpty),
      ("negative: compiler layouts omit records outside the signature graph",
        !has pal.recordLayouts "shuffler.Workspace:" && !has pal.recordLayouts "shuffler.Planner:"),
      ("each prompt names the Encode instances", all.all fun p =>
        let t := prompt p
        has t "`Lift.Pilot.Encode.instEncodeVectorOfInhabited" && has t "`Lift.Trusted.instEncodeBitVecOfNatNat :"),
      ("negative: no prompt names a module or a file of the deny list", deny.length > 0 &&
        all.all fun p => deny.all fun m => !has (prompt p) m && !has (prompt p) (fileOfModule m)),
      ("the binders of the template are fully qualified (isDemanded)",
        has (fill idm.ctx goodHoles "t") "(slot : FlatShuffler.StackSlot)" && has (fill idm.ctx goodHoles "t") "(pl : FlatShuffler.Flat.Planner)"),
      ("the template of each target elaborates with neutral holes", neutral.isEmpty),
      ("each prompt, with 4 rejected replies of the bad isSpilled reply, has at most promptLimit bytes", all.all fun p =>
        (prompt { p with rejected := List.replicate 4 (badSp, String.ofList (List.replicate 600 'e')) }).utf8ByteSize ≤ promptLimit),
      ("negative: the prompt of Planner.run at level 0 has more than promptLimit bytes, and its prompt is a shorter level",
        match targetOf "PlannerRun" ps with
        | some pr => (promptAt pr 0).utf8ByteSize > promptLimit && prompt pr != promptAt pr 0
        | none => false),
      ("a rejected reply is in the prompt as its holes, without the text before === ROOM",
        let t := prompt { sp with rejected := [(badSp, "E")] }
        has t "=== ROOM\n0\n=== CONTRACT\nTrue" && !has t "A wrong result encoding (true and false swapped)"),
      ("rounds: two wrong replies, then a good one, give the statement after 3 asks",
        third.module.isSome && third.asks == 3 && third.tries.length == 3 &&
          ((third.prompts.getLastD "").splitOn "=== END").length > 2),
      ("rounds: 5 wrong replies give open for the final rung after 5 asks; the sixth is not asked",
        match five.fate with
        | .openFinal e => five.asks == 5 && five.tries.length == 5 && has e "parse"
        | _ => false),
      ("negative: a wrong reply and then no reply is stopped, not open for the final rung",
        match stopped.fate with
        | .stopped _ => stopped.asks == 2 && stopped.tries.length == 1
        | _ => false),
      ("the pool keeps the order and runs at most 3 jobs, more than one at a time",
        pooled == (List.range 7).map (fun i => i * i) && top ≤ 3 && top > 1),
      ("INT-Q3: the prompt of isDemanded has the Zig records Planner and SpillSet with their fields and no method",
        let t := prompt idm
        has t "## The records of the function (Zig)" && has t "const Planner = extern struct {" && has t "source_size: usize," &&
          has t "const SpillSet = extern struct {" && has t "spilled: [*]u8," && !has t "noinline fn add("),
      ("INT-Q3: the prompt of classify has the record Mapping with its arrays",
        has (prompt cl) "const Mapping = extern struct {" && has (prompt cl) "destination_of: [max_stack_size]OptionalOffset,"),
      ("INT-Q3: the shared encoding in the prompt has the trace array (the statements of the functions that write the trace had to write it)",
        has (prompt ia) "def trace (e : Env) (st : St) (w : Bool) : Object" && has (prompt idm) "def trace (e : Env) (st : St) (w : Bool) : Object"),
      ("negative: the prompt of isAvailable has no record Emission (Layout.lean has its layout)",
        !has (prompt ia) "const Emission = extern struct"),
      ("negative: the prompt of workspaceSize has no section of records", !has (prompt ws) "## The records"),
      ("INT-Q3: the refute run of buildBottomUp (a model that does not end outside the contract) ends in 120 s with a verdict",
        bbuRefute.2.isEmpty && (bbuRefute.1.filterMap parseVerdict).length == 1),
      ("INT-Q3: the first replies of Emission.run, generate, produce and permuteAtLowestHeight, refused for `end` in `Layout.pend`, parse",
        refused.all fun (_, r) => !isErr r),
      ("INT-Q3: the first reply of produce passes the parse filter, and its error (if any) is not the word `end`",
        prodCheck.passed.contains .parse && match prodCheck.failure with
          | some (_, e) => !has e "word `end`"
          | none => true),
      ("INT-Q3: the refute files of planner functions with admitted samples give a verdict",
        planner.filter (fun (name, _) => name != "PlannerRun") |>.all fun (_, k) => match k.verdict with
          | some (.unknown _) | none => false
          | some _ => true),
      ("negative: the memory-free legacy PlannerRun proposal admits its ABI entry and fails on the machine",
        legacy.2.isEmpty && legacy.1.contains "true"),
      ("an extra binder named entry is preserved in the generated refuter",
        namedEntry.failure.isNone && namedEntry.verdict == some (.pass 1 0)),
      ("invalid entries and inputs outside the contract do not evaluate the model thunk",
        delayed.2.isEmpty && !delayed.1.any (fun line => has line "PANIC") &&
          (delayed.1.filter (· == "true")).length == 4),
      ("the delayed-model test detects the panic signal when its thunk is evaluated",
        panicSignal.2.isEmpty && panicSignal.1.any (fun line => has line "PANIC")),
      ("the old permute reply has no sampled input in its contract",
        pmRun.verdict == some (.unknown "0 checked, 64 skipped: no admissible entry: outside the contract")) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "intq" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks ++ (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  intq: {name}"
  return failed

end IntQTests
