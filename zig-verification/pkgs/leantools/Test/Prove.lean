import LeanTools.Prove
import Test.Harness

/-! Tests of the h1 loop with a scripted model, a scripted reflection model and fake tools. -/

open Lean LeanTools Chat Prove Test

namespace Test.Prove

def call (name : String) (args : Json := Json.mkObj []) (id : String := name) : ToolCall :=
  { id, name, arguments := args.compress }

def reply (calls : Array ToolCall) (content := "") (reasoning := "") : Completion :=
  { message := .assistant content calls reasoning, finishReason := "tool_calls",
    usage := { prompt := 100, cached := 0, completion := 10 } }

structure Fake where
  script : IO.Ref (List Completion)
  proverInputs : IO.Ref (Array (Array Chat.Message))
  /-- The request fields of the stage, for each prover call. -/
  proverExtras : IO.Ref (Array Json)
  reflectorInputs : IO.Ref (Array (Array Chat.Message))
  tools : IO.Ref (Array (String × Json))
  events : IO.Ref (Array Json)
  /-- The call id that each tool call gets: `none` for a forced submission. -/
  ids : IO.Ref (Array (Option String))

/-- `submits` gives the replies of submit_working_file in order; other tools answer "ok NAME". -/
def fake (script : List Completion) (submits : List String) : IO (Fake × Env) := do
  let scriptRef ← IO.mkRef script
  let proverInputs ← IO.mkRef #[]
  let proverExtras ← IO.mkRef #[]
  let reflectorInputs ← IO.mkRef #[]
  let tools ← IO.mkRef #[]
  let events ← IO.mkRef #[]
  let ids ← IO.mkRef #[]
  let f : Fake := { script := scriptRef, proverInputs, proverExtras, reflectorInputs, tools, events, ids }
  let submitsRef ← IO.mkRef submits
  let env : Env := {
    original := pure "ORIGINAL-TEXT"
    originalCheck := "INITIAL-CHECK"
    working := pure "WORKING-TEXT"
    prover := fun extra msgs _ => do
      f.proverInputs.modify (·.push msgs)
      f.proverExtras.modify (·.push extra)
      match ← f.script.get with
      | c :: rest => f.script.set rest; return .ok c
      | [] => return .error "the script is empty"
    reflector := fun msgs => do
      f.reflectorInputs.modify (·.push msgs)
      return .ok { message := .assistant s!"LESSONS-{(← f.reflectorInputs.get).size}",
                   finishReason := "stop", usage := {} }
    tool := fun id name args => do
      f.tools.modify (·.push (name, args))
      f.ids.modify (·.push id)
      if name == "submit_working_file" then
        match ← submitsRef.get with
        | r :: rest => submitsRef.set rest; return (r.startsWith "Accepted", r)
        | [] => return (false, "Not accepted: no reply scripted")
      return (true, s!"ok {name}")
    log := fun j => f.events.modify (·.push j) }
  return (f, env)

def lastUser (msgs : Array Chat.Message) : String :=
  (msgs.toList.filter (·.role == .user)).getLast?.map (·.content) |>.getD ""

def isAccepted : Outcome → Bool | .accepted _ => true | _ => false

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The fields `keys` of each logged event named `event`, as compact JSON. -/
def logged (f : Fake) (event : String) (keys : List String) : IO (List String) := do
  return (← f.events.get).toList.filter (·.getObjValD "event" == toJson event)
    |>.map fun j => (Json.mkObj (keys.map fun k => (k, j.getObjValD k))).compress

def failureRecoverySuite : T Unit := do
  let file := "Work.lean"
  let failure := "HTTP 429: provider retry limit reached"
  let (f, env) ← fake [reply #[call "edit_working_file"]] ["Accepted: t proved"]
  let prover := env.prover
  let env := { env with proverModel := "recovery", prover := fun extra msgs tools => do
    return (← prover extra msgs tools).mapError (fun _ => failure) }
  let s ← prove { maxIterations := 3, price := { input := 10000 } } env file
  check "request failure: accepts checked saved proof" (isAccepted s.outcome)
  checkEq "request failure: preserves replies and cost" (s.iterations, s.turns, s.cost) (1, 1, 1.0)
  checkEq "request failure: preserves usage" (s.usage.prompt, s.usage.completion) (100, 10)
  checkEq "request failure: preserves model" (toJson s.models).compress r#"["recovery"]"#
  checkEq "request failure: no further model request" (← f.proverInputs.get).size 2
  checkEq "request failure: forced submission id" (← f.ids.get).toList [some "edit_working_file", none]
  checkEq "request failure: forced submission file"
    (((← f.tools.get).back?.map (fun (entry : String × Json) => entry.2.getObjValD "file")).getD Json.null).compress
    (toJson file).compress
  checkEq "request failure: no reflection" (← f.reflectorInputs.get).size 0
  checkEq "request failure: records original error"
    (← logged f "request-failed" ["error"]) [(Json.mkObj [("error", toJson failure)]).compress]
  let report := "Accepted: t disproved, with the statements of the original and the standard axioms only."
  let (_, env) ← fake [reply #[call "edit_working_file"]] [report]
  let s ← prove {} env file
  check "request failure: keeps checked disproof report"
    (match s.outcome with | .accepted r => r == report | _ => false)
  let (f, env) ← fake [reply #[call "edit_working_file"]] ["Not accepted: false target"]
  let prover := env.prover
  let env := { env with prover := fun extra msgs tools => do
    return (← prover extra msgs tools).mapError (fun _ => failure) }
  let s ← prove { maxIterations := 3 } env file
  check "request failure: rejected proof keeps original failure"
    (match s.outcome with | .failed e => e == failure | _ => false)
  checkEq "request failure: rejected proof submits once" (← f.ids.get).toList [some "edit_working_file", none]
  checkEq "request failure: rejected proof does not reflect" (← f.reflectorInputs.get).size 0
  checkEq "request failure: rejected proof does not retry model" (← f.proverInputs.get).size 2
  let (f, env) ← fake [reply #[call "edit_working_file"]] ["Accepted: must not submit open work"]
  let env := { env with openWork := pure (some "1 sorry") }
  let s ← prove {} env file
  check "request failure: open work remains failed" (match s.outcome with | .failed _ => true | _ => false)
  checkEq "request failure: open work is not submitted" (← f.ids.get).toList [some "edit_working_file"]
  let (f, env) ← fake [reply #[call "edit_working_file"]] []
  let tool := env.tool
  let env := { env with tool := fun id name args => do
    if name == "submit_working_file" then throw (IO.userError "LOCAL-CHECK-FAILED")
    tool id name args }
  let s ← prove {} env file
  check "request failure: checker exception preserves request error"
    (match s.outcome with | .failed e => e == "the script is empty" | _ => false)
  checkEq "request failure: checker exception does not reflect" (← f.reflectorInputs.get).size 0
  let (_, env) ← fake [reply #[call "edit_working_file"]] ["Accepted: must not submit after open-work error"]
  let s ← prove {} { env with openWork := throw (IO.userError "OPEN-WORK-FAILED") } file
  check "request failure: open-work exception preserves request error"
    (match s.outcome with | .failed e => e == "the script is empty" | _ => false)
  let (f, env) ← fake [] ["Accepted: must not submit before the first reply"]
  let s ← prove {} env file
  check "request failure: initial failure is unchanged" (match s.outcome with | .failed _ => true | _ => false)
  checkEq "request failure: no initial submission" (← f.ids.get).size 0
  let (f, env) ← fake [reply #[call "edit_working_file"]] []
  let tool := env.tool
  let env := { env with tool := fun id name args => do
    if name == "finish" then
      f.ids.modify (·.push id)
      f.tools.modify (·.push (name, args))
      return (true, "Accepted: t proved")
    tool id name args }
  let s ← prove { tools := { schemas := #[], submit := "finish", takesFile := fun _ => false } } env file
  check "request failure: custom submit tool accepts" (isAccepted s.outcome)
  checkEq "request failure: custom submit has no file"
    (((← f.tools.get).back?.map (fun (entry : String × Json) => entry.2.getObjValD "file")).getD Json.null).compress "null"

def suite : T Unit := do
  failureRecoverySuite
  let file := "Work.lean"
  let (f, env) ← fake (List.replicate 3 (reply #[call "submit_working_file"]))
    ["Not accepted: first", "Not accepted: second", "Accepted: t proved"]
  let env := { env with proverModel := "base", reflectionModel := "reflection-effective" }
  let s ← prove { maxIterations := 3, stage := fun i =>
    { turns := 1, extra := Json.mkObj [("model", if i == 1 then "first" else "second")] } } env file
  check "request models: accepted" (isAccepted s.outcome)
  checkEq "request models: stage overrides"
    (← logged f "reply" ["model"]) [r#"{"model":"first"}"#, r#"{"model":"second"}"#, r#"{"model":"second"}"#]
  checkEq "request models: reflection name"
    (← logged f "reflection" ["model"])
    [r#"{"model":"reflection-effective"}"#, r#"{"model":"reflection-effective"}"#]
  checkEq "request models: summary names" (toJson s.models).compress r#"["first","second"]"#
  checkEq "request models: mixed summary has no single model" s.model.compress "null"
  let (_, env) ← fake [reply #[call "submit_working_file"]] ["Accepted: t proved"]
  let s ← prove {} { env with proverModel := "only" } file
  checkEq "request models: single summary model" s.model.compress "\"only\""
  let (_, env) ← fake [] []
  let s ← prove { budgetUsd := 0 } env file
  checkEq "request models: no call has no model" (toJson s.models).compress "[]"
  checkEq "request models: no call has no single model" s.model.compress "null"
  -- accepted in the first iteration; the working file is set on each call
  let (f, env) ← fake [reply #[call "view_working_file" (Json.mkObj [("file", "Other.lean")])],
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "done")])]]
                      ["Accepted: t proved"]
  let s ← prove { stage := fun _ => { turns := 5 } } env file
  check "accepted" (isAccepted s.outcome)
  checkEq "accepted: iterations, turns" (s.iterations, s.turns) (1, 2)
  checkEq "the file is the working file"
    ((← f.tools.get).map fun (n, a) => (n, (a.getObjValAs? String "file").toOption.getD "")).toList
    [("view_working_file", file), ("submit_working_file", file)]
  checkEq "no reflection" (← f.reflectorInputs.get).size 0
  let inputs ← f.proverInputs.get
  check "the tool reply reaches the model, with the turns left"
    (inputs[1]!.back?.map (fun m => m.role == .tool && m.content.startsWith "ok view_working_file"
      && (m.content.splitOn "[4 turns left in this iteration]").length == 2) |>.getD false)
  -- the harness sets `file` only for the tools with a `file` parameter; it overrides the model's
  -- `file` there, and leaves the arguments of the other tools as the model sent them
  let (f, env) ← fake [reply #[call "grep" (Json.mkObj [("pattern", "x")]),
                         call "lean_loogle" (Json.mkObj [("query", "q")]),
                         call "view_file" (Json.mkObj [("path", "A.lean"), ("file", "Other.lean")]),
                         call "lean_goal" (Json.mkObj [("line", 3)]),
                         call "lean_hover_info" (Json.mkObj [("file", "Other.lean"), ("line", 1), ("column", 2)]),
                         call "no_such_tool" (Json.mkObj [("a", 1)])],
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "done")])]]
                      ["Accepted: t proved"]
  let _ ← prove {} env file
  checkEq "file: only for the tools with a file parameter" ((← f.tools.get).map fun (n, a) => (n, a.compress)).toList
    [("grep", r#"{"pattern":"x"}"#), ("lean_loogle", r#"{"query":"q"}"#),
     ("view_file", r#"{"file":"Other.lean","path":"A.lean"}"#),
     ("lean_goal", r#"{"file":"Work.lean","line":3}"#),
     ("lean_hover_info", r#"{"column":2,"file":"Work.lean","line":1}"#),
     ("no_such_tool", r#"{"a":1}"#),
     ("submit_working_file", r#"{"file":"Work.lean","reasoning":"done"}"#)]
  -- the turn limit forces a submission; the reflection feeds the next iteration
  let (f, env) ← fake [reply #[call "view_working_file"], reply #[call "lean_goal"],
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "now")])]]
                      ["Not accepted: 1 sorry", "Accepted: t proved"]
  let s ← prove { stage := fun _ => { turns := 2 } } env file
  check "accepted in iteration 2" (isAccepted s.outcome && s.iterations == 2)
  let ts ← f.tools.get
  checkEq "tools" (ts.map (·.1)).toList ["view_working_file", "lean_goal", "submit_working_file",
    "submit_working_file"]
  check "forced submission" ((ts[2]!.2.getObjValAs? String "reasoning").toOption.getD "" |>.startsWith "[NOTE: this submission was FORCED")
  let refl ← f.reflectorInputs.get
  checkEq "one reflection" refl.size 1
  check "the reflection sees the feedback and the forced note"
    (refl[0]!.any fun m => (m.content.splitOn "Not accepted: 1 sorry").length > 1 && (m.content.splitOn "FORCED").length > 1)
  let second := (← f.proverInputs.get)[2]!
  check "iteration 2 gets the lessons, the code and the feedback"
    (let u := lastUser second; (u.splitOn "LESSONS-1").length > 1 && (u.splitOn "<code>\nWORKING-TEXT").length > 1
      && (u.splitOn "Not accepted: 1 sorry").length > 1 && (u.splitOn "ORIGINAL-TEXT").length > 1)
  checkEq "iteration 2 starts a new conversation" (second.size) 2
  -- no tool call: one request to submit, then a forced submission
  let (f, env) ← fake [reply #[] "I think", reply #[] "still thinking"] ["Not accepted: x"]
  let s ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1 } env file
  check "no tool call: out of iterations" (match s.outcome with | .iterations => true | _ => false)
  check "no tool call: closed with a request to submit"
    ((← f.proverInputs.get)[1]!.back?.map (·.content.startsWith "You ended your turn without calling any tool") |>.getD false)
  check "no tool call: forced"
    (((← f.tools.get).map (·.1)).toList == ["submit_working_file"]
      && (((← f.tools.get)[0]!.2.getObjValAs? String "reasoning").toOption.getD "").startsWith "[NOTE: this submission was FORCED")
  checkEq "no reflection after the last iteration" (← f.reflectorInputs.get).size 0
  -- An output limit does not mean that the model chose to stop. Never run its partial calls.
  let clipped := { reply #[call "submit_working_file"] with finishReason := "length" }
  let (f, env) ← fake [clipped, clipped, reply #[call "submit_working_file"]] ["Accepted: t proved"]
  let s ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1 } env file
  check "length: model can recover" (isAccepted s.outcome && s.turns == 3)
  checkEq "length: partial calls do not run" (← f.tools.get).size 1
  check "length: retry instruction" (has (lastUser ((← f.proverInputs.get).getD 1 #[])) "output limit")
  let events ← f.events.get
  let replies := events.filter (·.getObjValD "event" == toJson "reply")
  checkEq "length: finish reason is logged" (replies[0]!.getObjValAs? String "finish_reason").toOption (some "length")
  check "completion timing is logged" ((replies[0]!.getObjValAs? Nat "elapsed_ms").isOk)
  -- Reflection usage has the same accounting and completion metadata as prover usage.
  let (f, env) ← fake [reply #[call "submit_working_file"], reply #[call "submit_working_file"]]
    ["Not accepted: x", "Accepted: t proved"]
  let env := { env with reflector := fun _ => do
    return .ok { message := .assistant "lesson", finishReason := "stop",
                 usage := { prompt := 17, cached := 3, completion := 5 } } }
  let cfg : Prove.Config := {
    stage := fun _ => { turns := 1 }
    budgetUsd := 1000
    price := { input := 1000000 }
    reflectionPrice := { input := 1000000, cachedInput := 1000000, output := 1000000 } }
  let s ← prove cfg env file
  checkEq "reflection: usage totals" s.usage { prompt := 217, cached := 3, completion := 25 }
  checkEq "reflection: cost totals" s.cost 222.0
  let rs := (← f.events.get).filter (·.getObjValD "event" == toJson "reflection")
  checkEq "reflection: usage logged" (rs[0]!.getObjValAs? Nat "prompt_tokens").toOption (some 17)
  checkEq "reflection: finish logged" (rs[0]!.getObjValAs? String "finish_reason").toOption (some "stop")
  -- A cut reflection still costs tokens but must not replace the last complete context.
  let (f, env) ← fake (List.replicate 3 (reply #[call "submit_working_file"]))
    ["Not accepted: x", "Not accepted: y", "Accepted: t proved"]
  let count ← IO.mkRef (0 : Nat)
  let env := { env with reflector := fun _ => do
    count.modify (· + 1)
    let first := (← count.get) == 1
    return .ok {
      message := .assistant (if first then "KEPT-LESSON" else "CUT-LESSON"),
      finishReason := if first then "stop" else "length",
      usage := { prompt := 17, cached := 3, completion := 5 } } }
  let s ← prove { stage := fun _ => { turns := 1 }, maxIterations := 3 } env file
  check "reflection length: run completes" (isAccepted s.outcome)
  checkEq "reflection length: usage counts" s.usage { prompt := 334, cached := 6, completion := 40 }
  let third := lastUser ((← f.proverInputs.get).getD 2 #[])
  check "reflection length: previous context stays" (has third "KEPT-LESSON" && !has third "CUT-LESSON") third
  let rs := (← f.events.get).filter (·.getObjValD "event" == toJson "reflection")
  checkEq "reflection length: unused flag" (rs[1]!.getObjValAs? Bool "used").toOption (some false)
  -- the cost limit: each call costs 1 USD here
  let (f, env) ← fake (List.replicate 5 (reply #[call "view_working_file"])) []
  let s ← prove { stage := fun _ => { turns := 5 }, budgetUsd := 1.5, price := { input := 10000 } } env file
  check "budget" (match s.outcome with | .budget => true | _ => false)
  checkEq "budget: calls" (← f.proverInputs.get).size 2
  checkEq "budget: cost" s.cost 2.0
  -- a model error ends the run
  let (_, env) ← fake [] []
  let s ← prove {} { env with proverModel := "failed" } file
  check "model error" (match s.outcome with | .failed e => e.startsWith "the script is empty" | _ => false)
  checkEq "model error: requested model is kept" (toJson s.models).compress r#"["failed"]"#
  checkEq "model error: single summary model" s.model.compress "\"failed\""
  -- an exception of the environment ends the run; the turns and the cost so far are kept
  let (_, env) ← fake [reply #[call "view_working_file"]] []
  let env := { env with tool := fun _ _ _ => throw (IO.userError "TOOL-EXCEPTION") }
  let s ← try prove { price := { input := 10000 } } env file
    catch e => pure { outcome := .failed s!"not caught: {e}", iterations := 0, turns := 0, usage := {}, cost := 0 }
  check "exception: failed" (match s.outcome with | .failed e => e == "TOOL-EXCEPTION" | _ => false) (repr s.outcome |>.pretty)
  checkEq "exception: iterations, turns, cost" (s.iterations, s.turns, s.cost) (1, 1, 1.0)
  let (f, env) ← fake [reply #[call "view_working_file"]] []
  let env := { env with original := throw (IO.userError "NO-ORIGINAL") }
  let s ← try prove {} env file
    catch e => pure { outcome := .failed s!"not caught: {e}", iterations := 0, turns := 0, usage := {}, cost := 0 }
  check "no original: failed" (match s.outcome with | .failed e => e == "NO-ORIGINAL" | _ => false) (repr s.outcome |>.pretty)
  checkEq "no original: no model call" ((← f.proverInputs.get).size, s.iterations) (0, 0)
  -- each first message has the original's first check; the system prompt is the configured one
  let (f, env) ← fake [reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")])]] ["Accepted: t proved"]
  let _ ← prove { system := "SYSTEM-TEXT" } env file
  let first := (← f.proverInputs.get)[0]!
  checkEq "system prompt" (first[0]!.role, first[0]!.content) (.system, "SYSTEM-TEXT")
  check "initial feedback" (has (lastUser first) "<initial-feedback>\nINITIAL-CHECK\n</initial-feedback>")
  check "saved work: first iteration includes the current proof"
    (has (lastUser first) "<code>\nWORKING-TEXT\n</code>")
  let (f, env) ← fake [reply #[call "submit_working_file"]] ["Accepted: t proved"]
  let _ ← prove {} { env with working := pure "ORIGINAL-TEXT" } file
  check "saved work: unchanged original is not repeated"
    (!has (lastUser ((← f.proverInputs.get)[0]!)) "<code>")
  let (f, env) ← fake [] []
  let s ← prove {} { env with working := throw (IO.userError "NO-WORKING") } file
  check "saved work: read failure stops before a model call"
    (match s.outcome with | .failed e => e == "NO-WORKING" | _ => false)
  checkEq "saved work: no model call after read failure" (← f.proverInputs.get).size 0
  -- the transcript: whole when it fits; else the file views are left out, then middle turns
  let big := String.ofList (List.replicate 1000 'x')
  let msgs := #[Chat.Message.system "SYS", .user "FIRST",
    .assistant "" #[call "view_working_file" (id := "v1")], .tool "v1" big,
    .assistant "" #[call "lean_goal" (id := "g1")], .tool "g1" "GOAL-REPLY",
    .assistant "LAST"]
  check "transcript: whole" (has (transcript msgs 100000) big)
  let t := transcript msgs 600
  check "transcript: file view left out" (!has t big && has t "[file contents left out")
  check "transcript: other replies kept" (has t "GOAL-REPLY" && has t "FIRST" && has t "LAST" && !has t "omitted")
  let msgs := msgs ++ #[.assistant (String.ofList (List.replicate 500 'y')), .assistant "END"]
  let t := transcript msgs 600
  check "transcript: middle turns omitted" (has t "messages omitted" && has t "FIRST" && has t "END"
    && !has t big && t.length ≤ 700) t
  -- the transcript has the prover's reasoning; the cut still bounds it
  let msgs := #[Chat.Message.system "SYS", .user "FIRST",
    .assistant "" #[call "lean_goal" (id := "g1")] "WHY-1", .tool "g1" "GOAL-REPLY"]
  check "transcript: reasoning" (has (transcript msgs 100000) "WHY-1")
  let msgs := msgs ++ #[.assistant "" #[call "lean_goal" (id := "g2")] (String.ofList (List.replicate 5000 'z')),
    .tool "g2" "GOAL-REPLY", .assistant "END" #[] "WHY-END"]
  let t := transcript msgs 600
  check "transcript: long reasoning omitted" (has t "messages omitted" && has t "FIRST" && has t "END"
    && has t "WHY-END" && !has t "zzz" && t.length ≤ 700) t
  -- the transcript has no system prompt: the reflection's own prompt describes the setting
  check "transcript: no system prompt" (!has (transcript #[Chat.Message.system "SYSTEM-PROMPT", .user "FIRST"] 100000) "SYSTEM-PROMPT")
  -- a view_file reply (a library file) is left out with the other file views
  let lib := String.ofList (List.replicate 1000 'l')
  let msgs := #[Chat.Message.system "SYS", .user "FIRST",
    .assistant "" #[call "view_file" (id := "f1")], .tool "f1" lib, .assistant "LAST"]
  let t := transcript msgs 600
  check "transcript: view_file left out" (!has t lib && has t "[file contents left out" && has t "LAST") t
  -- before a turn is left out, long reasoning keeps its head and tail, a long tool reply its head;
  -- each turn's calls remain
  let mid := String.ofList (List.replicate 6000 'm')
  let longReply := "REPLY-HEAD" ++ String.ofList (List.replicate 6000 'r') ++ "REPLY-TAIL"
  let msgs := #[Chat.Message.system "SYS", .user "FIRST",
    .assistant "" #[call "lean_goal" (id := "g1")] ("WHY-HEAD" ++ mid ++ "WHY-TAIL"), .tool "g1" longReply,
    .assistant "" #[call "grep" (id := "g2")] "SHORT", .tool "g2" "GREP-REPLY",
    .assistant "END"]
  let t := transcript msgs 9000
  check "clip: no turn left out" (!has t "messages omitted" && has t "FIRST" && has t "END" && has t "GREP-REPLY") t
  check "clip: the reasoning's head and tail" (has t "WHY-HEAD" && has t "WHY-TAIL" && !has t mid && has t "characters of reasoning left out]") t
  check "clip: the reply's head" (has t "REPLY-HEAD" && !has t "REPLY-TAIL" && has t "characters of the reply left out]") t
  check "clip: the call" (has t "[tool call lean_goal") t
  check "clip: within the limit" (t.length ≤ 9000) s!"{t.length}"
  -- the first message (the original and its check) is never cut
  let firstBig := "FIRST" ++ String.ofList (List.replicate 5000 'f') ++ "FIRST-END"
  let t := transcript #[Chat.Message.system "SYS", .user firstBig, .assistant "" #[] mid, .assistant "END"] 7000
  check "clip: the first message whole" (has t "FIRST-END" && has t "END") t
  -- a submission ends the iteration: later calls of the same reply do not run
  let (f, env) ← fake [reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")]), call "view_working_file"]]
                      ["Accepted: t proved"]
  let _ ← prove {} env file
  checkEq "submit stops the other calls" ((← f.tools.get).map (·.1)).toList ["submit_working_file"]
  -- arguments that are not a JSON object go back to the model as an error
  let (f, env) ← fake [reply #[{ id := "c", name := "lean_goal", arguments := "line 3" }],
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")])]] ["Accepted: t proved"]
  let _ ← prove {} env file
  checkEq "bad arguments: no tool call" ((← f.tools.get).map (·.1)).toList ["submit_working_file"]
  check "bad arguments: error to the model"
    ((← f.proverInputs.get)[1]!.back?.map (·.content.startsWith "Error: the arguments are not a JSON object") |>.getD false)
  -- the record: each call with its id, name and arguments as the model sent them (without the
  -- `file` that the harness adds; the raw text when it is not JSON); the id joins the tool events
  let (f, env) ← fake [reply #[call "lean_goal" (Json.mkObj [("line", 3)]) "g1",
                         { id := "b1", name := "grep", arguments := "line 3" }],
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")]) "s1"]]
                      ["Accepted: t proved"]
  let _ ← prove {} env file
  checkEq "record: calls of the replies" (← logged f "reply" ["tool_calls", "calls"])
    [r#"{"calls":[{"arguments":{"line":3},"id":"g1","name":"lean_goal"},{"arguments":"line 3","id":"b1","name":"grep"}],"tool_calls":["lean_goal","grep"]}"#,
     r#"{"calls":[{"arguments":{"reasoning":"r"},"id":"s1","name":"submit_working_file"}],"tool_calls":["submit_working_file"]}"#]
  checkEq "record: tool events" (← logged f "tool" ["id", "name", "ok"]) [r#"{"id":"g1","name":"lean_goal","ok":true}"#]
  checkEq "record: submit event" (← logged f "submit" ["id", "reasoning", "accepted"])
    [r#"{"accepted":true,"id":"s1","reasoning":"r"}"#]
  checkEq "record: the call ids reach the tools" (← f.ids.get).toList [some "g1", some "s1"]
  -- the forced submissions have no call id: the turn limit (iteration 1), no tool call (iteration 2)
  let (f, env) ← fake [reply #[call "view_working_file" (id := "v1")], reply #[call "lean_goal" (id := "v2")],
                       reply #[] "I think", reply #[] "still"]
                      ["Not accepted: x", "Not accepted: y"]
  let _ ← prove { stage := fun _ => { turns := 2 }, maxIterations := 2 } env file
  checkEq "record: forced, calls" (← logged f "reply" ["calls"])
    [r#"{"calls":[{"arguments":{},"id":"v1","name":"view_working_file"}]}"#,
     r#"{"calls":[{"arguments":{},"id":"v2","name":"lean_goal"}]}"#, r#"{"calls":[]}"#, r#"{"calls":[]}"#]
  checkEq "record: forced, submit events" (← logged f "submit" ["id", "reasoning"])
    [(Json.mkObj [("id", Json.null), ("reasoning", toJson forcedTurns)]).compress,
     (Json.mkObj [("id", Json.null), ("reasoning", toJson forcedSilent)]).compress]
  checkEq "record: forced, the call ids reach the tools" (← f.ids.get).toList [some "v1", some "v2", none, none]
  -- the reasoning: sent back within the iteration, not into the next one; in the record and the
  -- reflection's transcript
  let (f, env) ← fake [reply #[call "view_working_file"] (reasoning := "THINK-1"),
                       reply #[call "lean_goal"] (reasoning := "THINK-2"),
                       reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")])]]
                      ["Not accepted: x", "Accepted: t proved"]
  let _ ← prove { stage := fun _ => { turns := 2 } } env file
  let inputs ← f.proverInputs.get
  let reasonings (msgs : Array Chat.Message) := (msgs.filter (·.role == .assistant)).map (·.reasoning)
  checkEq "reasoning: sent back in the iteration" (inputs.map reasonings)
    #[#[], #["THINK-1"], #[]]
  checkEq "reasoning: record" (← logged f "reply" ["reasoning"])
    [r#"{"reasoning":"THINK-1"}"#, r#"{"reasoning":"THINK-2"}"#, r#"{"reasoning":""}"#]
  check "reasoning: the reflection sees it"
    ((← f.reflectorInputs.get)[0]!.any fun m => has m.content "THINK-1" && has m.content "THINK-2")
  -- the stages: iteration i has the turn limit and the request fields of `stage i`; the record
  -- has them in the iteration event
  let stages (i : Nat) : Stage := if i == 1 then { turns := 1, extra := Json.mkObj [("effort", "high")] }
    else { turns := 2, extra := Json.mkObj [("effort", "max")] }
  let (f, env) ← fake [reply #[call "view_working_file"],
                       reply #[call "view_working_file"], reply #[call "lean_goal"],
                       reply #[call "view_working_file"], reply #[call "submit_working_file" (Json.mkObj [("reasoning", "r")])]]
                      ["Not accepted: x", "Not accepted: y", "Accepted: t proved"]
  let s ← prove { stage := stages, maxIterations := 3 } env file
  check "stages: accepted in iteration 3" (isAccepted s.outcome && s.iterations == 3)
  checkEq "stages: turns of each iteration" ((← f.proverInputs.get).map (·.size)).toList [2, 2, 4, 2, 4]
  checkEq "stages: the request fields of each call" ((← f.proverExtras.get).map (·.compress)).toList
    [r#"{"effort":"high"}"#, r#"{"effort":"max"}"#, r#"{"effort":"max"}"#, r#"{"effort":"max"}"#, r#"{"effort":"max"}"#]
  check "stages: the turns left count from the stage's limit"
    ((← f.proverInputs.get)[2]!.back?.map (has ·.content "[1 turns left in this iteration]") |>.getD false)
  checkEq "stages: record" (← logged f "iteration" ["iteration", "turns", "extra"])
    [r#"{"extra":{"effort":"high"},"iteration":1,"turns":1}"#, r#"{"extra":{"effort":"max"},"iteration":2,"turns":2}"#,
     r#"{"extra":{"effort":"max"},"iteration":3,"turns":2}"#]

def contextError := "HTTP 400: Provider returned error: This model configuration accepts at most 1048576 combined input and output tokens."

/-- Context failures close a partial iteration, then use the normal validator and reflection. -/
def contextSuite : T Unit := do
  let file := "Work.lean"
  let (f, env) ← fake [reply #[call "edit_working_file"] (reasoning := "SAVED-WORK"),
      reply #[call "submit_working_file"]] ["Not accepted: open goals", "Accepted: t proved"]
  let attempts ← IO.mkRef (0 : Nat)
  let send := env.prover
  let env := { env with prover := fun extra msgs tools => do
    attempts.modify (· + 1)
    if (← attempts.get) == 2 then return .error contextError
    send extra msgs tools }
  let s ← prove { maxIterations := 3 } env file
  check "context error: resumes and accepts" (isAccepted s.outcome && s.iterations == 2)
  checkEq "context error: successful replies only" s.turns 2
  checkEq "context error: refused request is not retried" (← attempts.get) 3
  checkEq "context error: reflects once" (← f.reflectorInputs.get).size 1
  checkEq "context error: edit runs once" ((← f.tools.get).filter (·.1 == "edit_working_file")).size 1
  check "context error: reflection contains saved work"
    ((← f.reflectorInputs.get).any fun ms => ms.any (has ·.content "SAVED-WORK"))
  check "context error: next iteration has code and reflection"
    ((← f.proverInputs.get).any fun ms => has (lastUser ms) "WORKING-TEXT" && has (lastUser ms) "LESSONS-1")
  -- A refusal on the first request cannot be fixed by repeating an unchanged prompt.
  let (f, env) ← fake [] []
  let s ← prove { maxIterations := 3 } { env with prover := fun _ _ _ => pure (.error contextError) } file
  check "initial context error: fails without empty iterations"
    (match s.outcome with | .failed _ => s.iterations == 1 && s.turns == 0 | _ => false)
  checkEq "initial context error: no reflection" (← f.reflectorInputs.get).size 0
  checkEq "initial context error: no submission" (← f.tools.get).size 0
  -- Other bad requests must keep their original error outcome.
  let (f, env) ← fake [reply #[call "edit_working_file"]] []
  let send := env.prover
  let attempts ← IO.mkRef (0 : Nat)
  let bad := "HTTP 400: invalid tool schema"
  let env := { env with prover := fun extra msgs tools => do
    attempts.modify (· + 1)
    if (← attempts.get) == 2 then return .error bad
    send extra msgs tools }
  let s ← prove { maxIterations := 3 } env file
  check "other HTTP error: remains failed" (match s.outcome with | .failed e => e == bad | _ => false)
  checkEq "other HTTP error: no reflection" (← f.reflectorInputs.get).size 0

/-- Token estimates close complete tool rounds at the configured input bound. -/
def thresholdSuite : T Unit := do
  let file := "Work.lean"
  let extra := Json.mkObj [("max_tokens", toJson (393216 : Nat))]
  let limit : ContextLimit := { window := 1048576 }
  checkEq "context: reserve output before applying percent" (limit.inputLimit extra) 557056
  forAll "context: threshold stays in the input room" 300 71
    (fun g => let (w, g) := below 1000000 g; let (o, g) := below (w + 1) g
              let (p, g) := below 100 g; ((w, o, p + 1), g))
    fun (w, o, p) => ({ window := w, percent := p } : ContextLimit).inputLimit
      (Json.mkObj [("max_tokens", toJson o)]) ≤ w - o
  let toolMessage := Chat.Message.tool "edit_working_file" "ok edit_working_file\n[3 turns left in this iteration]"
  let bound := messageTokenBound toolMessage
  let cfg : Prove.Config := { stage := fun _ => { turns := 4, extra }, maxIterations := 2, context := some limit }
  for delta in [0, 1] do
    let tokens := limit.inputLimit extra - bound - delta
    let first := { reply #[call "edit_working_file"] with usage := { prompt := tokens - 10, completion := 10 } }
    let (f, env) ← fake [first, reply #[call "submit_working_file"]]
      (if delta == 0 then ["Not accepted: open", "Accepted"] else ["Accepted"])
    let s ← prove cfg env file
    check s!"context boundary {delta}: accepted" (isAccepted s.outcome)
    checkEq s!"context boundary {delta}: iteration" s.iterations (if delta == 0 then 2 else 1)
    checkEq s!"context boundary {delta}: reflection count" (← f.reflectorInputs.get).size (if delta == 0 then 1 else 0)
    if delta == 0 then
      let events ← logged f "context-limit" ["estimated_input_tokens", "input_limit_tokens"]
      checkEq "context: event records measured threshold" events
        [r#"{"estimated_input_tokens":557056,"input_limit_tokens":557056}"#]
  -- Both tools from one assistant message finish before the threshold checkpoint.
  let (f, env) ← fake
    [{ reply #[call "edit_working_file", call "lean_goal"] with usage := { prompt := 550000, completion := 8000 } },
     reply #[call "submit_working_file"]] ["Not accepted: open", "Accepted"]
  let s ← prove cfg env file
  check "context: completion tokens reach next input" (isAccepted s.outcome && s.iterations == 2)
  checkEq "context: complete tool round before checkpoint"
    ((← f.tools.get).map (·.1)).toList ["edit_working_file", "lean_goal", "submit_working_file", "submit_working_file"]
  -- A large tool result can cross the boundary even when the model reply is small.
  let (_, env) ← fake [reply #[call "view_file"], reply #[call "submit_working_file"]]
    ["Not accepted: open", "Accepted"]
  let tool := env.tool
  let huge := String.ofList (List.replicate 600000 'x')
  let env := { env with tool := fun id name args => do
    let r ← tool id name args
    return if name == "view_file" then (true, huge) else r }
  let s ← prove cfg env file
  check "context: tool bytes trigger reflection" (isAccepted s.outcome && s.iterations == 2)
  -- Without usage, count the encoded prompt, schemas, assistant reply and tool output.
  let (f, env) ← fake [{ reply #[call "edit_working_file"] with usageKnown := false },
      reply #[call "submit_working_file"]] ["Not accepted: open", "Accepted"]
  let small : Prove.Config := { cfg with
    context := some { window := 600, percent := 85 }
    stage := fun _ => { turns := 4, extra := Json.mkObj [("max_tokens", toJson (100 : Nat))] } }
  let s ← prove small env file
  check "context: missing usage uses encoded messages" (isAccepted s.outcome && s.iterations == 2)
  checkEq "context: unknown usage has one reflection" (← f.reflectorInputs.get).size 1
  -- A forced checkpoint can accept; acceptance never causes a reflection or a new call.
  let (f, env) ← fake [{ reply #[call "edit_working_file"] with usage := { prompt := 558000 } }] ["Accepted"]
  let s ← prove cfg env file
  check "context: checkpoint can accept" (isAccepted s.outcome && s.turns == 1)
  checkEq "context: no reflection after acceptance" (← f.reflectorInputs.get).size 0
  -- The last permitted iteration still checks the file, then stops at its limit.
  let (f, env) ← fake [{ reply #[call "edit_working_file"] with usage := { prompt := 558000 } }] ["Not accepted: open"]
  let s ← prove { cfg with maxIterations := 1 } env file
  check "context: final iteration stays within limit" (s.outcome.name == "iterations" && s.iterations == 1 && s.turns == 1)
  checkEq "context: final iteration does not reflect" (← f.reflectorInputs.get).size 0
  checkEq "context: final iteration still checks" (← f.ids.get).toList [some "edit_working_file", none]
  -- A schedule changes the reservation at the next iteration, not in the current round.
  let later := Json.mkObj [("max_tokens", toJson (100 : Nat))]
  let (f, env) ← fake
    [{ reply #[call "edit_working_file"] with usage := { prompt := 558000 } },
     { reply #[call "edit_working_file"] with usage := { prompt := 558000 } }, reply #[call "submit_working_file"]]
    ["Not accepted: open", "Accepted"]
  let s ← prove { cfg with stage := fun i => { turns := 4, extra := if i == 1 then extra else later } } env file
  check "context: schedule applies new output reservation" (isAccepted s.outcome && s.iterations == 2 && s.turns == 3)
  checkEq "context: schedule reflects only at first threshold" (← f.reflectorInputs.get).size 1
  for e in [contextError, "HTTP 400: context_length_exceeded", "HTTP 413: maximum context length",
      "HTTP 400: input length exceeds the context window"] do
    check "context: recognize provider refusal" (isContextError e) e
  for e in ["HTTP 429: maximum context length", "HTTP 400: invalid schema", "transport context_length_exceeded"] do
    check "context: leave other errors fatal" (!isContextError e) e

/-- A toolset: another submit tool, other schemas, and a rejection that does not end the iteration. -/
def toolsetSuite : T Unit := do
  let file := "Work.lean"
  -- a toolset: another submit tool without a `file` parameter, other schemas, and a rejected
  -- submission that is a tool error while the iteration goes on
  let schemas : Array Json := #[Json.mkObj [("type", "function"), ("function", Json.mkObj [("name", "finish")])]]
  let toolset : Toolset := { schemas, submit := "finish", takesFile := fun _ => false, continueOnReject := true }
  let finishReplies ← IO.mkRef ["Not accepted: first reason", "Not accepted: second reason", "Accepted: t proved"]
  let (f, env) ← fake [reply #[call "view_working_file" (Json.mkObj [("line", 1)]),
                               call "finish" (Json.mkObj [("reasoning", "r1")]) "f1",
                               call "lean_goal" (Json.mkObj [("line", 2)])],
                       reply #[call "finish" (Json.mkObj [("reasoning", "r2")]) "f2"],
                       reply #[call "finish" (Json.mkObj [("reasoning", "r3")]) "f3", call "grep"]] []
  let env := { env with tool := fun id name args => do
    f.tools.modify (·.push (name, args))
    f.ids.modify (·.push id)
    if name == "finish" then
      match ← finishReplies.get with
      | r :: rest => finishReplies.set rest; return (r.startsWith "Accepted", r)
      | [] => return (false, "no reply scripted")
    return (true, s!"ok {name}") }
  let s ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1, tools := toolset } env file
  check "toolset: accepted in the first iteration" (isAccepted s.outcome && s.iterations == 1 && s.turns == 3)
  checkEq "toolset: the model sees the given schemas" (← f.proverInputs.get).size 3
  checkEq "toolset: calls, with no file argument and the calls after a rejection run"
    ((← f.tools.get).map fun (n, a) => (n, a.compress)).toList
    [("view_working_file", r#"{"line":1}"#), ("finish", r#"{"reasoning":"r1"}"#), ("lean_goal", r#"{"line":2}"#),
     ("finish", r#"{"reasoning":"r2"}"#), ("finish", r#"{"reasoning":"r3"}"#)]
  let inputs ← f.proverInputs.get
  let toolReplies (msgs : Array Chat.Message) := (msgs.filter (·.role == .tool)).map (·.content)
  checkEq "toolset: a rejection is a tool error, with the turns left" (toolReplies inputs[1]!).toList
    ["ok view_working_file\n[4 turns left in this iteration]",
     "Error: Not accepted: first reason\n[4 turns left in this iteration]",
     "ok lean_goal\n[4 turns left in this iteration]"]
  checkEq "toolset: the iteration is one conversation" (inputs.map (·.size)).toList [2, 6, 8]
  checkEq "toolset: no reflection" (← f.reflectorInputs.get).size 0
  -- the schemas that the toolset gives are those of the requests
  let seen ← IO.mkRef (#[] : Array (Array Json))
  let (_, env) ← fake [reply #[call "finish" (Json.mkObj [("reasoning", "r")])]] []
  let env := { env with
    prover := fun _ _ tools => do seen.modify (·.push tools); return .ok (reply #[call "finish"])
    tool := fun _ _ _ => return (true, "Accepted: t proved") }
  let _ ← prove { tools := toolset } env file
  checkEq "toolset: the request has the given schemas" ((← seen.get).map (·.map (·.compress))).toList
    [schemas.map (·.compress)]
  -- a rejection with the iteration going on: the turn limit forces a submission, which ends it
  let (f, env) ← fake [reply #[call "finish"], reply #[call "view_working_file"]] []
  let env := { env with tool := fun id name args => do
    f.tools.modify (·.push (name, args))
    f.ids.modify (·.push id)
    return (false, if name == "finish" then "Not accepted: still open" else "ok") }
  let s ← prove { stage := fun _ => { turns := 2 }, maxIterations := 1, tools := toolset } env file
  check "toolset: the forced submission ends the iteration" (match s.outcome with | .iterations => true | _ => false)
  checkEq "toolset: forced call has no file" ((← f.tools.get).map fun (n, a) => (n, a.compress)).toList
    [("finish", "{}"), ("view_working_file", "{}"),
     ("finish", (Json.mkObj [("reasoning", toJson forcedTurns)]).compress)]
  checkEq "toolset: forced call has no id" (← f.ids.get).toList [some "finish", some "view_working_file", none]
  -- the silent end of the model names the given submit tool
  let (f, env) ← fake [reply #[] "I think", reply #[] "still"] []
  let env := { env with tool := fun _ _ _ => return (false, "Not accepted: x") }
  let _ ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1, tools := toolset } env file
  check "toolset: the close request names the submit tool"
    ((← f.proverInputs.get)[1]!.back?.map (has ·.content "Call finish now") |>.getD false)
  -- a reply with no tool call, with something open in the file, says what is open and does not ask to submit
  let (f, env) ← fake [reply #[] "I think", reply #[call "submit_working_file"]] []
  let env := { env with openWork := pure (some "0 errors and 1 `sorry` (`sorry` at 7:3)."),
                        tool := fun _ _ _ => return (true, "Accepted: t proved") }
  let _ ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1, tools := toolset } env file
  let nudge := lastUser ((← f.proverInputs.get)[1]!)
  check "open work: the message says what is open" (has nudge "1 `sorry` (`sorry` at 7:3)")
  check "open work: the message does not ask to submit" (!has nudge "Call finish")
  -- nothing open: the request to submit stays
  let (f, env) ← fake [reply #[] "I think", reply #[call "submit_working_file"]] []
  let env := { env with openWork := pure none, tool := fun _ _ _ => return (true, "Accepted: t proved") }
  let _ ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1, tools := toolset } env file
  check "no open work: the request to submit" (has (lastUser ((← f.proverInputs.get)[1]!)) "Call finish now")
  -- a rejected submission still ends the iteration with the default toolset
  let (f, env) ← fake [reply #[call "submit_working_file", call "view_working_file"]] ["Not accepted: x"]
  let _ ← prove { stage := fun _ => { turns := 5 }, maxIterations := 1 } env file
  checkEq "default toolset: a rejection ends the iteration" ((← f.tools.get).map (·.1)).toList ["submit_working_file"]

end Test.Prove
