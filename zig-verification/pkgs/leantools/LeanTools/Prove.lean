import LeanTools.Chat
import LeanTools.Prompts
import LeanTools.RunMetadata

/-!
# The h1 loop

`prove` keeps a model at work on one working file until the validator accepts a submission or a
limit stops it (Moalla et al. 2026, Section 2.2):

1. An iteration is one conversation: the system prompt, then a user message with the original,
   from the second iteration the working file, the verifier's feedback, and the context of the
   reflection. The model reasons and calls tools for at most `turns` replies of the iteration's
   stage; each tool reply says how many turns are left. The stage's `extra` fields go into each
   request of the iteration (for example a reasoning effort for each iteration).
2. A call of `submit_working_file` ends the iteration; its later calls in the same reply do not
   run. At the turn limit the harness submits the file itself. A reply with no tool call gets one
   request to submit; then the harness submits.
3. After a rejected submission, if iterations remain, the reflection model condenses the attempt
   (its transcript, cut to `reflectionChars` characters) into the context of the next iteration.

The model, the reflection model, the tools and the files are parameters (`Env`), so that tests
can script them. The working file is fixed: the harness sets the `file` argument of each call of
a tool with a `file` parameter, and passes the other calls as the model sent them. A `Toolset`
changes the tool schemas, the name of the submit tool and the `file` rule, and can let the
iteration go on after a rejected submission (the coordinator's campaign worker does this).
-/

open Lean

namespace LeanTools.Prove

open Chat

/-- The settings of one iteration. -/
structure Stage where
  /-- Model replies. -/
  turns : Nat := 50
  /-- Fields of each prover request, merged at the top level of the body. -/
  extra : Json := Json.mkObj []

/-- The tools as the model sees them: without the `file` parameter, which the harness sets. -/
def modelTools : Array Json :=
  functionTools.map fun t =>
    let f := t.getObjValD "function"
    let p := f.getObjValD "parameters"
    let props := match p.getObjValD "properties" with
      | .obj kvs => Json.obj (kvs.erase "file")
      | j => j
    let req : Array Json := (p.getObjValD "required").getArr?.toOption.getD #[] |>.filter (· != "file")
    let p := (p.setObjVal! "properties" props).setObjVal! "required" (toJson req)
    t.setObjVal! "function" (f.setObjVal! "parameters" p)

/-- Whether the tool `name` has a `file` parameter, which the harness sets. -/
def takesFile (name : String) : Bool :=
  tools.any fun t => t.name == name && t.params.any (·.name == "file")

/-- The tools of an iteration. The defaults are the leantools tools of `leantools prove`: the
harness sets the `file` argument of a tool with a `file` parameter, and `submit_working_file` ends
the iteration. A caller can give other schemas, another submit tool, and the rule that a rejected
submission is a tool error with the iteration going on. -/
structure Toolset where
  /-- The tool schemas that the model sees. -/
  schemas : Array Json := modelTools
  /-- The name of the tool that ends the iteration. -/
  submit : String := "submit_working_file"
  /-- Whether the harness sets the `file` argument of a call of this tool. -/
  takesFile : String → Bool := takesFile
  /-- A rejected submission goes back to the model as a tool error, and the iteration goes on.
  A forced submission still ends the iteration. -/
  continueOnReject : Bool := false

/-- The provider's combined input/output window. The percentage applies after reserving output. -/
structure ContextLimit where
  window : Nat
  percent : Nat := 85
deriving Repr, BEq

def ContextLimit.inputLimit (c : ContextLimit) (extra : Json) : Nat :=
  (c.window - (extra.getObjValAs? Nat "max_tokens").toOption.getD 0) * c.percent / 100

structure Config where
  /-- The stage of iteration `i` (from 1). -/
  stage : Nat → Stage := fun _ => {}
  maxIterations : Nat := 100
  /-- The run stops before a model call once its cost reaches this. -/
  budgetUsd : Float := 20
  price : Price := {}
  reflectionPrice : Price := {}
  /-- The transcript that the reflection model sees is cut to this many characters. -/
  reflectionChars : Nat := 400000
  /-- Close an iteration before the next request reaches this input limit. -/
  context : Option ContextLimit := none
  /-- The prover's system prompt. -/
  system : String := Prompts.prover
  tools : Toolset := {}

structure Env where
  original : IO String
  /-- The check of the original when it was frozen: its errors and the goal at each `sorry`. -/
  originalCheck : String
  working : IO String
  proverModel : String := ""
  /-- The reflection request's model field, after its configured overrides. -/
  reflectionModel : Json := .null
  /-- A prover request with the stage's `extra` fields, the messages and the tools. -/
  prover : Json → Array Chat.Message → Array Json → IO (Except String Completion)
  reflector : Array Chat.Message → IO (Except String Completion)
  /-- A tool call, with the model's call id (`none` for a submission that the harness forces) and
  the `file` argument set for the tools with a `file` parameter; gives whether it succeeded and its
  reply. -/
  tool : Option String → String → Json → IO (Bool × String)
  /-- What is open in the working file (a check of its errors and `sorry`), or none when nothing is. It
  decides the message after a reply with no tool call: a file with something open is not a file to
  submit. -/
  openWork : IO (Option String) := pure none
  log : Json → IO Unit := fun _ => pure ()

inductive Outcome where
  | accepted (report : String)
  | budget
  | iterations
  | failed (why : String)
deriving Repr

def Outcome.name : Outcome → String
  | .accepted _ => "accepted" | .budget => "budget" | .iterations => "iterations" | .failed _ => "failed"

structure Summary where
  outcome : Outcome
  iterations : Nat
  /-- Prover replies, over all iterations. -/
  turns : Nat
  usage : Usage
  cost : Float
  /-- Prover request models in the order first used, including failed requests. -/
  models : Array Json := #[]

/-- A model name only when all prover requests used the same model. -/
def Summary.model (s : Summary) : Json :=
  if s.models.size == 1 then s.models[0]! else .null

def forcedTurns := "[NOTE: this submission was FORCED: the turn limit of the iteration was reached]"
def forcedSilent := "[NOTE: this submission was FORCED: the model ended its turn without calling a tool]"
def forcedContext (why : String) := s!"[NOTE: this submission was FORCED: {why}; reflect before the next iteration]"
def closeRequest (submit : String) :=
  s!"You ended your turn without calling any tool, so this iteration is being closed. Call {submit} now, with your reasoning."

/-- The message after a reply with no tool call, when `work` is open in the working file. It says what is open
and does not ask for a submission, which would be rejected. -/
def openRequest (submit work : String) :=
  s!"You ended your turn without calling any tool. The working file is not complete: {work} {submit} is rejected until nothing is open. Go on with the tools."

def lengthRequest := "Your reply reached the output limit (finish_reason=length). Its tool calls did not run. Send a complete tool call, with less text."

def firstMessage (file original check : String) (code? : Option String) (feedback context : String) :
    String :=
  let parts := [s!"The working file is `{file}`.", s!"<file>\n{original}\n</file>",
      s!"<initial-feedback>\n{check}\n</initial-feedback>"]
    ++ (code?.map fun c => [s!"<code>\n{c}\n</code>"]).getD []
    ++ (if feedback.isEmpty then [] else [s!"<verifier-feedback>\n{feedback}\n</verifier-feedback>"])
    ++ (if context.isEmpty then [] else [s!"<problem-experience>\n{context}\n</problem-experience>"])
  "\n\n".intercalate parts

def fileViews : List String := ["view_working_file", "view_original_file", "view_file"]

def fileLeftOut := "[file contents left out: the final code is in <final-attempt>; other files can be read again]"

/-- In a cut transcript, a reasoning keeps this many characters (its head and its tail), and a tool
reply its first this many. -/
def reasoningKeep : Nat := 3000
def replyKeep : Nat := 2000

/-- The head and the tail of `s`, `keep` characters in all, with a note of what is left out. -/
def clipMiddle (s : String) (keep : Nat) (what : String) : String :=
  if s.length ≤ keep then s
  else (s.take (keep / 2)).toString ++ s!"\n[... {s.length - keep} characters of {what} left out]\n"
    ++ (s.drop (s.length - keep / 2)).toString

/-- The head of `s`, with a note of what is left out. -/
def clipTail (s : String) (keep : Nat) (what : String) : String :=
  if s.length ≤ keep then s else (s.take keep).toString ++ s!"\n[... {s.length - keep} characters of {what} left out]"

/-- The transcript as text for the reflection model, without the system prompt (the reflection's
own prompt describes the setting). With more than `max` characters it is cut in steps, until it
fits: the replies of the file views are left out (the final code is in the reflection's input);
then each reasoning keeps its head and tail and each tool reply its head, so that each turn's
calls and the start of their results remain; then the middle turns are left out, so that the
first message and the last turns remain (Moalla et al. 2026, Appendix B.2). -/
def transcript (msgs : Array Chat.Message) (max : Nat) : String := Id.run do
  let msgs := msgs.filter (·.role != .system)
  let render (m : Chat.Message) : String :=
    let calls := m.toolCalls.toList.map fun c => s!"[tool call {c.name} {c.arguments}]"
    let head := match m.role with
      | .system => "### system" | .user => "### user" | .assistant => "### prover" | .tool => "### tool reply"
    let reasoning := if m.reasoning.isEmpty then [] else [s!"<reasoning>\n{m.reasoning}\n</reasoning>"]
    "\n".intercalate (head :: reasoning ++ m.content :: calls)
  let total (ps : Array String) := ps.foldl (· + ·.length) 0
  let fits (ps : Array String) := total ps + 2 * ps.size ≤ max
  let parts := msgs.map render
  if fits parts then return "\n\n".intercalate parts.toList
  let views := msgs.flatMap fun m => (m.toolCalls.filter (fileViews.contains ·.name)).map (·.id)
  let msgs := msgs.map fun m => if m.role == .tool && views.contains m.toolCallId then { m with content := fileLeftOut } else m
  let parts := msgs.map render
  if fits parts then return "\n\n".intercalate parts.toList
  -- the first message (the original and its check) stays whole
  let msgs := msgs.mapIdx fun i m =>
    if i == 0 then m
    else { m with reasoning := clipMiddle m.reasoning reasoningKeep "reasoning",
                  content := if m.role == .tool then clipTail m.content replyKeep "the reply" else m.content }
  let parts := msgs.map render
  if fits parts then return "\n\n".intercalate parts.toList
  -- keep the first message and as many of the last ones as fit
  let headParts := parts.extract 0 1
  let budget := max - min max (total headParts + 64)
  let mut tail : List String := []
  let mut used := 0
  for p in parts.extract 1 parts.size |>.reverse do
    if used + p.length + 2 > budget then break
    tail := p :: tail
    used := used + p.length + 2
  let omitted := parts.size - 1 - tail.length
  return "\n\n".intercalate (headParts.toList ++ [s!"[... {omitted} messages omitted ...]"] ++ tail)

structure Run where
  usage : Usage := {}
  cost : Float := 0
  turns : Nat := 0
  iterations : Nat := 0
  models : Array Json := #[]

/-- A tool call as the model sent it, for the run record: the arguments as JSON when they parse,
else as the raw text. -/
def callRecord (c : ToolCall) : Json :=
  Json.mkObj [("id", toJson c.id), ("name", toJson c.name),
    ("arguments", (Json.parse c.arguments).toOption.getD (toJson c.arguments))]

/-- Provider token counts already include the preceding request, tools and reasoning. Completion
tokens cover its assistant reply. New tool/user messages use UTF-8 bytes as a conservative estimate. -/
structure PromptEstimate where
  tokens : Nat
  messages : Nat
deriving Repr

def messageTokenBound (m : Chat.Message) : Nat := m.encode.compress.utf8ByteSize + 16

def PromptEstimate.next (p : PromptEstimate) (msgs : Array Chat.Message) : Nat :=
  p.tokens + (msgs.extract p.messages msgs.size).foldl (fun n m => n + messageTokenBound m) 0

/-- Recognize provider context refusals, not other HTTP 400 failures. -/
def isContextError (why : String) : Bool :=
  let s := why.toLower
  (s.startsWith "http 400:" || s.startsWith "http 413:") &&
    ["context_length_exceeded", "maximum context length", "combined input and output tokens",
     "input length exceeds the context"].any (fun marker => (s.splitOn marker).length > 1)

/-- One iteration; gives the submission's result and reasoning, and the transcript. -/
def iteration (cfg : Config) (stage : Stage) (env : Env) (file : String) (first : String) (run : IO.Ref Run) :
    IO (Except Outcome ((Bool × String) × String × Array Chat.Message)) := do
  let mut msgs := #[Chat.Message.system cfg.system, Chat.Message.user first]
  let mut asked := false
  let mut prompt : Option PromptEstimate := none
  let submit (id : Option String) (args : Json) : IO ((Bool × String) × String) := do
    let reasoning := (args.getObjValAs? String "reasoning").toOption.getD ""
    let r ← env.tool id cfg.tools.submit args
    env.log (Json.mkObj [("event", "submit"), ("id", toJson id), ("reasoning", toJson reasoning),
      ("accepted", toJson r.1), ("report", toJson r.2)])
    return (r, reasoning)
  let forced (note : String) :=
    submit none (Json.mkObj ((if cfg.tools.takesFile cfg.tools.submit then [("file", toJson file)] else [])
      ++ [("reasoning", toJson note)]))
  let contextEnd (msgs : Array Chat.Message) (why : String) (fields : List (String × Json)) := do
    env.log (Json.mkObj ([("event", toJson "context-limit"), ("reason", toJson why),
      ("iteration", toJson (← run.get).iterations)] ++ fields))
    let (r, reasoning) ← forced (forcedContext why)
    return Except.ok (r, reasoning, msgs)
  let model := Chat.requestModel env.proverModel stage.extra
  for k in [1:stage.turns + 1] do
    if (← run.get).cost ≥ cfg.budgetUsd then return .error .budget
    if let some limit := cfg.context then
      if let some p := prompt then
        let estimate := p.next msgs
        if estimate ≥ limit.inputLimit stage.extra then
          return ← contextEnd msgs "input context threshold reached"
            [("estimated_input_tokens", toJson estimate), ("input_limit_tokens", toJson (limit.inputLimit stage.extra)),
             ("context_window_tokens", toJson limit.window), ("context_percent", toJson limit.percent),
             ("output_reservation_tokens", stage.extra.getObjValD "max_tokens")]
    run.modify fun r => { r with models := if r.models.contains model then r.models else r.models.push model }
    let started ← IO.monoMsNow
    let c ← match ← env.prover stage.extra msgs cfg.tools.schemas with
      | .ok c => pure c
      | .error e =>
        if k > 1 && isContextError e then
          return ← contextEnd msgs "provider refused the input context" [("error", toJson e)]
        env.log (Json.mkObj [("event", toJson "request-failed"), ("error", toJson e),
          ("iteration", toJson (← run.get).iterations), ("turn", toJson k)])
        -- A completed local proof can survive a failed request for the next reply.
        -- Rejection or a local check error must keep the original request failure.
        if k > 1 && !isContextError e then
          try
            if (← env.openWork).isNone then
              let (r, reasoning) ← forced "The prover request failed. Check the saved working file before ending the run."
              if r.1 then return .ok (r, reasoning, msgs)
          catch checkError =>
            env.log (Json.mkObj [("event", toJson "failure-recovery-error"),
              ("error", toJson (toString checkError)), ("request_error", toJson e)])
        return .error (.failed e)
    run.modify fun r => { r with usage := r.usage + c.usage, cost := r.cost + cfg.price.cost c.usage, turns := r.turns + 1 }
    env.log (Json.mkObj [("event", "reply"), ("turn", toJson k), ("content", toJson c.message.content),
      ("iteration", toJson (← run.get).iterations), ("model", model),
      ("finish_reason", toJson c.finishReason), ("elapsed_ms", toJson ((← IO.monoMsNow) - started)),
      ("reasoning", toJson c.message.reasoning),
      ("tool_calls", toJson (c.message.toolCalls.map (·.name))), ("calls", toJson (c.message.toolCalls.map callRecord)),
      ("prompt_tokens", toJson c.usage.prompt), ("cached_tokens", toJson c.usage.cached),
      ("completion_tokens", toJson c.usage.completion)])
    msgs := msgs.push (if c.finishReason == "length" then { c.message with toolCalls := #[] } else c.message)
    let tokens := if c.usageKnown then c.usage.prompt + c.usage.completion else
        (msgs.foldl (fun n m => n + messageTokenBound m) 0) +
          (toJson cfg.tools.schemas).compress.utf8ByteSize
    prompt := some { tokens, messages := msgs.size }
    if c.finishReason == "length" then
      asked := false
      msgs := msgs.push (.user lengthRequest)
      continue
    if c.message.toolCalls.isEmpty then
      if asked then
        let (r, reasoning) ← forced forcedSilent
        return .ok (r, reasoning, msgs)
      asked := true
      msgs := msgs.push (.user (← match ← env.openWork with
        | some work => pure (openRequest cfg.tools.submit work)
        | none => pure (closeRequest cfg.tools.submit)))
      continue
    asked := false
    let left := stage.turns - k
    for call in c.message.toolCalls do
      match Json.parse call.arguments with
      | .ok (.obj kvs) =>
        let args := Json.obj (if cfg.tools.takesFile call.name then kvs.insert "file" (toJson file) else kvs)
        if call.name == cfg.tools.submit then
          let (r, reasoning) ← submit call.id args
          if r.1 || !cfg.tools.continueOnReject then
            return .ok (r, reasoning, msgs.push (.tool call.id r.2))
          msgs := msgs.push (.tool call.id s!"Error: {r.2}\n[{left} turns left in this iteration]")
        else
          let (ok, text) ← env.tool call.id call.name args
          env.log (Json.mkObj [("event", "tool"), ("id", toJson call.id), ("name", toJson call.name), ("ok", toJson ok)])
          msgs := msgs.push (.tool call.id s!"{if ok then "" else "Error: "}{text}\n[{left} turns left in this iteration]")
      | _ =>
        msgs := msgs.push (.tool call.id s!"Error: the arguments are not a JSON object: {call.arguments}\n[{left} turns left in this iteration]")
  let (r, reasoning) ← forced forcedTurns
  return .ok (r, reasoning, msgs)

def reflect (cfg : Config) (env : Env) (context reasoning feedback code : String) (msgs : Array Chat.Message)
    (run : IO.Ref Run) : IO String := do
  let input := "\n\n".intercalate [
    s!"<previous-context>\n{context}\n</previous-context>",
    s!"<final-attempt>\nThe prover's reasoning for its submission: {reasoning}\n\nIts final code:\n{code}\n\nThe verifier's feedback:\n{feedback}\n</final-attempt>",
    s!"<transcript>\n{transcript msgs cfg.reflectionChars}\n</transcript>"]
  let started ← IO.monoMsNow
  match ← env.reflector #[.system Prompts.reflection, .user input] with
  | .ok c =>
    run.modify fun r => { r with usage := r.usage + c.usage, cost := r.cost + cfg.reflectionPrice.cost c.usage }
    env.log (Json.mkObj [("event", "reflection"), ("content", toJson c.message.content),
      ("iteration", toJson (← run.get).iterations), ("model", env.reflectionModel),
      ("finish_reason", toJson c.finishReason), ("elapsed_ms", toJson ((← IO.monoMsNow) - started)),
      ("prompt_tokens", toJson c.usage.prompt), ("cached_tokens", toJson c.usage.cached),
      ("completion_tokens", toJson c.usage.completion), ("used", toJson (c.finishReason != "length"))])
    return if c.finishReason == "length" then context else c.message.content
  | .error e =>
    env.log (Json.mkObj [("event", "reflection-failed"), ("error", toJson e),
      ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
    return context

/-- Runs the iterations. An exception of the environment (a tool, a file) ends the run as
`failed`; the totals of the run so far are kept (in `run`: the assignments in a `try` block are lost
when it throws). -/
def prove (cfg : Config) (env : Env) (file : String) : IO Summary := do
  let run ← IO.mkRef ({} : Run)
  let mut context := ""
  let mut feedback := ""
  let mut outcome := Outcome.iterations
  try
    let original ← env.original
    for i in [1:cfg.maxIterations + 1] do
      run.modify ({ · with iterations := i })
      let stage := cfg.stage i
      env.log (Json.mkObj [("event", "iteration"), ("iteration", toJson i), ("turns", toJson stage.turns),
        ("extra", RunMetadata.redact stage.extra)])
      let working ← env.working
      let code? := if i == 1 && working == original then none else some working
      match ← iteration cfg stage env file (firstMessage file original env.originalCheck code? feedback context) run with
      | .error o => outcome := o; break
      | .ok ((accepted, report), reasoning, msgs) =>
        if accepted then outcome := .accepted report; break
        feedback := report
        if i < cfg.maxIterations then
          context ← reflect cfg env context reasoning report (← env.working) msgs run
  catch e => outcome := .failed (toString e)
  let r ← run.get
  return { outcome, iterations := r.iterations, turns := r.turns, usage := r.usage,
           cost := r.cost, models := r.models }

end LeanTools.Prove
