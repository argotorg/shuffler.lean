import Std.Time
import LeanTools.Ask
import LeanTools.ProveMain

/-!
# `leantools ask --config PATH --budget PATH --max-usd X [--dry-run] [--system FILE] PROMPT_FILE|-`

One chat-completions request, guarded by the budget file (`docs/deepseek-budget.json`). The
config is the config of `prove` with `maxTokens` and `price` (`Ask.Config`). The reply text goes
to stdout, nothing else; stderr gets one line `ask: prompt_tokens=… cost_usd=… finish_reason=…`
after a call.

Exit status: 0 the reply is complete; 1 the call is refused (nothing is sent), the request failed,
or the cost is not recorded; 2 an argument, the config, the budget file or the key is wrong
(nothing is sent); 3 the reply is cut by `max_tokens` (`finish_reason=length`): the reply is
printed and its cost recorded. A reply with `finish_reason=error` is a failed call: status 1, with
its cost recorded.

The budget file is locked (`flock` on `PATH.lock`) for the check and for the record, not across the
request, so that calls run at the same time. The check reserves the cost bound of the call in the
file (`reservations`), and a check counts the reservations of the calls in flight: `spentUsd` +
reservations + bound is at most `budgetUsd`. The record removes the reservation and adds the cost.
A killed call leaves its reservation in the file; remove it by hand. The file is written to a
temporary file in the same directory and renamed. `--dry-run` sends nothing, locks nothing and changes nothing.

The record of a call is `.leantools/runs/<time>-ask-<pid>/` with `events.jsonl` and
`summary.json`. The `reply` event has the text and the reasoning text of the reply (the `reasoning`
or `reasoning_content` field of the response, as in `prove`). The config is redacted there as in
`prove`; the key is never written.
-/

open Lean

namespace LeanTools.Ask

structure Env where
  root : System.FilePath
  /-- The environment variable of the key. -/
  getEnv : String → IO (Option String) := fun k => IO.getEnv k
  /-- The wait between two attempts of a request; a test does not sleep. -/
  sleep : Nat → IO Unit := fun ms => IO.sleep ms.toUInt32

/-- What the command does: the status and the text for stdout and stderr. -/
structure Outcome where
  code : UInt32
  out : String := ""
  err : String := ""

private abbrev M := ExceptT Outcome IO

private def fail {α : Type} (code : UInt32) (msg : String) : M α := throw { code, err := msg ++ "\n" }

private def readText (what path : String) : M String := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok t => pure t
  | .error e => fail 2 s!"cannot read {what} {path}: {e}"

private def parseJsonFile (path text : String) : M Json :=
  match Json.parse text with
  | .ok j => pure j
  | .error e => fail 2 s!"{path}: {e}"

private def ofExcept {α : Type} (path : String) : Except String α → M α
  | .ok a => pure a
  | .error e => fail 2 s!"{path}: {e}"

/-- Write to a temporary file in the directory of `path`, then rename. -/
def writeAtomic (path : System.FilePath) (text : String) : IO Unit := do
  let tmp := System.FilePath.mk s!"{path}.tmp{← IO.Process.getPID}"
  IO.FS.writeFile tmp text
  IO.FS.rename tmp path

/-- Run `k` with the exclusive `flock` of `path`. The lock goes with the handle, so that a crash
leaves no stale lock. -/
def withLock {α : Type} (path : System.FilePath) (k : IO α) : IO α := do
  let h ← IO.FS.Handle.mk path .append
  h.lock
  try k finally h.unlock

private def messages (system : Option String) (prompt : String) : Array Chat.Message :=
  (system.map fun s => #[Chat.Message.system s]).getD #[] ++ #[.user prompt]

private def endpointOf (cfg : Config) (key : String) : OpenAI.Endpoint :=
  let e := cfg.prove.prover.endpoint cfg.prove key
  { e with extra := e.extra.mergeObj (Json.mkObj [("max_tokens", toJson cfg.maxTokens)]) }

private def readBudget (path : String) : M Budget := do
  ofExcept path (Budget.parse (← parseJsonFile path (← readText "budget file" path)))

/-- The time in UTC (the local zone may be unknown, as in a sandbox), with no `:` for a file name. -/
private def stamp : IO String := do
  let now := Std.Time.PlainDateTime.ofWallTime
    (Std.Time.WallTime.ofTimestamp (← Std.Time.Timestamp.now) Std.Time.TimeZone.Offset.zero)
  return ((toString now).map fun c => if c == ':' then '-' else c)

private def dryRun (a : Args) (body : Json) (promptTok : Nat) (cfg : Config) (bound : Money) : M Outcome := do
  let b ← readBudget a.budget
  let verdict := match decide b a.maxUsd bound with
    | .ok () => "ok"
    | .error r => s!"would refuse: {r.message}"
  return { code := 0, out := String.intercalate "\n" [
    "request body (credentials redacted):", (RunMetadata.redact body).pretty,
    s!"prompt_tokens_bound: {promptTok}", s!"max_tokens: {cfg.maxTokens}",
    s!"cost_bound_usd: {bound}", s!"max_usd: {a.maxUsd}", s!"spent_usd: {b.spent}",
    s!"budget_usd: {b.total}", s!"check: {verdict}", ""] }

/-- Runs `k` with the lock of the budget file. -/
private def locked {α : Type} (lockPath : System.FilePath) (k : M α) : M α := do
  match ← (withLock lockPath k.run).toBaseIO with
  | .ok (.ok a) => pure a
  | .ok (.error o) => throw o
  | .error e => fail 2 s!"cannot lock {lockPath}: {e}"

/-- The call itself. The budget file is locked for the check, which reserves the bound of the call
in the file, and again for the record, which replaces the reservation by the cost. The request runs
with no lock, so that calls run at the same time; the reservations keep the sum of the spend and
the bounds of the calls in flight within `budgetUsd`. -/
private def call (env : Env) (a : Args) (cfg : Config) (cfgJson : Json) (key : String)
    (msgs : Array Chat.Message) (promptSha : String) (promptTok : Nat) (bound : Money) : M Outcome := do
  let lockPath := System.FilePath.mk s!"{a.budget}.lock"
  let runName := s!"{← stamp}-ask-{← IO.Process.getPID}"
  let refusal ← locked lockPath do
    let b ← readBudget a.budget
    match decide b a.maxUsd bound with
    | .error r => pure (some r.message)
    | .ok () =>
      if let .error e ← (writeAtomic a.budget ((b.reserve runName bound).toJson.pretty ++ "\n")).toBaseIO then
        fail 1 s!"cannot reserve the cost bound in {a.budget}: {e}"
      pure none
  if let some msg := refusal then
    return { code := 1, err := msg ++ "\n" }
  let runDir := stateDir env.root / "runs" / runName
  IO.FS.createDirAll runDir
  let events ← IO.FS.Handle.mk (runDir / "events.jsonl") .write
  let log (j : Json) : IO Unit := do
    events.putStrLn (j.mergeObj (Json.mkObj [("ms", toJson (← IO.monoMsNow))])).compress
    events.flush
  let ep := endpointOf cfg key
  let model := ((Chat.requestModel ep.model ep.extra).getStr?).toOption.getD ep.model
  log (Json.mkObj [("event", "run-start"), ("config", RunMetadata.redact cfgJson),
    ("prompt_sha256", toJson promptSha), ("prompt_tokens_bound", toJson promptTok),
    ("cost_bound_usd", bound.toJson), ("max_usd", a.maxUsd.toJson)])
  let result ← OpenAI.complete ep msgs #[] env.sleep (onAttempt := fun attempt =>
    log (attempt.toJson.mergeObj (Json.mkObj [("event", "request-attempt"),
      ("operation", toJson "ask"), ("model", model)])))
  let time ← stamp
  -- the status, the text, and the entry for the budget
  let (code, text, reasoning, finish, usage, cost, known, error) :
      UInt32 × String × String × String × Chat.Usage × Money × Bool × Option String :=
    match result with
    | .ok c =>
      -- an endpoint that reports no usage is charged the bound
      let cost := if c.usageKnown then cfg.price.cost c.usage else bound
      -- the provider reports a failure that it charged for as `finish_reason=error`
      let code : UInt32 := if c.finishReason == "length" then 3 else if c.finishReason == "error" then 1 else 0
      (code, c.message.content, c.message.reasoning, c.finishReason, c.usage, cost, c.usageKnown, none)
    | .error e => (1, "", "", "error", {}, ⟨0⟩, true, some e)
  log (Json.mkObj [("event", "reply"), ("finish_reason", toJson finish), ("cost_usd", cost.toJson),
    ("text", toJson text), ("reasoning", toJson reasoning)])
  let entry := entry time model promptSha finish usage cost known runName error
  -- the summary is written first and its failure is only reported: the budget entry comes next
  let summary := (entry.mergeObj (Json.mkObj [
    ("outcome", toJson (if code == 0 then "ok" else if code == 3 then "length" else "error"))])).pretty ++ "\n"
  let summaryWarning := match ← (IO.FS.writeFile (runDir / "summary.json") summary).toBaseIO with
    | .ok () => ""
    | .error e => s!"warning: cannot write {runDir / "summary.json"}: {e}\n"
  -- the record: the reservation goes, the cost comes. The budget is read again, as other calls
  -- have changed it during the request
  let notRecorded (why : String) : Outcome :=
    { code := 1, out := text, err := summaryWarning ++ s!"the cost {cost} USD is NOT recorded in {a.budget}: {why}; see {runDir / "summary.json"}\n" }
  let settled : Except Outcome (Except String String) ← (locked lockPath do
    let b ← readBudget a.budget
    match ← (writeAtomic a.budget ((b.settle runName cost entry).toJson.pretty ++ "\n")).toBaseIO with
    | .ok () =>
      pure (Except.ok (if b.spent + cost ≤ b.total then "" else
        s!"warning: the cost {cost} is above the bound {bound}; spentUsd is above budgetUsd\n"))
    | .error e => pure (Except.error (toString e))).run
  let over ← match settled with
    | .error o => return notRecorded o.err.trimAscii.toString
    | .ok (.error e) => return notRecorded e
    | .ok (.ok over) => pure over
  let usageLine := s!"ask: prompt_tokens={usage.prompt} cached_tokens={usage.cached} completion_tokens={usage.completion} cost_usd={cost} finish_reason={finish}\n"
  return { code, out := text, err := usageLine ++ summaryWarning ++ over ++ (error.map (s!"request failed: " ++ · ++ "\n")).getD "" }

/-- The command, with its effects given by `env`. `stdin` is read only for the prompt `-`. -/
def run (env : Env) (a : Args) (stdin : IO String) : IO Outcome := do
  let r ← (do
    let cfgText ← readText "config" a.config
    let cfgJson ← parseJsonFile a.config cfgText
    let cfg ← ofExcept a.config (Config.parse cfgJson)
    let prompt ← match a.prompt with
      | .file p => readText "prompt" p
      | .stdin => stdin
    let system ← a.system.mapM (readText "system file")
    let msgs := messages system prompt
    let body ← ofExcept a.config ((endpointOf cfg "").requestBody msgs #[])
    let promptTok := promptBound (msgs.toList.map (·.content))
    let bound := cfg.price.bound promptTok cfg.maxTokens
    if a.dryRun then return ← dryRun a body promptTok cfg bound
    let some key ← env.getEnv cfg.prove.apiKeyEnv | fail 2 s!"set ${cfg.prove.apiKeyEnv} to the API key"
    -- the file must exist, so that a wrong path does not create a lock
    unless ← (System.FilePath.mk a.budget).pathExists do fail 2 s!"cannot read budget file {a.budget}: no such file"
    let sha ← RunMetadata.sha256 prompt
    call env a cfg cfgJson key msgs sha promptTok bound : M Outcome).run
  return match r with | .ok o => o | .error o => o

end LeanTools.Ask

namespace LeanTools

/-- `leantools ask ARGS`. -/
def runAsk (root : System.FilePath) (args : List String) : IO UInt32 := do
  match Ask.Args.parse args with
  | .error e =>
    IO.eprintln s!"leantools ask: {e}"
    IO.eprintln "usage: leantools ask --config PATH --budget PATH --max-usd X [--dry-run] [--system FILE] PROMPT_FILE|-"
    return 2
  | .ok a =>
    match ← (Ask.run { root } a (do (← IO.getStdin).readToEnd)).toBaseIO with
    | .ok o =>
      IO.print o.out
      IO.eprint o.err
      return o.code
    | .error e =>
      IO.eprintln s!"leantools ask: {e}"
      return 1

end LeanTools
