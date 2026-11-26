import Std.Time
import LeanTools.Daemon
import LeanTools.OpenAI
import LeanTools.ProveConfig
import LeanTools.ProveBudget
import LeanTools.RunMetadata

/-!
# `leantools prove FILE [--config PATH]`

Runs the h1 loop on one working file of the project. The tools go through the project's daemon,
so several runs share one Lean server; the model is an OpenAI chat-completions endpoint. The run
record goes to `.leantools/runs/<time>-<file>/`: `events.jsonl` (each reply, tool call,
submission and reflection) and `summary.json`.
-/

open Lean

namespace LeanTools

def ProveConfig.Model.endpoint (m : ProveConfig.Model) (c : ProveConfig.Config) (key : String) :
    OpenAI.Endpoint :=
  { baseUrl := c.baseUrl, apiKey := key, model := m.model, extra := m.extra,
    timeoutMs := c.timeoutSeconds * 1000, maxRetries := c.maxRetries }

def runProve (root : System.FilePath) (file : String) (configPath : System.FilePath) : IO UInt32 := do
  let fail (msg : String) : IO UInt32 := do IO.eprintln s!"leantools prove: {msg}"; return 2
  let file ← match resolveIn root file with
    | .ok f => pure f
    | .error e => return ← fail e
  unless ← configPath.pathExists do return ← fail s!"no config file {configPath}"
  let configText ← IO.FS.readFile configPath
  let configJson ← match Json.parse configText with
    | .ok j => pure j
    | .error e => return ← fail s!"{configPath}: {e}"
  let cfg ← match ProveConfig.parse configJson with
    | .ok c => pure c
    | .error e => return ← fail s!"{configPath}: {e}"
  let prices ← match ProveBudget.prices configJson with
    | .ok p => pure p
    | .error e => return ← fail s!"{configPath}: {e}"
  let guard ← ProveBudget.create prices.total
  let some key ← IO.getEnv cfg.apiKeyEnv | return ← fail s!"set ${cfg.apiKeyEnv} to the API key"
  let primer ← match cfg.primer with
    | none => pure ""
    | some p =>
      unless ← (root / p).pathExists do return ← fail s!"no primer file {p}"
      pure (← IO.FS.readFile (root / p))
  let system := if cfg.primer.isSome then Prompts.withPrimer Prompts.prover primer else Prompts.prover
  -- the first tool call freezes the original
  let r ← call root "view_original_file" (Json.mkObj [("file", toJson file)])
  let text := (r.getObjValD "text").getStr?.toOption.getD r.compress
  unless (r.getObjValD "ok") == .bool true do return ← fail text
  let originalCheck := ((text.splitOn originalCheckHeader).getLast?).getD ""
  let stamp := ((toString (← Std.Time.PlainDateTime.now)).map fun c => if c == ':' then '-' else c)
  let runDir := stateDir root / "runs" / s!"{stamp}-{file.replace "/" "_"}"
  IO.FS.createDirAll runDir
  let events ← IO.FS.Handle.mk (runDir / "events.jsonl") .write
  let lock ← Std.Mutex.new ()
  let log (j : Json) : IO Unit := lock.atomically do
    events.putStrLn (j.mergeObj (Json.mkObj [("ms", toJson (← IO.monoMsNow))])).compress
    events.flush
  let hashes := (← RunMetadata.source root).mergeObj (Json.mkObj [
    ("config_sha256", toJson (← RunMetadata.sha256 configText)),
    ("prompt_sha256", toJson (← RunMetadata.sha256 system)),
    ("reflection_prompt_sha256", toJson (← RunMetadata.sha256 Prompts.reflection)),
    ("primer_sha256", toJson (← RunMetadata.sha256 primer)),
    ("tools_sha256", toJson (← RunMetadata.sha256 (toJson Prove.modelTools).compress))])
  log (hashes.mergeObj (Json.mkObj [("event", "run-start"), ("config", RunMetadata.redact configJson)]))
  let complete (operation : String) (price : Ask.Price) (endpoint : OpenAI.Endpoint) (msgs : Array Chat.Message)
      (tools : Array Json) : IO (Except String Chat.Completion) :=
    ProveBudget.run guard price endpoint.extra msgs tools <| OpenAI.complete endpoint msgs tools (onAttempt := fun attempt =>
      log (attempt.toJson.mergeObj (Json.mkObj [("event", "request-attempt"),
        ("operation", toJson operation), ("model", Chat.requestModel endpoint.model endpoint.extra)])))
  let env : Prove.Env := {
    original := IO.FS.readFile (stateDir root / "orig" / file)
    originalCheck
    working := IO.FS.readFile (root / file)
    proverModel := cfg.prover.model
    reflectionModel := Chat.requestModel cfg.reflection.model cfg.reflection.extra
    prover := fun extra msgs tools => complete "prover" prices.prover { cfg.prover.endpoint cfg key with extra } msgs tools
    reflector := fun msgs => complete "reflection" prices.reflection (cfg.reflection.endpoint cfg key) msgs #[]
    tool := fun id name args => do
      let r ← call root name args
      let text := (r.getObjValD "text").getStr?.toOption.getD r.compress
      log (Json.mkObj [("event", "tool-reply"), ("id", toJson id), ("name", toJson name), ("text", toJson text)])
      return ((r.getObjValD "ok") == .bool true, text)
    log }
  IO.println s!"leantools prove {file}: initial model {(Chat.requestModel cfg.prover.model (cfg.loop.stage 1).extra).compress}, run record {runDir}"
  let s ← Prove.prove { cfg.loop with system } env file
  let report := match s.outcome with
    | .accepted r => r
    | .failed why => why
    | _ => ""
  let accounted ← guard.spent.get
  let summary := hashes.mergeObj (Json.mkObj [("file", toJson file), ("outcome", toJson s.outcome.name), ("report", toJson report),
    ("iterations", toJson s.iterations), ("turns", toJson s.turns), ("prompt_tokens", toJson s.usage.prompt),
    ("cached_tokens", toJson s.usage.cached), ("completion_tokens", toJson s.usage.completion),
    ("cost_usd", accounted.toJson), ("reported_cost_usd", toJson s.cost), ("model", s.model), ("models", toJson s.models),
    ("configured_model", toJson cfg.prover.model)])
  IO.FS.writeFile (runDir / "summary.json") (summary.pretty ++ "\n")
  IO.println s!"{s.outcome.name} after {s.iterations} iterations, {s.turns} turns, {accounted} USD"
  unless report.isEmpty do IO.println report
  return if s.outcome.name == "accepted" then 0 else 1

end LeanTools
