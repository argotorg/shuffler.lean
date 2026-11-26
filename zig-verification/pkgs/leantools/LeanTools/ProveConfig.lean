import Lean.Data.Json
import LeanTools.Chat
import LeanTools.Prove

/-!
# The configuration of `leantools prove`

A JSON object; a missing field keeps its default:

    { "baseUrl": "https://api.openai.com/v1", "model": "…", "apiKeyEnv": "OPENAI_API_KEY",
      "extra": {"reasoning_effort": "high"},
      "price": {"input": 1.25, "cachedInput": 0.125, "output": 10},
      "reflection": {"model": "…", "extra": {…}, "price": {…}},
      "turns": 50, "maxIterations": 100, "budgetUsd": 20, "reflectionChars": 400000,
      "contextWindow": 1048576, "contextPercent": 85,
      "timeoutSeconds": 900, "maxRetries": 8, "primer": "KRAKEN.md",
      "schedule": [{"turns": 40, "extra": {"reasoning_effort": "low"}}, {"turns": 100}] }

`timeoutSeconds` is the timeout of one request. Without it, the timeout is `timeoutFor` of the
largest `max_tokens` of `extra`, of the schedule items and of the reflection (120 s and 1 s for each
100 tokens), or 900 s when there is no `max_tokens`. Prices are USD per million tokens. `schedule` gives the stage of each iteration: item `i` holds
for iteration `i`, the last item for the later iterations. An item's `extra` is merged over the
top-level `extra` (a key of the item replaces that key); its `turns` defaults to the top-level
`turns`. Without `schedule`, each iteration has the top-level `turns` and `extra`. `primer` is a file, relative to the project root, that becomes
the last section of the prover's system prompt. The reflection model defaults to the prover's model, extra
fields and prices.

`contextWindow` enables an input checkpoint. Each stage first reserves its `extra.max_tokens`;
`contextPercent` (default 85) is the fraction of the remaining input capacity. At that threshold,
the loop submits the current file and reflects after rejection. It completes all tool calls in
the current reply before the checkpoint. A recognized provider context error after the first
reply follows the same path. The existing iteration and budget limits still apply.
-/

open Lean

namespace LeanTools.ProveConfig

structure Model where
  model : String
  extra : Json := Json.mkObj []
  price : Chat.Price := {}

structure Config where
  baseUrl : String := "https://api.openai.com/v1"
  apiKeyEnv : String := "OPENAI_API_KEY"
  prover : Model
  reflection : Model
  loop : Prove.Config
  timeoutSeconds : Nat := 900
  maxRetries : Nat := 8
  primer : Option String := none

/-- The request timeout in seconds for a reply of at most `tokens` tokens: 120 s, and 1 s for each
100 tokens (the provider writes at least 100 tokens/s). -/
def timeoutFor (tokens : Nat) : Nat := 120 + (tokens + 99) / 100

/-- The timeout when the config has no `max_tokens` and no `timeoutSeconds`. -/
def defaultTimeoutSeconds : Nat := 900

/-- The largest `max_tokens` of the `extra` of the config, of its schedule items and of its
reflection. -/
def requestTokens (j : Json) : Option Nat :=
  let extras := [j.getObjValD "extra", (j.getObjValD "reflection").getObjValD "extra"]
    ++ ((j.getObjValD "schedule").getArr?.toOption.getD #[]).toList.map (·.getObjValD "extra")
  (extras.filterMap fun e => (e.getObjValD "max_tokens").getNat?.toOption).max?

def opt {α : Type} [FromJson α] (j : Json) (k : String) (dflt : α) : Except String α :=
  match j.getObjValD k with
  | .null => .ok dflt
  | v => (fromJson? v).mapError (s!"{k}: " ++ ·)

def parsePrice (j : Json) (dflt : Chat.Price) : Except String Chat.Price := do
  match j with
  | .null => return dflt
  | j => return { input := ← opt j "input" dflt.input, cachedInput := ← opt j "cachedInput" dflt.cachedInput,
                  output := ← opt j "output" dflt.output }

/-- A schedule item over the top-level stage `top`. -/
def parseStage (top : Prove.Stage) (j : Json) : Except String Prove.Stage := do
  let kvs ← j.getObj?
  if let some k := kvs.toArray.map (·.1) |>.find? (!["turns", "extra"].contains ·) then
    throw s!"unknown key {k}"
  let extra ← match j.getObjValD "extra" with
    | .null => pure top.extra
    | e@(.obj _) => pure (top.extra.mergeObj e)
    | _ => throw "extra must be an object"
  return { turns := ← opt j "turns" top.turns, extra }

/-- The stage of each iteration: the items of `schedule` (the last one repeats), else `top`. -/
def parseSchedule (top : Prove.Stage) : Json → Except String (Nat → Prove.Stage)
  | .null => pure fun _ => top
  | .arr items => do
    let stages ← items.mapM (parseStage top)
    match stages.back? with
    | none => throw "the list is empty"
    | some last => pure fun i => stages.getD (i - 1) last
  | _ => throw "a list of stages is expected"

def parse (j : Json) : Except String Config := do
  let model ← match j.getObjValD "model" with
    | .str m => pure m
    | .null => throw "model is required"
    | _ => throw "model must be a string"
  let extra := match j.getObjValD "extra" with | .null => Json.mkObj [] | e => e
  let price ← (parsePrice (j.getObjValD "price") {}).mapError ("price: " ++ ·)
  let r := j.getObjValD "reflection"
  let reflection : Model := {
    model := ← opt r "model" model
    extra := match r.getObjValD "extra" with | .null => extra | e => e
    price := ← (parsePrice (r.getObjValD "price") price).mapError ("reflection.price: " ++ ·) }
  let d : Prove.Config := {}
  let top : Prove.Stage := { turns := ← opt j "turns" (d.stage 1).turns, extra }
  let stage ← (parseSchedule top (j.getObjValD "schedule")).mapError ("schedule: " ++ ·)
  let context ← match j.getObjValD "contextWindow" with
    | .null =>
      if j.getObjValD "contextPercent" != .null then
        throw "contextPercent: requires contextWindow"
      pure none
    | value => do
      let window ← (fromJson? value : Except String Nat).mapError ("contextWindow: " ++ ·)
      let percent ← opt j "contextPercent" (85 : Nat)
      if window == 0 then throw "contextWindow: must be positive"
      if percent == 0 || percent > 100 then throw "contextPercent: must be between 1 and 100"
      let stages := match j.getObjValD "schedule" with
        | .arr items => items.toList.mapIdx (fun i _ => stage (i + 1))
        | _ => [top]
      for s in stages do
        let output ← (s.extra.getObjValAs? Nat "max_tokens").mapError
          (fun _ => "contextWindow: each stage needs a positive extra.max_tokens")
        if output == 0 || output ≥ window then
          throw "contextWindow: each stage's max_tokens must be positive and smaller than contextWindow"
        if (window - output) * percent / 100 == 0 then
          throw "contextPercent: leaves no input tokens after output reservation"
      pure (some { window, percent } : Option Prove.ContextLimit)
  let timeoutSeconds ← opt j "timeoutSeconds" ((requestTokens j).elim defaultTimeoutSeconds timeoutFor)
  if timeoutSeconds == 0 then throw "timeoutSeconds: must be at least 1"
  return {
    baseUrl := ← opt j "baseUrl" "https://api.openai.com/v1"
    apiKeyEnv := ← opt j "apiKeyEnv" "OPENAI_API_KEY"
    prover := { model, extra, price }
    reflection
    loop := { stage, maxIterations := ← opt j "maxIterations" d.maxIterations,
              budgetUsd := ← opt j "budgetUsd" d.budgetUsd, price, reflectionPrice := reflection.price,
              reflectionChars := ← opt j "reflectionChars" d.reflectionChars, context }
    timeoutSeconds
    maxRetries := ← opt j "maxRetries" 8
    primer := ← opt j "primer" none }

end LeanTools.ProveConfig
