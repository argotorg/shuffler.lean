import LeanTools.ProveConfig
import Test.Harness

open Lean LeanTools ProveConfig Test

namespace Test.ProveConfig

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def parseS (s : String) : Except String ProveConfig.Config := Json.parse s >>= parse

def suite : T Unit := do
  match parseS "{\"model\": \"m\"}" with
  | .error e => check "defaults" false e
  | .ok c =>
    checkEq "defaults: base URL" c.baseUrl "https://api.openai.com/v1"
    checkEq "defaults: key variable" c.apiKeyEnv "OPENAI_API_KEY"
    checkEq "defaults: loop" ((c.loop.stage 1).turns, c.loop.maxIterations) (50, 100)
    checkEq "defaults: reflection model" c.reflection.model "m"
  match parseS "{\"model\": \"m\", \"extra\": {\"reasoning_effort\": \"high\"}, \"turns\": 10,
      \"price\": {\"input\": 2, \"output\": 8}, \"reflection\": {\"model\": \"r\"}, \"budgetUsd\": 3.5}" with
  | .error e => check "fields" false e
  | .ok c =>
    checkEq "turns" (c.loop.stage 1).turns 10
    checkEq "budget" c.loop.budgetUsd 3.5
    checkEq "extra" (c.prover.extra.getObjValAs? String "reasoning_effort" |>.toOption) (some "high")
    checkEq "reflection model" c.reflection.model "r"
    checkEq "reflection keeps the prover's extra" (c.reflection.extra.getObjValAs? String "reasoning_effort" |>.toOption) (some "high")
    checkEq "price" (c.prover.price.input, c.prover.price.cachedInput, c.prover.price.output) (2.0, 0.0, 8.0)
    checkEq "reflection price defaults to the prover's" c.loop.reflectionPrice.output 8.0
  check "model is required" (match parseS "{}" with | .error e => e == "model is required" | .ok _ => false)
  check "a wrong type is an error" (match parseS "{\"model\": \"m\", \"turns\": \"x\"}" with
    | .error e => e.startsWith "turns:" | .ok _ => false)
  checkEq "no primer" (match parseS "{\"model\": \"m\"}" with | .ok c => c.primer | .error _ => some "x") none
  checkEq "primer" (match parseS "{\"model\": \"m\", \"primer\": \"KRAKEN.md\"}" with
    | .ok c => c.primer | .error _ => none) (some "KRAKEN.md")
  -- the schedule: item i holds for iteration i, the last item for the later ones; an item's `extra`
  -- is merged over the top-level `extra` (a key of the item replaces the key), its `turns`
  -- defaults to the top-level `turns`
  let stage (c : ProveConfig.Config) (i : Nat) := ((c.loop.stage i).turns, (c.loop.stage i).extra.compress)
  match parseS "{\"model\": \"m\", \"turns\": 7, \"extra\": {\"a\": 1, \"reasoning\": {\"effort\": \"low\"}}}" with
  | .error e => check "no schedule" false e
  | .ok c =>
    checkEq "no schedule: each iteration has the top-level fields" [stage c 1, stage c 2, stage c 9]
      (List.replicate 3 (7, r#"{"a":1,"reasoning":{"effort":"low"}}"#))
    checkEq "no schedule: the prover's extra" c.prover.extra.compress r#"{"a":1,"reasoning":{"effort":"low"}}"#
  match parseS "{\"model\": \"m\", \"turns\": 7, \"extra\": {\"a\": 1, \"reasoning\": {\"effort\": \"low\"}},
      \"schedule\": [{\"turns\": 40, \"extra\": {\"reasoning\": {\"effort\": \"high\"}}},
                     {\"extra\": {\"reasoning\": {\"effort\": \"max\"}}}]}" with
  | .error e => check "schedule" false e
  | .ok c =>
    checkEq "schedule: iteration 1" (stage c 1) (40, r#"{"a":1,"reasoning":{"effort":"high"}}"#)
    checkEq "schedule: iteration 2, turns from the top level" (stage c 2) (7, r#"{"a":1,"reasoning":{"effort":"max"}}"#)
    checkEq "schedule: the last item holds after it" (stage c 5) (stage c 2)
    checkEq "schedule: the reflection keeps the top-level extra" c.reflection.extra.compress
      r#"{"a":1,"reasoning":{"effort":"low"}}"#
  check "an empty schedule is an error" (match parseS "{\"model\": \"m\", \"schedule\": []}" with
    | .error e => e.startsWith "schedule:" | .ok _ => false)
  check "a schedule that is not a list is an error" (match parseS "{\"model\": \"m\", \"schedule\": {}}" with
    | .error e => e.startsWith "schedule:" | .ok _ => false)
  check "a wrong type in a schedule item is an error" (match parseS "{\"model\": \"m\", \"schedule\": [{\"turns\": \"x\"}]}" with
    | .error e => e.startsWith "schedule:" | .ok _ => false)
  check "an unknown key in a schedule item is an error" (match parseS "{\"model\": \"m\", \"schedule\": [{\"turn\": 3}]}" with
    | .error e => e.startsWith "schedule:" | .ok _ => false)
  -- the request timeout: 120 s and 1 s for each 100 tokens of `max_tokens`, unless it is given
  let timeout (s : String) : Option Nat := (parseS s).toOption.map (·.timeoutSeconds)
  checkEq "timeoutFor" ([0, 1, 100, 101, 8192, 65536, 393216].map timeoutFor) [120, 121, 121, 122, 202, 776, 4053]
  forAll "timeoutFor: at least 1 s for 100 tokens, and monotone" 300 11
    (fun g => let (a, g) := below 1000000 g; let (b, g) := below 1000000 g; ((a, b), g))
    fun (a, b) => timeoutFor a * 100 ≥ a && (a ≤ b → timeoutFor a ≤ timeoutFor b)
  checkEq "timeout: no max_tokens, the old default" (timeout "{\"model\": \"m\"}") (some 900)
  checkEq "timeout: scales with max_tokens"
    (timeout "{\"model\": \"m\", \"extra\": {\"max_tokens\": 393216}}") (some 4053)
  checkEq "timeout: given, it stays"
    (timeout "{\"model\": \"m\", \"timeoutSeconds\": 300, \"extra\": {\"max_tokens\": 393216}}") (some 300)
  checkEq "timeout: the largest max_tokens of the stages counts"
    (timeout "{\"model\": \"m\", \"extra\": {\"max_tokens\": 1000},
      \"schedule\": [{}, {\"extra\": {\"max_tokens\": 65536}}], \"reflection\": {\"extra\": {\"max_tokens\": 8192}}}")
    (some 776)
  checkEq "timeout: the reflection's max_tokens counts"
    (timeout "{\"model\": \"m\", \"extra\": {\"max_tokens\": 1000}, \"reflection\": {\"extra\": {\"max_tokens\": 65536}}}")
    (some 776)
  check "timeout: 0 is an error" (match parseS "{\"model\": \"m\", \"timeoutSeconds\": 0}" with
    | .error e => e.startsWith "timeoutSeconds:" | .ok _ => false)
  let context (s : String) := (parseS s).toOption.bind (·.loop.context)
  checkEq "context: disabled by default" (context r#"{"model":"m"}"#) none
  checkEq "context: default percent" (context r#"{"model":"m","contextWindow":1048576,"extra":{"max_tokens":393216}}"#)
    (some { window := 1048576, percent := 85 })
  for percent in [1, 85, 100] do
    let j := Json.mkObj [("model", toJson "m"), ("contextWindow", toJson (1000 : Nat)),
      ("contextPercent", toJson percent), ("extra", Json.mkObj [("max_tokens", toJson (100 : Nat))])]
    checkEq s!"context: valid percent {percent}" ((parse j).toOption.bind (·.loop.context))
      (some { window := 1000, percent })
  for j in [r#"{"model":"m","contextPercent":85}"#,
      r#"{"model":"m","contextWindow":0,"extra":{"max_tokens":10}}"#,
      r#"{"model":"m","contextWindow":1000,"contextPercent":0,"extra":{"max_tokens":10}}"#,
      r#"{"model":"m","contextWindow":1000,"contextPercent":101,"extra":{"max_tokens":10}}"#,
      r#"{"model":"m","contextWindow":1000,"extra":{"max_tokens":0}}"#,
      r#"{"model":"m","contextWindow":1000,"extra":{"max_tokens":1000}}"#,
      r#"{"model":"m","contextWindow":1000,"extra":{"max_tokens":2000}}"#,
      r#"{"model":"m","contextWindow":1000}"#,
      r#"{"model":"m","contextWindow":"large","extra":{"max_tokens":10}}"#,
      r#"{"model":"m","contextWindow":1000,"extra":{"max_tokens":"large"}}"#,
      r#"{"model":"m","contextWindow":1000,"extra":{"max_tokens":10},"schedule":[{}, {"extra":{"max_tokens":1001}}]}"#,
      r#"{"model":"m","contextWindow":2,"contextPercent":1,"extra":{"max_tokens":1}}"#] do
    check "context: reject invalid settings" (!(parseS j).isOk) j
  check "context: stages may supply all output limits"
    (parseS r#"{"model":"m","contextWindow":1000,"schedule":[{"extra":{"max_tokens":100}},{"extra":{"max_tokens":200}}]}"#).isOk
  check "the primer section" (has (Prompts.withPrimer "P" "PRIMER-TEXT") "P\n\n# Project background\n\nPRIMER-TEXT")

end Test.ProveConfig
