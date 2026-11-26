import Lean.Data.Json
import LeanTools.Chat
import LeanTools.ProveConfig

/-!
# `leantools ask`: the data

The pure part of `leantools ask`: money, the price, the bound of the cost of one call, the budget
file, the arguments and the configuration. `LeanTools.AskMain` does the IO.

Money is a natural number of pico-USD (10⁻¹² USD), so that the sums and the comparisons with the
budget are exact. A number of a file is read once, at the boundary, into `Money` or `Price`, with
the rounding that is safe for the use: a budget is rounded down, a spend and a price up.

The bound of the cost of a call is

    promptBound * max(price.input, price.cachedInput) + maxTokens * price.output

where `promptBound` is the UTF-8 size in bytes of the texts of the messages plus 16 for each
message (a token has at least one byte; the 16 is for the framing of the chat template).
-/

open Lean

namespace LeanTools.Ask

/-- An amount in units of 10⁻¹² USD. -/
structure Money where
  pico : Nat
deriving DecidableEq, Repr, Inhabited

instance : Add Money := ⟨fun a b => ⟨a.pico + b.pico⟩⟩
instance : LE Money := ⟨fun a b => a.pico ≤ b.pico⟩
instance (a b : Money) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.pico ≤ b.pico))

/-- Exact decimal text (USD) of the amount, for example `0.003412345678`. -/
def Money.toJson (m : Money) : Json := .num ⟨m.pico, 12⟩

instance : ToString Money := ⟨fun m => (m.toJson).compress⟩

/-- `n * 10^shift`, rounded up or down to a natural number. The exponent is bounded so that the
file cannot make an arbitrarily large power. -/
def scaled (n : JsonNumber) (shift : Nat) (up : Bool) : Except String Nat := do
  if n.mantissa < 0 then throw "the number is negative"
  if n.exponent > 100 then throw "the number has more than 100 decimals"
  let m := n.mantissa.toNat
  if n.exponent ≤ shift then return m * 10 ^ (shift - n.exponent)
  let d := 10 ^ (n.exponent - shift)
  return if up then (m + d - 1) / d else m / d

def numberOf : Json → Except String JsonNumber
  | .num n => .ok n
  | _ => .error "a number is expected"

/-- A USD amount of a file. -/
def Money.parse (up : Bool) (j : Json) : Except String Money := do
  return ⟨← scaled (← numberOf j) 12 up⟩

/-- A USD amount of text, as the argument `--max-usd` gives it. Rounded down. -/
def Money.ofText (s : String) : Except String Money := do
  match Json.parse s with
  | .ok j@(.num _) => Money.parse false j
  | _ => throw s!"{s.quote} is not a number"

/-- Prices in pico-USD for one token. -/
structure Price where
  input : Nat
  cachedInput : Nat
  output : Nat
deriving Repr, BEq

/-- The object `{"input": …, "output": …, "cachedInput": …}` of USD for one million tokens, as
in the config of `prove`. `cachedInput` is optional and then equals `input`. Rounded up. -/
def Price.parse (j : Json) : Except String Price := do
  let field (k : String) : Except String Nat := do
    match j.getObjValD k with
    | .null => throw s!"price.{k} is required"
    | v => (do scaled (← numberOf v) 6 true).mapError (s!"price.{k}: " ++ ·)
  let input ← field "input"
  let cachedInput ← match j.getObjValD "cachedInput" with
    | .null => pure input
    | _ => field "cachedInput"
  return { input, cachedInput, output := ← field "output" }

/-- The cost of the tokens that an endpoint reported. -/
def Price.cost (p : Price) (u : Chat.Usage) : Money :=
  ⟨(u.prompt - u.cached) * p.input + u.cached * p.cachedInput + u.completion * p.output⟩

/-- The bound of the prompt tokens of the message texts. -/
def promptBound (texts : List String) : Nat :=
  texts.foldl (fun n s => n + s.utf8ByteSize + 16) 0

/-- The bound of the cost of a call: at most `promptBound` prompt tokens and `maxTokens` tokens of
reply. -/
def Price.bound (p : Price) (promptBound maxTokens : Nat) : Money :=
  ⟨promptBound * max p.input p.cachedInput + maxTokens * p.output⟩

/-- The configuration of `ask`: the config of `prove` (endpoint, model, `extra`, time-out,
retries) with a price and a limit for the tokens of the reply. -/
structure Config where
  prove : ProveConfig.Config
  price : Price
  /-- Sent as `max_tokens`; replaces a `max_tokens` of `extra`. -/
  maxTokens : Nat

def Config.parse (j : Json) : Except String Config := do
  let prove ← ProveConfig.parse j
  let price ← (Price.parse (j.getObjValD "price")).mapError ("price: " ++ ·)
  let maxTokens ← match j.getObjValD "maxTokens" with
    | .null => throw "maxTokens is required"
    | v => (fromJson? (α := Nat) v).mapError ("maxTokens: " ++ ·)
  if maxTokens == 0 then throw "maxTokens must be at least 1"
  -- `maxTokens` replaces `extra.max_tokens`, so the default timeout follows it
  let prove := if j.getObjValD "timeoutSeconds" == .null
    then { prove with timeoutSeconds := ProveConfig.timeoutFor maxTokens } else prove
  return { prove, price, maxTokens }

/-- The budget file. `rest` holds its other fields (`note`), kept as they are. `runs` holds the
entries as written by `ask` or by another tool. -/
structure Budget where
  total : Money
  spent : Money
  runs : Array Json
  rest : List (String × Json)
  /-- The bound of each call in flight, by run name: a call reserves its bound before the request and
  the record replaces it by the cost. A killed call leaves its reservation in the file. -/
  reservations : Array (String × Money) := #[]

/-- The sum of the reservations. -/
def Budget.reserved (b : Budget) : Money := b.reservations.foldl (fun m r => m + r.2) ⟨0⟩

def Budget.parse (j : Json) : Except String Budget := do
  let kvs ← j.getObj?
  let field (k : String) : Except String Json :=
    match j.getObjVal? k with
    | .ok v => .ok v
    | .error _ => .error s!"{k} is missing"
  let total ← (Money.parse false (← field "budgetUsd")).mapError ("budgetUsd: " ++ ·)
  let spent ← (Money.parse true (← field "spentUsd")).mapError ("spentUsd: " ++ ·)
  let runs ← match ← field "runs" with
    | .arr a => pure a
    | _ => throw "runs: a list is expected"
  let reservations ← match j.getObjValD "reservations" with
    | .null => pure #[]
    | .arr a => a.mapM fun r => do
      let run ← (r.getObjValAs? String "run").mapError ("reservations: run: " ++ ·)
      let bound ← (Money.parse true (r.getObjValD "boundUsd")).mapError ("reservations: boundUsd: " ++ ·)
      pure (run, bound)
    | _ => throw "reservations: a list is expected"
  let rest := kvs.toArray.toList.filter fun (k, _) => !["budgetUsd", "spentUsd", "runs", "reservations"].contains k
  return { total, spent, runs, rest, reservations }

/-- The file keeps the `reservations` field only while a call is in flight. -/
def Budget.toJson (b : Budget) : Json :=
  Json.mkObj (b.rest ++ [("budgetUsd", b.total.toJson), ("spentUsd", b.spent.toJson), ("runs", .arr b.runs)]
    ++ (if b.reservations.isEmpty then [] else
      [("reservations", .arr (b.reservations.map fun (run, bound) =>
        Json.mkObj [("run", .str run), ("boundUsd", bound.toJson)]))]))

/-- The budget after one call: the cost is added to `spentUsd` and the entry to `runs`. -/
def Budget.record (b : Budget) (cost : Money) (entry : Json) : Budget :=
  { b with spent := b.spent + cost, runs := b.runs.push entry }

/-- The budget with the bound of the call `run` reserved. -/
def Budget.reserve (b : Budget) (run : String) (bound : Money) : Budget :=
  { b with reservations := b.reservations.push (run, bound) }

/-- The budget after the call `run`: its reservation is removed, the cost and the entry are
recorded. -/
def Budget.settle (b : Budget) (run : String) (cost : Money) (entry : Json) : Budget :=
  { b with reservations := b.reservations.filter (·.1 != run) }.record cost entry

/-- Why a call does not start. -/
inductive Refusal where
  | overMax (maxUsd bound : Money)
  | overBudget (spent bound total : Money)
  | overReserved (spent reserved bound total : Money)

def Refusal.message : Refusal → String
  | .overMax m b => s!"refused: --max-usd {m} is below the cost bound {b}"
  | .overBudget s b t => s!"refused: spentUsd {s} + cost bound {b} is above budgetUsd {t}"
  | .overReserved s r b t =>
    s!"refused: spentUsd {s} + reserved {r} (calls in flight) + cost bound {b} is above budgetUsd {t}"

/-- A call starts only if its bound is within `--max-usd` and within what is left of the budget after
the spend and the reservations of the calls in flight. -/
def decide (b : Budget) (maxUsd bound : Money) : Except Refusal Unit :=
  if ¬ bound ≤ maxUsd then .error (.overMax maxUsd bound)
  else if b.spent + b.reserved + bound ≤ b.total then .ok ()
  else if b.reserved == ⟨0⟩ then .error (.overBudget b.spent bound b.total)
  else .error (.overReserved b.spent b.reserved bound b.total)

/-- The entry of `runs` for one call. -/
def entry (time model promptSha finish : String) (u : Chat.Usage) (cost : Money)
    (usageKnown : Bool) (run : String) (error : Option String) : Json :=
  Json.mkObj ([("time", toJson time), ("model", toJson model), ("promptSha256", toJson promptSha),
    ("promptTokens", toJson u.prompt), ("cachedTokens", toJson u.cached),
    ("completionTokens", toJson u.completion), ("costUsd", cost.toJson),
    ("finishReason", toJson finish), ("run", toJson run)]
    ++ (if usageKnown then [] else [("usageKnown", toJson false)])
    ++ (error.map fun e => [("error", toJson e)]).getD [])

inductive Source where
  | file (path : String)
  | stdin

structure Args where
  config : String
  budget : String
  maxUsd : Money
  dryRun : Bool
  system : Option String
  prompt : Source

private structure Partial where
  config : Option String := none
  budget : Option String := none
  maxUsd : Option Money := none
  dryRun : Bool := false
  system : Option String := none
  prompt : Option Source := none

private def Args.go (p : Partial) : List String → Except String Partial
  | [] => .ok p
  | "--dry-run" :: rest => Args.go { p with dryRun := true } rest
  | "--config" :: v :: rest => Args.go { p with config := some v } rest
  | "--budget" :: v :: rest => Args.go { p with budget := some v } rest
  | "--system" :: v :: rest => Args.go { p with system := some v } rest
  | "--max-usd" :: v :: rest => do Args.go { p with maxUsd := some (← Money.ofText v) } rest
  | f :: rest =>
    if f.startsWith "--" then .error s!"unknown or incomplete option {f}"
    else if p.prompt.isSome then .error "more than one prompt"
    else Args.go { p with prompt := some (if f == "-" then .stdin else .file f) } rest

/-- The arguments after `ask`. -/
def Args.parse (args : List String) : Except String Args := do
  let p ← Args.go {} args
  let some config := p.config | throw "--config is required"
  let some budget := p.budget | throw "--budget is required"
  let some maxUsd := p.maxUsd | throw "--max-usd is required"
  let some prompt := p.prompt | throw "a prompt file, or - for stdin, is required"
  return { config, budget, maxUsd, dryRun := p.dryRun, system := p.system, prompt }

end LeanTools.Ask
