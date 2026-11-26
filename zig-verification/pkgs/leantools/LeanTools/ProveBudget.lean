import LeanTools.Ask

/-! Request cost bounds for the prover and its reflection. Amounts use pico-USD.
The h1 loop makes requests in sequence. The guard belongs to one run and both models share it.
Missing output limits or prices are refused before a request. Unknown costs retain their bound. -/

namespace LeanTools.ProveBudget

open Lean

structure Guard where
  total : Ask.Money
  spent : IO.Ref Ask.Money

def create (total : Ask.Money) : IO Guard := do
  return { total, spent := ← IO.mkRef ⟨0⟩ }

/-- A request must name its output limit. The complete request text also bounds tool schemas and replayed reasoning. -/
def bound (price : Ask.Price) (extra : Json) (msgs : Array Chat.Message) (tools : Array Json) : Except String Ask.Money := do
  let tokens ← (extra.getObjValAs? Nat "max_tokens").mapError (fun _ => "prove budget: extra.max_tokens must be a positive integer")
  if tokens == 0 then throw "prove budget: extra.max_tokens must be a positive integer"
  if extra.getObjValD "n" != .null && extra.getObjValD "n" != toJson (1 : Nat) then
    throw "prove budget: only one completion per request is supported"
  let bytes := (Chat.requestBody "" msgs tools extra).compress.utf8ByteSize + 16 * (msgs.size + tools.size + 1)
  pure (price.bound bytes tokens)

/-- One sequential h1 request. An unreported cost keeps the reservation. -/
def run (g : Guard) (price : Ask.Price) (extra : Json) (msgs : Array Chat.Message) (tools : Array Json)
    (request : IO (Except String Chat.Completion)) : IO (Except String Chat.Completion) := do
  let limit ← match bound price extra msgs tools with
    | .error e => return .error e
    | .ok b => pure b
  let spent ← g.spent.get
  if g.total.pico < spent.pico + limit.pico then
    return .error s!"prove budget: spent {spent} + request bound {limit} exceeds budgetUsd {g.total}"
  g.spent.set (spent + limit)
  let result ← try request catch e => pure (.error s!"request failed: {e}")
  if let .ok c := result then
    if c.usageKnown then
      let cost := price.cost c.usage
      g.spent.set (spent + cost)
      if limit.pico < cost.pico then return .error "prove budget: reported usage exceeds the request bound"
  return result

structure Prices where
  total : Ask.Money
  prover : Ask.Price
  reflection : Ask.Price

/-- Parse money once, with budgets rounded down and prices rounded up. -/
def prices (j : Json) : Except String Prices := do
  let total ← Ask.Money.parse false (if j.getObjValD "budgetUsd" == .null then toJson (20 : Nat) else j.getObjValD "budgetUsd")
  let p := j.getObjValD "price"
  let prover ← Ask.Price.parse p
  let r := (j.getObjValD "reflection").getObjValD "price"
  let reflection ← Ask.Price.parse (if r == .null then p else p.mergeObj r)
  pure { total, prover, reflection }

end LeanTools.ProveBudget
