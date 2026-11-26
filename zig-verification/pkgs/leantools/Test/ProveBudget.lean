import LeanTools.ProveBudget
import Test.Harness

namespace Test.ProveBudget

open Lean LeanTools

def suite : T Unit := do
  let price : Ask.Price := { input := 0, cachedInput := 0, output := 1 }
  let extra := Json.mkObj [("max_tokens", toJson (10 : Nat))]
  let calls ← IO.mkRef 0
  let request : IO (Except String Chat.Completion) := do
    calls.modify (· + 1)
    return .ok { message := .assistant "", finishReason := "stop", usage := { completion := 6 } }
  let g ← LeanTools.ProveBudget.create ⟨15⟩
  check "first bounded call runs" (← LeanTools.ProveBudget.run g price extra #[] #[] request).isOk
  check "a call that can cross the cap is refused" (← LeanTools.ProveBudget.run g price extra #[] #[] request).toOption.isNone
  checkEq "refused call makes no request" (← calls.get) 1
  checkEq "cost is exact" (← g.spent.get).pico 6
  let g ← LeanTools.ProveBudget.create ⟨100⟩
  check "missing token bound is refused" (← LeanTools.ProveBudget.run g price (Json.mkObj []) #[] #[] request).toOption.isNone
  check "zero token bound is refused" (← LeanTools.ProveBudget.run g price
    (Json.mkObj [("max_tokens", toJson (0 : Nat))]) #[] #[] request).toOption.isNone
  check "multiple completions are refused" (← LeanTools.ProveBudget.run g price
    (extra.setObjVal! "n" (toJson (2 : Nat))) #[] #[] request).toOption.isNone
  let g ← LeanTools.ProveBudget.create ⟨10⟩
  let failed : IO (Except String Chat.Completion) := pure (.error "lost response")
  let _ ← LeanTools.ProveBudget.run g price extra #[] #[] failed
  checkEq "an unknown request cost keeps its bound" (← g.spent.get).pico 10
  let g ← LeanTools.ProveBudget.create ⟨10⟩
  let unknown : IO (Except String Chat.Completion) := pure (.ok {
    message := .assistant "", finishReason := "stop", usage := {}, usageKnown := false })
  let _ ← LeanTools.ProveBudget.run g price extra #[] #[] unknown
  checkEq "a reply without usage keeps its bound" (← g.spent.get).pico 10
  let g ← LeanTools.ProveBudget.create ⟨100⟩
  let p : Ask.Price := { input := 1, cachedInput := 1, output := 0 }
  check "tool schema bytes enter the request bound" (← LeanTools.ProveBudget.run g p extra #[]
    #[Json.mkObj [("description", toJson (String.ofList (List.replicate 120 'x')))]] request).toOption.isNone
  let g ← LeanTools.ProveBudget.create ⟨100⟩
  check "reasoning bytes enter the request bound" (← LeanTools.ProveBudget.run g p extra
    #[.assistant "" #[] (String.ofList (List.replicate 120 'x'))] #[] request).toOption.isNone
  let config := Json.mkObj [("budgetUsd", Json.num ⟨12345678901239, 13⟩),
    ("price", Json.mkObj [("input", toJson (1 : Nat)), ("output", toJson (2 : Nat))])]
  match LeanTools.ProveBudget.prices config with
  | .error e => check "prices parse" false e
  | .ok ps =>
    checkEq "budget rounds down" ps.total.pico 1234567890123
    checkEq "reflection price defaults to prover price" ps.reflection ps.prover
  check "missing prices are refused before a request" (LeanTools.ProveBudget.prices (Json.mkObj [])).toOption.isNone

end Test.ProveBudget
