import LeanTools.OpenAI
import Test.Harness

open Lean LeanTools Test

namespace Test.Anthropic

private instance : Repr Json where
  reprPrec j _ := j.compress

def blocks : Array Json := #[
  Json.mkObj [("type", "thinking"), ("thinking", "Check."), ("signature", "signed")],
  Json.mkObj [("type", "redacted_thinking"), ("data", "opaque")],
  Json.mkObj [("type", "tool_use"), ("id", "toolu_1"), ("name", "check"), ("input", Json.mkObj [])],
  Json.mkObj [("type", "tool_use"), ("id", "toolu_2"), ("name", "view"), ("input", Json.mkObj [])]]

def response : Json := Json.mkObj [("type", "message"), ("role", "assistant"),
  ("content", toJson blocks), ("stop_reason", "tool_use"),
  ("usage", Json.mkObj [("input_tokens", toJson (10 : Nat)),
    ("cache_creation_input_tokens", toJson (20 : Nat)),
    ("cache_read_input_tokens", toJson (70 : Nat)), ("output_tokens", toJson (30 : Nat))])]

def suite : T Unit := do
  let extra := LeanTools.Anthropic.defaultExtra.mergeObj (Json.mkObj [("max_tokens", toJson (1024 : Nat))])
  let tools := #[Json.mkObj [("type", "function"), ("function", Json.mkObj [
    ("name", "check"), ("description", "Check."),
    ("parameters", Json.mkObj [("type", "object"), ("properties", Json.mkObj [])])])]]
  let start := #[Chat.Message.system "System.", .user "Task."]
  let body := (LeanTools.Anthropic.requestBody "sonnet" start tools extra).toOption.getD .null
  check "API tag parses" (fromJson? (α := OpenAI.Api) (toJson "anthropicMessages")).isOk
  checkEq "automatic cache control" ((body.getObjValD "cache_control").getObjValD "type") (toJson "ephemeral")
  checkEq "native tool schema" (((body.getObjValD "tools").getArr?.toOption.getD #[])[0]!.getObjValD "input_schema")
    ((tools[0]!.getObjValD "function").getObjValD "parameters")
  checkEq "system is separate" (((body.getObjValD "system").getArr?.toOption.getD #[])[0]!.getObjValD "text") (toJson "System.")
  for key in ["messages", "system", "model", "tools", "stream", "cache_control"] do
    check ("reject caller override: " ++ key)
      (!(LeanTools.Anthropic.requestBody "sonnet" start tools (extra.setObjVal! key (toJson "override"))).isOk)
  for invalid in [Json.mkObj [], extra.setObjVal! "max_tokens" (toJson (0 : Nat)),
      extra.setObjVal! "max_tokens" (toJson "1024")] do
    check "output bound is required and positive" (!(LeanTools.Anthropic.requestBody "sonnet" start tools invalid).isOk)
  match LeanTools.Anthropic.parseCompletion response with
  | .error error => check "parse native completion" false error
  | .ok result =>
    checkEq "total input includes writes and reads" result.usage.prompt 100
    checkEq "cache counters" (result.usage.cached, result.cacheCreation) (70, 20)
    check "usage is known" (result.usageKnown && result.cachedKnown)
    checkEq "tool IDs" (result.message.toolCalls.map (·.id)) #["toolu_1", "toolu_2"]
    let next := (LeanTools.Anthropic.requestBody "sonnet"
      (start ++ #[result.message, .tool "toolu_1" "Checked.", .tool "toolu_2" "Source."])
      tools extra).toOption.getD .null
    let messages := (next.getObjValD "messages").getArr?.toOption.getD #[]
    checkEq "assistant blocks are unchanged" (messages[1]!.getObjValD "content") (toJson blocks)
    let results := (messages[2]!.getObjValD "content").getArr?.toOption.getD #[]
    checkEq "all tool results share a user message" (messages.size, results.size) (3, 2)
    checkEq "tool result matches its call" (results[1]!.getObjValD "tool_use_id") (toJson "toolu_2")
  for stop in ["max_tokens", "model_context_window_exceeded"] do
    let limited := (LeanTools.Anthropic.parseCompletion (response.setObjVal! "stop_reason" (toJson stop))).toOption
    checkEq "incomplete calls cannot execute" (limited.map fun c => (c.finishReason, c.message.toolCalls.size)) (some ("length", 0))
    check "incomplete calls cannot enter history" (limited.all fun c => c.message.responseItems.all
      (fun block => block.getObjValD "type" != toJson "tool_use"))
  -- A refusal is no decision: its tool calls do not run and do not enter the history.
  let refused := (LeanTools.Anthropic.parseCompletion (response.setObjVal! "stop_reason" (toJson "refusal"))).toOption
  checkEq "a refusal cannot execute tools" (refused.map fun c => (c.finishReason, c.message.toolCalls.size)) (some ("refusal", 0))
  check "a refusal keeps no tool call in the history" (refused.all fun c => c.message.responseItems.all
    (fun block => block.getObjValD "type" != toJson "tool_use"))
  let missing := (LeanTools.Anthropic.parseCompletion (response.setObjVal! "usage" .null)).toOption
  checkEq "missing usage stays unknown" (missing.map (·.usageKnown)) (some false)
  let malformed := (response.getObjValD "usage").setObjVal! "cache_read_input_tokens" (toJson "70")
  checkEq "malformed usage stays unknown"
    ((LeanTools.Anthropic.parseCompletion (response.setObjVal! "usage" malformed)).toOption.map (·.usageKnown)) (some false)
  for invalid in [Json.null, response.setObjVal! "stop_reason" .null,
      response.setObjVal! "content" (toJson #[Json.mkObj [("type", "unknown")]]),
      response.setObjVal! "content" (toJson #[blocks[2]!.setObjVal! "input" (toJson "bad")]),
      Json.mkObj [("type", "error"), ("error", Json.mkObj [("message", "denied")])]] do
    check "invalid responses cannot execute tools" (!(LeanTools.Anthropic.parseCompletion invalid).isOk)

end Test.Anthropic
