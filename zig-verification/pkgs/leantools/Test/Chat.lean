import LeanTools.Chat
import Test.Harness

/-! Tests of the OpenAI chat-completions types: the request body, and the parse of responses. -/

open Lean LeanTools Chat Test

namespace Test.Chat

def completion (s : String) : Except String Completion := Json.parse s >>= parseCompletion

def toolCallReply := "{\"id\": \"c1\", \"choices\": [{\"index\": 0, \"finish_reason\": \"tool_calls\",
  \"message\": {\"role\": \"assistant\", \"content\": null, \"tool_calls\": [
    {\"id\": \"call_1\", \"type\": \"function\", \"function\": {\"name\": \"lean_goal\", \"arguments\": \"{\\\"file\\\": \\\"A.lean\\\", \\\"line\\\": 3}\"}},
    {\"id\": \"call_2\", \"type\": \"function\", \"function\": {\"name\": \"grep\", \"arguments\": \"{\\\"pattern\\\": \\\"x\\\"}\"}}]}}],
  \"usage\": {\"prompt_tokens\": 1200, \"completion_tokens\": 80,
    \"prompt_tokens_details\": {\"cached_tokens\": 1024}, \"completion_tokens_details\": {\"reasoning_tokens\": 50}}}"

def textReply := "{\"choices\": [{\"finish_reason\": \"stop\", \"message\": {\"role\": \"assistant\", \"content\": \"Done.\"}}],
  \"usage\": {\"prompt_tokens\": 10, \"completion_tokens\": 2}}"

/-- A text reply whose reasoning is in the message field `field`. -/
def reasoningReply (field : String) : String :=
  (Json.mkObj [("choices", Json.arr #[Json.mkObj [("finish_reason", "stop"), ("message", Json.mkObj [
    ("role", "assistant"), ("content", "No."), (field, "91 = 7 × 13, not prime.")])]]),
    ("usage", Json.mkObj [])]).compress

/-- The message `i` of a request body. -/
def bodyMessage (body : Json) (i : Nat) : Json :=
  ((body.getObjValD "messages").getArr?.toOption.getD #[])[i]?.getD Json.null

def suite : T Unit := do
  -- parse: the reasoning, under either name; empty without it
  for field in ["reasoning", "reasoning_content"] do
    match completion (reasoningReply field) with
    | .error e => check s!"parse {field}" false e
    | .ok c => checkEq s!"parse {field}" (c.message.content, c.message.reasoning) ("No.", "91 = 7 × 13, not prime.")
  checkEq "parse without reasoning" ((completion textReply).toOption.map (·.message.reasoning)) (some "")
  let both := Json.mkObj [("choices", Json.arr #[Json.mkObj [("message", Json.mkObj [
    ("role", "assistant"), ("content", "No."), ("reasoning", ""), ("reasoning_content", "RC")])]])]
  checkEq "parse empty reasoning, then reasoning_content" ((parseCompletion both).toOption.map (·.message.reasoning)) (some "RC")
  checkEq "parse other field" ((completion (reasoningReply "thoughts")).toOption.map (·.message.reasoning)) (some "")
  -- parse: tool calls, in order, with their arguments as JSON text
  match completion toolCallReply with
  | .error e => check "parse tool calls" false e
  | .ok c =>
    checkEq "tool call names" (c.message.toolCalls.map (·.name)) #["lean_goal", "grep"]
    checkEq "tool call ids" (c.message.toolCalls.map (·.id)) #["call_1", "call_2"]
    checkEq "tool call arguments" ((c.message.toolCalls[0]?.map (·.arguments)).bind fun a =>
      (Json.parse a).toOption.bind (·.getObjValAs? Nat "line" |>.toOption)) (some 3)
    checkEq "no content" c.message.content ""
    checkEq "finish reason" c.finishReason "tool_calls"
    checkEq "usage" (c.usage.prompt, c.usage.cached, c.usage.completion) (1200, 1024, 80)
    checkEq "known usage and cache counts" (c.usageKnown, c.cachedKnown) (true, true)
  match completion textReply with
  | .error e => check "parse text" false e
  | .ok c =>
    checkEq "text content" c.message.content "Done."
    checkEq "no tool calls" c.message.toolCalls.size 0
    checkEq "usage without details" (c.usage.prompt, c.usage.cached, c.usage.completion) (10, 0, 2)
    checkEq "known usage without cache details" (c.usageKnown, c.cachedKnown) (true, false)
  checkEq "missing usage is unknown" ((completion (reasoningReply "reasoning")).toOption.map (·.usageKnown)) (some false)
  check "no choices is an error" (completion "{\"choices\": []}" |>.toOption |>.isNone)
  let clipped := r#"{"choices":[{"finish_reason":"length","message":{"content":"part","tool_calls":[{"function":{"arguments":"{"}}]}}],"usage":{"completion_tokens":7}}"#
  match completion clipped with
  | .error e => check "length: malformed calls keep completion metadata" false e
  | .ok c =>
    checkEq "length: calls do not run" c.message.toolCalls #[]
    checkEq "length: metadata" (c.finishReason, c.usage.completion, c.message.content) ("length", 7, "part")
  check "an error object is an error"
    (match completion "{\"error\": {\"message\": \"bad key\"}}" with
     | .error e => e.startsWith "bad key"
     | .ok _ => false)
  -- the request body: model, messages in order, tools, extra fields
  let msgs : Array Chat.Message := #[.system "S", .user "U",
    .assistant "" #[{ id := "call_1", name := "grep", arguments := "{}" }], .tool "call_1" "R"]
  let tools := #[Json.mkObj [("type", "function")]]
  let body := requestBody "m1" msgs tools (Json.mkObj [("reasoning_effort", "high")])
  checkEq "model" (body.getObjValAs? String "model" |>.toOption) (some "m1")
  checkEq "request model: configured name" (requestModel "m1" (Json.mkObj [])).compress "\"m1\""
  checkEq "request model: extra override"
    (requestModel "m1" (Json.mkObj [("model", "m2")])).compress "\"m2\""
  checkEq "request model: preserve an invalid field"
    (requestModel "m1" (Json.mkObj [("model", .null)])).compress "null"
  checkEq "extra field" (body.getObjValAs? String "reasoning_effort" |>.toOption) (some "high")
  checkEq "tools" ((body.getObjValD "tools").getArr?.toOption.map (·.size)) (some 1)
  let roles := ((body.getObjValD "messages").getArr?.toOption.getD #[]).map fun m =>
    (m.getObjValAs? String "role").toOption.getD "?"
  checkEq "roles" roles #["system", "user", "assistant", "tool"]
  let m2 := ((body.getObjValD "messages").getArr?.toOption.getD #[])[2]!
  checkEq "assistant tool call id" ((m2.getObjValD "tool_calls").getArrVal? 0 |>.toOption |>.bind
    (·.getObjValAs? String "id" |>.toOption)) (some "call_1")
  let m3 := ((body.getObjValD "messages").getArr?.toOption.getD #[])[3]!
  checkEq "tool message id" (m3.getObjValAs? String "tool_call_id" |>.toOption) (some "call_1")
  check "assistant without reasoning: no field" ((m2.getObjVal? "reasoning").toOption.isNone) m2.compress
  -- the reasoning goes back in its assistant message, with the tool calls and a null content
  let calls := #[{ id := "call_1", name := "grep", arguments := "{}" : ToolCall }]
  let m := bodyMessage (requestBody "m1" #[.assistant "" calls "R1"] #[] (Json.mkObj [])) 0
  checkEq "assistant with reasoning" (m.getObjValAs? String "reasoning" |>.toOption, (m.getObjValD "content").isNull,
    (m.getObjValD "tool_calls").getArr?.toOption.map (·.size)) (some "R1", true, some 1)
  checkEq "assistant text with reasoning" (bodyMessage (requestBody "m1" #[.assistant "T" #[] "R2"] #[] (Json.mkObj [])) 0).compress
    r#"{"content":"T","reasoning":"R2","role":"assistant"}"#
  -- no tools: no tools field (some servers reject an empty array)
  check "no tools field" ((requestBody "m1" msgs #[] (Json.mkObj [])).getObjValD "tools").isNull
  -- the tool schemas of leantools as OpenAI functions
  let fs := functionTools
  checkEq "all tools" fs.size LeanTools.tools.size
  checkEq "function name" ((fs[0]?.map fun f => (f.getObjValD "function").getObjValAs? String "name" |>.toOption).join)
    (some "view_working_file")
  check "parameters are a JSON schema" ((fs[0]?.map fun f =>
    ((f.getObjValD "function").getObjValD "parameters").getObjValAs? String "type" |>.toOption).join == some "object")
  -- cost: uncached input, cached input and output at their own prices (USD per million tokens)
  let price : Price := { input := 2.0, cachedInput := 0.5, output := 10.0 }
  checkEq "cost" (price.cost { prompt := 1200, cached := 1024, completion := 80 })
    ((176 * 2.0 + 1024 * 0.5 + 80 * 10.0) / 1000000)

end Test.Chat
