import LeanTools.OpenAI
import Test.Http

open Lean LeanTools Test

namespace Test.Responses

private instance : Repr Json where
  reprPrec j _ := j.compress

def message : Json := Json.mkObj [
  ("type", "message"), ("id", "msg_1"), ("role", "assistant"), ("phase", "commentary"),
  ("status", "completed"), ("content", toJson #[Json.mkObj [("type", "output_text"), ("text", "Check it.")]])]

def reasoning : Json := Json.mkObj [
  ("type", "reasoning"), ("id", "rs_1"), ("summary", toJson (#[] : Array Json)),
  ("encrypted_content", "opaque-reasoning")]

def call : Json := Json.mkObj [
  ("type", "function_call"), ("id", "fc_1"), ("call_id", "call_1"),
  ("namespace", "lean"), ("name", "check"), ("arguments", "{}"), ("status", "completed")]

def response (status : String := "completed") : Json := Json.mkObj [
  ("status", toJson status), ("output", toJson #[reasoning, message, call]),
  ("usage", Json.mkObj [("input_tokens", toJson (100 : Nat)),
    ("input_tokens_details", Json.mkObj [("cached_tokens", toJson (80 : Nat))]),
    ("output_tokens", toJson (20 : Nat))])]

def event (kind : String) (r : Json) : String :=
  "event: " ++ kind ++ "\ndata: " ++ (Json.mkObj [("type", toJson kind), ("response", r)]).compress ++ "\n\n"

def suite : T Unit := do
  checkEq "old task records use Chat Completions"
    ((fromJson? (α := OpenAI.Api) Json.null).toOption) (some .chatCompletions)
  check "unknown API is rejected" (!(fromJson? (α := OpenAI.Api) (toJson "unknown")).isOk)
  let routing : LeanTools.Responses.Routing := { sessionId := "session-1" }
  let tools := #[Json.mkObj [("type", "function"), ("function", Json.mkObj [
    ("name", "check"), ("description", "Check the file."),
    ("parameters", Json.mkObj [("type", "object"), ("properties", Json.mkObj [])])])]]
  let msgs := #[Chat.Message.system "S", .user "U"]
  let body := (LeanTools.Responses.requestBody "m1" msgs tools (Json.mkObj []) routing).toOption.getD .null
  checkEq "SIWC request flags" (body.getObjValD "store", body.getObjValD "stream") (.bool false, .bool true)
  checkEq "cache key" (body.getObjValD "prompt_cache_key") (toJson "session-1")
  checkEq "reasoning is requested" (body.getObjValD "include") (toJson #["reasoning.encrypted_content"])
  let input := (body.getObjValD "input").getArr?.toOption.getD #[]
  checkEq "system instructions use developer role" (input[0]!.getObjValD "role") (toJson "developer")
  let ns := ((body.getObjValD "tools").getArr?.toOption.getD #[])[0]!
  checkEq "tools use a namespace" (ns.getObjValD "type", ns.getObjValD "name") (toJson "namespace", toJson "lean")
  checkEq "namespaced function name"
    (((ns.getObjValD "tools").getArr?.toOption.getD #[])[0]!.getObjValD "name") (toJson "check")
  for key in ["store", "stream", "model", "input", "tools", "include", "prompt_cache_key",
      "previous_response_id", "conversation", "background", "max_output_tokens", "max_tool_calls",
      "metadata", "moderation", "multi_agent", "prompt", "prompt_cache_retention", "safety_identifier",
      "temperature", "top_logprobs", "top_p", "truncation", "user", "messages", "reasoning_effort",
      "max_tokens", "max_completion_tokens"] do
    check ("reject extra: " ++ key)
      (!(LeanTools.Responses.requestBody "m1" msgs tools (Json.mkObj [(key, toJson "override")]) routing).isOk)
  match LeanTools.Responses.parseStream (event "response.completed" (response "completed")) with
  | .error e => check "completed stream" false e
  | .ok c =>
    checkEq "usage" (c.usage.prompt, c.usage.cached, c.usage.completion) (100, 80, 20)
    check "usage is known" (c.usageKnown && c.cachedKnown)
    checkEq "call IDs differ from item IDs" (c.message.toolCalls.map (·.id)) #["call_1"]
    checkEq "output items are retained" c.message.responseItems #[reasoning, message, call]
    let next := (LeanTools.Responses.requestBody "m1" (msgs ++ #[c.message, .tool "call_1" "ok"])
      tools (Json.mkObj []) routing).toOption.getD .null
    let history := (next.getObjValD "input").getArr?.toOption.getD #[]
    checkEq "output history is replayed without changes" (history.extract 2 5) #[reasoning, message, call]
    checkEq "tool result uses call ID" (history[5]!.getObjValD "call_id") (toJson "call_1")
  let stream := ": ping\r\n\r\n" ++ (event "response.completed" (response "completed")).replace "\n" "\r\n" ++ "data: [DONE]\r\n\r\n"
  check "CRLF and comments" (LeanTools.Responses.parseStream stream).isOk
  for stream in ["", "data: [DONE]\n\n", "data: {bad}\n\n",
      ((event "response.completed" (response "completed")).dropEnd 1).toString,
      event "response.failed" (Json.mkObj [("error", Json.mkObj [("message", "denied")])]),
      event "response.incomplete" (response "incomplete")] do
    check "failed or interrupted stream is not a success" (!(LeanTools.Responses.parseStream stream).isOk)
  let nestedError := Json.mkObj [("type", "error"), ("error", Json.mkObj [
    ("code", "subscription_sharing_unsupported_capability"), ("message", "Unsupported tool."),
    ("param", "tools")])]
  match LeanTools.Responses.parseStream ("data: " ++ nestedError.compress ++ "\n\n") with
  | .error e =>
    check "nested error retains code" (e.startsWith "subscription_sharing_unsupported_capability") e
    check "nested error retains message and parameter" (e.endsWith "Unsupported tool. (param: tools)") e
  | .ok _ => check "nested error is rejected" false
  let missingError := Json.mkObj [("type", "response.failed"), ("response", Json.mkObj [
    ("id", "resp_failed"), ("status", "failed"), ("error", .null)])]
  match LeanTools.Responses.parseStream ("data: " ++ missingError.compress ++ "\n\n") with
  | .error e => check "failure without an error retains event details" (e.endsWith missingError.compress) e
  | .ok _ => check "failure without an error is rejected" false
  let limited := (response "incomplete").mergeObj (Json.mkObj [
    ("incomplete_details", Json.mkObj [("reason", "max_output_tokens")])])
  let c := (LeanTools.Responses.parseStream (event "response.incomplete" limited)).toOption
  checkEq "length limit suppresses calls" (c.map fun c => (c.finishReason, c.message.toolCalls.size)) (some ("length", 0))
  let completed := event "response.completed" (response "completed")
  check "duplicate terminal events are rejected"
    (!(LeanTools.Responses.parseStream (completed ++ completed)).isOk)
  let unknown := (response "completed").mergeObj (Json.mkObj [("usage", .null)])
  let usage := (LeanTools.Responses.parseStream (event "response.completed" unknown)).toOption
  checkEq "missing usage remains unknown" (usage.map fun c => (c.usageKnown, c.cachedKnown)) (some (false, false))
  let wrongNamespace := (response "completed").mergeObj (Json.mkObj [
    ("output", toJson #[call.mergeObj (Json.mkObj [("namespace", "other")])])])
  check "unknown namespace is rejected"
    (!(LeanTools.Responses.parseStream (event "response.completed" wrongNamespace)).isOk)
  forAll "history replay preserves escaped and Unicode text" 200 421
    (randString #['a', '"', '\\', '\n', 'λ', '⊢'] 80) fun text =>
      let raw := #[reasoning.mergeObj (Json.mkObj [("encrypted_content", toJson text)]),
        message.mergeObj (Json.mkObj [("content", toJson #[Json.mkObj [("type", "output_text"), ("text", toJson text)]])])]
      let r := (response "completed").mergeObj (Json.mkObj [("output", toJson raw)])
      match LeanTools.Responses.parseStream (event "response.completed" r) with
      | .error _ => false
      | .ok c => match LeanTools.Responses.requestBody "m1" (msgs.push c.message) tools (Json.mkObj []) routing with
        | .error _ => false
        | .ok body => ((body.getObjValD "input").getArr?.toOption.getD #[]).extract 2 4 == raw
  Test.Http.withServer fun base => do
    let endpoint : OpenAI.Endpoint := {
      baseUrl := base ++ "/v1/responses-ok", apiKey := "test-token", model := "m1",
      api := .responses, routing }
    let first ← OpenAI.complete endpoint msgs tools
    match first with
    | .error e => check "HTTP Responses request" false e
    | .ok c =>
      checkEq "capture routing state" c.turnState (some "route-first")
      let next ← OpenAI.complete { endpoint with routing := routing.capture c.turnState }
        (msgs ++ #[c.message, .tool "call_1" "ok"]) tools
      match next with
      | .error e => check "HTTP Responses continuation" false e
      | .ok c => checkEq "routing state is set once per turn" c.turnState (some "route-first")
    check "a new turn omits the old routing state" (← OpenAI.complete endpoint msgs tools).isOk
    let noSleep := fun (_ : Nat) => pure ()
    let retried ← OpenAI.complete { endpoint with baseUrl := base ++ "/v1/responses-retry", maxRetries := 1 } msgs tools noSleep
    check "retry uses Responses endpoint and succeeds" retried.isOk
    let count ← LeanTools.Http.request "GET" (base ++ "/count/responses-retry")
    checkEq "one retry sends two requests" (count.toOption.map (·.text)) (some "2")
    let failed ← OpenAI.complete { endpoint with baseUrl := base ++ "/v1/responses-failed" } msgs tools noSleep
    checkEq "HTTP 200 preserves the provider failure" failed.toOption.isNone true
    match failed with
    | .error e => check "provider failure message" (e.endsWith "denied") e
    | .ok _ => pure ()
    let rejected ← OpenAI.complete { endpoint with routing := { routing with turnState := some "bad\r\nInjected: yes" }, maxRetries := 0 } msgs tools noSleep
    match rejected with
    | .error e =>
      check "routing header injection is rejected before HTTP"
        (e.startsWith "the value of header x-codex-turn-state holds CR, LF or NUL") e
    | .ok _ => check "routing header injection is rejected" false

end Test.Responses
