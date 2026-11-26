import LeanTools.Chat

/-! The SIWC Responses wire format. History contains the returned output items without
rewriting reasoning, message phases, or call IDs. Routing state belongs to one agent turn. -/

open Lean

namespace LeanTools.Responses

structure Routing where
  sessionId : String := ""
  turnState : Option String := none
  deriving Repr, BEq

/-- Codex captures the first token, then replays it unchanged until the turn ends. -/
def Routing.capture (routing : Routing) (token : Option String) : Routing :=
  { routing with turnState := routing.turnState.or token }

def Routing.headers (routing : Routing) : Array (String × String) :=
  (if routing.sessionId.isEmpty then #[] else #[("session_id", routing.sessionId)]) ++
    (routing.turnState.toArray.map fun token => ("x-codex-turn-state", token))

/-- SIWC rejects these fields, or the client owns them to preserve its request contract. -/
def forbiddenExtra : List String := [
  "model", "messages", "input", "tools", "store", "stream", "include", "prompt_cache_key",
  "reasoning_effort", "max_tokens", "max_completion_tokens", "background", "conversation",
  "max_output_tokens", "max_tool_calls", "metadata", "moderation", "multi_agent", "prompt",
  "prompt_cache_retention", "safety_identifier", "temperature", "top_logprobs", "top_p",
  "truncation", "user", "previous_response_id"]

def checkExtra (extra : Json) : Except String Unit := do
  let fields ← extra.getObj?
  for (key, _) in fields.toArray do
    if forbiddenExtra.contains key then throw s!"Responses extra cannot set {key}"

def messageItems (m : Chat.Message) : Array Json :=
  if m.role == .assistant && !m.responseItems.isEmpty then m.responseItems
  else match m.role with
    | .tool => #[Json.mkObj [("type", "function_call_output"),
        ("call_id", toJson m.toolCallId), ("output", toJson m.content)]]
    | role => #[Json.mkObj [("role", toJson (if role == .system then "developer" else Chat.roleName role)),
        ("content", toJson m.content)]]

def functionTool (tool : Json) : Except String Json := do
  unless tool.getObjValD "type" == toJson "function" do throw "Responses expects function tools"
  let f ← tool.getObjVal? "function"
  return Json.mkObj [("type", "function"), ("name", toJson (← f.getObjValAs? String "name")),
    ("description", f.getObjValD "description"), ("parameters", ← f.getObjVal? "parameters"),
    ("strict", .bool false)]

def requestBody (model : String) (messages : Array Chat.Message) (tools : Array Json)
    (extra : Json) (routing : Routing) : Except String Json := do
  checkExtra extra
  let functions ← tools.mapM functionTool
  let base := Json.mkObj ([
    ("model", toJson model), ("input", toJson (messages.flatMap messageItems)),
    ("store", .bool false), ("stream", .bool true),
    ("include", toJson #["reasoning.encrypted_content"])] ++
    (if routing.sessionId.isEmpty then [] else [("prompt_cache_key", toJson routing.sessionId)]) ++
    (if functions.isEmpty then [] else [("tools", toJson #[Json.mkObj [
      ("type", "namespace"), ("name", "lean"), ("description", "Lean proof tools."),
      ("tools", toJson functions)]])]))
  return base.mergeObj extra

def responseError (response : Json) : String :=
  let error := response.getObjValD "error"
  let code := (error.getObjValD "code").getStr?.toOption.getD "response failed"
  let message := (error.getObjValD "message").getStr?.toOption.getD ""
  let param := (error.getObjValD "param").getStr?.toOption.getD ""
  let detail := if message.isEmpty then code else code ++ ": " ++ message
  let detail := if param.isEmpty then detail else detail ++ s!" (param: {param})"
  if error == .null then detail ++ ": " ++ (response.compress.take 2000).toString else detail

def parseResponse (response : Json) (limited : Bool := false) : Except String Chat.Completion := do
  let output ← (response.getObjValD "output").getArr?
  let mut content := ""
  let mut reasoning := ""
  let mut calls := #[]
  for item in output do
    match ← item.getObjValAs? String "type" with
    | "message" =>
      for part in ← (item.getObjValD "content").getArr? do
        match ← part.getObjValAs? String "type" with
        | "output_text" => content := content ++ (← part.getObjValAs? String "text")
        | "refusal" => content := content ++ (← part.getObjValAs? String "refusal")
        | kind => throw s!"unsupported Responses content: {kind}"
    | "reasoning" =>
      for part in (item.getObjValD "summary").getArr?.toOption.getD #[] do
        reasoning := reasoning ++ (part.getObjValD "text").getStr?.toOption.getD ""
    | "function_call" =>
      unless limited do
        let ns := item.getObjValD "namespace"
        unless ns == .null || ns == toJson "lean" do throw "unknown Responses tool namespace"
        calls := calls.push {
          id := ← item.getObjValAs? String "call_id", name := ← item.getObjValAs? String "name",
          arguments := ← item.getObjValAs? String "arguments" : Chat.ToolCall }
    | kind => throw s!"unsupported Responses output: {kind}"
  let u := response.getObjValD "usage"
  return {
    message := { Chat.Message.assistant content calls reasoning with
      responseItems := if limited then output.filter (fun item => item.getObjValD "type" != toJson "function_call") else output }
    finishReason := if limited then "length" else if calls.isEmpty then "stop" else "tool_calls"
    usageKnown := (u.getObjValAs? Nat "input_tokens").isOk && (u.getObjValAs? Nat "output_tokens").isOk
    cachedKnown := ((u.getObjValD "input_tokens_details").getObjValAs? Nat "cached_tokens").isOk
    usage := {
      prompt := Chat.natAt u ["input_tokens"]
      cached := Chat.natAt u ["input_tokens_details", "cached_tokens"]
      completion := Chat.natAt u ["output_tokens"] } }

/-- Only a terminal response supplies tool calls. Deltas cannot execute partial calls.
The HTTP layer bounds and buffers the stream; a missing final event is an error. -/
def parseStream (stream : String) : Except String Chat.Completion := do
  let frames := ((stream.replace "\r\n" "\n").splitOn "\n\n").dropLast
  let mut result := none
  for frame in frames do
    let lines := (frame.splitOn "\n").filterMap fun line =>
      if line.startsWith "data:" then
        let data := (line.drop 5).toString
        some (if data.startsWith " " then (data.drop 1).toString else data)
      else none
    unless lines.isEmpty do
      let data := String.intercalate "\n" lines
      unless data == "[DONE]" do
        let event ← Json.parse data
        let kind ← event.getObjValAs? String "type"
        if ["response.completed", "response.incomplete", "response.failed", "error"].contains kind then
          if result.isSome then throw "the stream has more than one terminal response"
          match kind with
          | "response.failed" =>
            let response := event.getObjValD "response"
            throw (responseError (if response.getObjValD "error" == .null then event else response))
          | "error" => throw (responseError (if event.getObjValD "error" == .null then
              Json.mkObj [("error", event)] else event))
          | "response.incomplete" =>
            let response := event.getObjValD "response"
            unless (response.getObjValD "incomplete_details").getObjValD "reason" == toJson "max_output_tokens" do
              throw "the Responses result is incomplete"
            result := some (← parseResponse response true)
          | _ =>
            let response := event.getObjValD "response"
            unless response.getObjValD "status" == toJson "completed" do
              throw "response.completed has a non-completed status"
            result := some (← parseResponse response)
  match result with
  | some completion => return completion
  | none => throw "the stream ended without a terminal response"

end LeanTools.Responses
