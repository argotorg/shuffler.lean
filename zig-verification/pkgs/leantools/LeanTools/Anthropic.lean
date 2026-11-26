import LeanTools.Chat

open Lean

namespace LeanTools.Anthropic

def defaultExtra : Json := Json.mkObj [
  ("thinking", Json.mkObj [("type", "adaptive")]),
  ("output_config", Json.mkObj [("effort", "high")])]

def checkExtra (extra : Json) : Except String Unit := do
  discard <| extra.getObj?
  for key in ["model", "messages", "system", "tools", "stream", "cache_control"] do
    unless extra.getObjValD key == .null do throw s!"Anthropic extra cannot set {key}"

def functionTool (tool : Json) : Except String Json := do
  unless tool.getObjValD "type" == toJson "function" do throw "Anthropic expects function tools"
  let f ← tool.getObjVal? "function"
  return Json.mkObj [("name", toJson (← f.getObjValAs? String "name")),
    ("description", f.getObjValD "description"), ("input_schema", ← f.getObjVal? "parameters")]

def textBlock (text : String) : Json := Json.mkObj [("type", "text"), ("text", toJson text)]

def messageBlocks (m : Chat.Message) : Except String (Array Json) := do
  match m.role with
  | .tool => return #[Json.mkObj [("type", "tool_result"),
      ("tool_use_id", toJson m.toolCallId), ("content", toJson m.content)]]
  | .assistant =>
    if !m.responseItems.isEmpty then return m.responseItems
    let calls ← m.toolCalls.mapM fun call => do
      let args ← Json.parse call.arguments
      discard <| args.getObj?
      return Json.mkObj [("type", "tool_use"), ("id", toJson call.id),
        ("name", toJson call.name), ("input", args)]
    return (if m.content.isEmpty then #[] else #[textBlock m.content]) ++ calls
  | _ => return #[textBlock m.content]

def appendMessage (messages : Array Json) (role : String) (blocks : Array Json) : Array Json :=
  match messages.back? with
  | some last =>
    if last.getObjValD "role" == toJson role then
      messages.pop.push (last.setObjVal! "content"
        (toJson ((last.getObjValD "content").getArr?.toOption.getD #[] ++ blocks)))
    else messages.push (Json.mkObj [("role", toJson role), ("content", toJson blocks)])
  | none => #[Json.mkObj [("role", toJson role), ("content", toJson blocks)]]

def requestBody (model : String) (messages : Array Chat.Message) (tools : Array Json)
    (extra : Json) : Except String Json := do
  checkExtra extra
  let maximum ← extra.getObjValAs? Nat "max_tokens"
  unless maximum > 0 do throw "Anthropic max_tokens must be positive"
  let system := messages.filter (·.role == .system) |>.map (fun m => textBlock m.content)
  let history ← (messages.filter (·.role != .system)).foldlM (fun history m => do
    let blocks ← messageBlocks m
    return appendMessage history (if m.role == .assistant then "assistant" else "user") blocks) #[]
  let functions ← tools.mapM functionTool
  return (Json.mkObj [("model", toJson model), ("system", toJson system),
    ("messages", toJson history), ("tools", toJson functions), ("stream", .bool false),
    ("cache_control", Json.mkObj [("type", "ephemeral")])]).mergeObj extra

/-- Optional cache counters are zero when absent; malformed counters leave usage unknown. -/
def cacheCounterKnown (usage : Json) (name : String) : Bool :=
  usage.getObjValD name == .null || (usage.getObjValAs? Nat name).isOk

def parseCompletion (response : Json) : Except String Chat.Completion := do
  if response.getObjValD "type" == toJson "error" then
    throw (((response.getObjValD "error").getObjValD "message").getStr?.toOption.getD "Anthropic request failed")
  unless response.getObjValD "type" == toJson "message" &&
      response.getObjValD "role" == toJson "assistant" do throw "expected an Anthropic assistant message"
  let stop ← response.getObjValAs? String "stop_reason"
  unless ["end_turn", "tool_use", "stop_sequence", "max_tokens", "model_context_window_exceeded",
      "pause_turn", "refusal"].contains stop do throw s!"unknown Anthropic stop reason: {stop}"
  let limited := ["max_tokens", "model_context_window_exceeded"].contains stop
  -- A refusal is no decision: its tool calls do not run, as those of a cut reply do not.
  let refused := stop == "refusal"
  let output ← (response.getObjValD "content").getArr?
  let mut content := ""
  let mut reasoning := ""
  let mut calls := #[]
  for item in output do
    match ← item.getObjValAs? String "type" with
    | "text" => content := content ++ (← item.getObjValAs? String "text")
    | "thinking" => reasoning := reasoning ++ ((item.getObjValD "thinking").getStr?.toOption.getD "")
    | "redacted_thinking" => pure ()
    | "tool_use" =>
      unless limited || refused do
        let args ← item.getObjVal? "input"
        discard <| args.getObj?
        calls := calls.push {
          id := ← item.getObjValAs? String "id", name := ← item.getObjValAs? String "name",
          arguments := args.compress : Chat.ToolCall }
    | kind => throw s!"unsupported Anthropic content: {kind}"
  let usage := response.getObjValD "usage"
  let cached := Chat.natAt usage ["cache_read_input_tokens"]
  let created := Chat.natAt usage ["cache_creation_input_tokens"]
  let cacheKnown := cacheCounterKnown usage "cache_read_input_tokens" &&
    cacheCounterKnown usage "cache_creation_input_tokens"
  return {
    message := { Chat.Message.assistant content calls reasoning with
      responseItems := if limited || refused then output.filter (fun item => item.getObjValD "type" != toJson "tool_use")
        else output }
    finishReason := if limited then "length" else if refused then "refusal"
      else if calls.isEmpty then "stop" else "tool_calls"
    usageKnown := (usage.getObjValAs? Nat "input_tokens").isOk &&
      (usage.getObjValAs? Nat "output_tokens").isOk && cacheKnown
    cachedKnown := cacheKnown
    cacheCreation := created
    usage := {
      prompt := Chat.natAt usage ["input_tokens"] + created + cached
      cached := cached
      completion := Chat.natAt usage ["output_tokens"] } }

end LeanTools.Anthropic
