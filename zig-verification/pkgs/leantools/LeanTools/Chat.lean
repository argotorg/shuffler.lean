import Lean.Data.Json
import LeanTools.Tools

/-!
# OpenAI chat completions: the data

Messages, tool calls, usage and cost, the request body, and the parse of a response, as pure
functions. `LeanTools.OpenAI` sends the requests.
-/

open Lean

namespace LeanTools.Chat

structure ToolCall where
  id : String
  name : String
  /-- The arguments as JSON text, as the model wrote them. -/
  arguments : String
deriving Repr, BEq, Inhabited

inductive Role where
  | system | user | assistant | tool
deriving Repr, BEq, Inhabited

structure Message where
  role : Role
  content : String
  toolCalls : Array ToolCall := #[]
  /-- For a tool message: the call that it answers. -/
  toolCallId : String := ""
  /-- For an assistant message: the model's reasoning text; empty when the response has none. -/
  reasoning : String := ""
  /-- Provider output blocks, including signed or encrypted reasoning, for replay. -/
  responseItems : Array Json := #[]
deriving BEq, Inhabited

instance : Repr Message where
  reprPrec m _ := repr (m.role, m.content, m.toolCalls, m.toolCallId, m.reasoning,
    m.responseItems.map Json.compress)

def Message.system (s : String) : Message := { role := .system, content := s }
def Message.user (s : String) : Message := { role := .user, content := s }
def Message.assistant (s : String) (calls : Array ToolCall := #[]) (reasoning := "") : Message :=
  { role := .assistant, content := s, toolCalls := calls, reasoning }
def Message.tool (id s : String) : Message := { role := .tool, content := s, toolCallId := id }

structure Usage where
  prompt : Nat := 0
  /-- The prompt tokens read from the provider's cache. -/
  cached : Nat := 0
  completion : Nat := 0
deriving Repr, BEq, Inhabited

instance : Add Usage := ⟨fun a b => ⟨a.prompt + b.prompt, a.cached + b.cached, a.completion + b.completion⟩⟩

/-- Prices in USD per million tokens. -/
structure Price where
  input : Float := 0
  cachedInput : Float := 0
  output : Float := 0
deriving Repr, Inhabited

def Price.cost (p : Price) (u : Usage) : Float :=
  ((u.prompt - u.cached).toFloat * p.input + u.cached.toFloat * p.cachedInput
    + u.completion.toFloat * p.output) / 1000000

structure Completion where
  message : Message
  finishReason : String
  usage : Usage
  usageKnown : Bool := true
  cachedKnown : Bool := true
  /-- Anthropic input tokens used to create cache entries. -/
  cacheCreation : Nat := 0
  /-- The first routing token received within this agent turn. -/
  turnState : Option String := none
deriving Repr, Inhabited

def roleName : Role → String
  | .system => "system" | .user => "user" | .assistant => "assistant" | .tool => "tool"

def Message.encode (m : Message) : Json :=
  match m.role with
  | .tool => Json.mkObj [("role", "tool"), ("tool_call_id", toJson m.toolCallId), ("content", toJson m.content)]
  | .assistant =>
    let calls := m.toolCalls.map fun c => Json.mkObj [("id", toJson c.id), ("type", "function"),
      ("function", Json.mkObj [("name", toJson c.name), ("arguments", toJson c.arguments)])]
    let content : Json := if m.content.isEmpty && !calls.isEmpty then Json.null else toJson m.content
    let fields : List (String × Json) := [("role", toJson "assistant"), ("content", content)]
    Json.mkObj (fields ++ (if calls.isEmpty then [] else [("tool_calls", toJson calls)])
      ++ if m.reasoning.isEmpty then [] else [("reasoning", toJson m.reasoning)])
  | r => Json.mkObj [("role", toJson (roleName r)), ("content", toJson m.content)]

/-- The request body: `extra` (for example `reasoning_effort`) is merged at the top level. -/
def requestBody (model : String) (messages : Array Message) (tools : Array Json) (extra : Json) : Json :=
  let base := Json.mkObj ([("model", toJson model), ("messages", toJson (messages.map Message.encode))]
    ++ if tools.isEmpty then [] else [("tools", toJson tools)])
  base.mergeObj extra

/-- The model field sent after `extra` replaces request fields. -/
def requestModel (model : String) (extra : Json) : Json :=
  (requestBody model #[] #[] extra).getObjValD "model"

def natAt (j : Json) (path : List String) : Nat :=
  (path.foldl (fun j k => j.getObjValD k) j).getNat?.toOption.getD 0

def parseCompletion (j : Json) : Except String Completion := do
  if let .ok (msg : String) := (j.getObjValD "error").getObjValAs? String "message" then
    throw msg
  let choices ← (j.getObjValD "choices").getArr?
  let some choice := choices[0]? | throw "the response has no choices"
  let m := choice.getObjValD "message"
  let content := (m.getObjValD "content").getStr?.toOption.getD ""
  let finishReason := (choice.getObjValD "finish_reason").getStr?.toOption.getD ""
  -- A length-limited reply may end in the middle of a tool call. Keep usage and text, but do
  -- not parse or execute those calls. The proof loop requests a complete reply.
  let rawCalls := if finishReason == "length" then #[] else (m.getObjValD "tool_calls").getArr?.toOption.getD #[]
  let calls ← rawCalls.mapM fun c => do
    let f := c.getObjValD "function"
    return { id := ← c.getObjValAs? String "id", name := ← f.getObjValAs? String "name",
             arguments := (f.getObjValD "arguments").getStr?.toOption.getD "{}" : ToolCall }
  -- `reasoning` (vLLM, OpenRouter) or `reasoning_content` (DeepSeek)
  let reasoning := ["reasoning", "reasoning_content"].findSome? (m.getObjValD · |>.getStr?.toOption |>.filter (!·.isEmpty)) |>.getD ""
  let u := j.getObjValD "usage"
  return { message := .assistant content calls reasoning,
           finishReason,
           usageKnown := (u.getObjValAs? Nat "prompt_tokens").isOk &&
             (u.getObjValAs? Nat "completion_tokens").isOk,
           cachedKnown := ((u.getObjValD "prompt_tokens_details").getObjValAs? Nat "cached_tokens").isOk,
           usage := { prompt := natAt u ["prompt_tokens"], cached := natAt u ["prompt_tokens_details", "cached_tokens"],
                      completion := natAt u ["completion_tokens"] } }

/-- The leantools tools as OpenAI function tools. -/
def functionTools : Array Json :=
  LeanTools.tools.map fun t =>
    let s := t.schema
    Json.mkObj [("type", "function"), ("function", Json.mkObj [
      ("name", s.getObjValD "name"), ("description", s.getObjValD "description"),
      ("parameters", s.getObjValD "input_schema")])]

end LeanTools.Chat
