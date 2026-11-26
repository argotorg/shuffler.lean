import LeanTools.Chat
import LeanTools.Http
import LeanTools.Responses
import LeanTools.Anthropic

/-!
# Chat Completions, Responses and Anthropic Messages clients

`complete` sends `POST {baseUrl}/chat/completions`, `/responses` or `/messages`. Responses uses SSE with
`store: false` and retains output items for history replay. Pass the returned `turnState` through
the endpoint's turn-local `routing` on continuation requests. A rate limit (429), a server error (500,
502, 503, 504), a timeout (408) or a transport failure is tried again after a wait that doubles
each time, up to `maxRetries` more times; other statuses are errors at once. The wait is a
parameter, so that tests do not sleep. The same retry rule applies to an error code inside an
HTTP-200 JSON response. An internal server error without a code also permits a retry.
-/

open Lean

namespace LeanTools.OpenAI

inductive Api where
  | chatCompletions | responses | anthropicMessages
  deriving Repr, BEq, ToJson

/-- Task records made before the Responses client have no API tag. -/
instance : FromJson Api where
  fromJson?
    | .null | .str "chatCompletions" => .ok .chatCompletions
    | .str "responses" => .ok .responses
    | .str "anthropicMessages" => .ok .anthropicMessages
    | _ => .error "api must be chatCompletions, responses or anthropicMessages"

structure Endpoint where
  /-- For example `https://api.openai.com/v1`. -/
  baseUrl : String
  apiKey : String
  model : String
  api : Api := .chatCompletions
  routing : Responses.Routing := {}
  /-- Extra request fields; Responses uses `reasoning: {effort: "high"}`. -/
  extra : Json := Json.mkObj []
  timeoutMs : Nat := 900000
  maxRetries : Nat := 8
  /-- The first wait; then 2, 4, … times it, at most 60 s. -/
  backoffMs : Nat := 2000

def Endpoint.requestBody (e : Endpoint) (messages : Array Chat.Message) (tools : Array Json) :
    Except String Json :=
  match e.api with
  | .chatCompletions => .ok (Chat.requestBody e.model messages tools e.extra)
  | .responses => Responses.requestBody e.model messages tools e.extra e.routing
  | .anthropicMessages => Anthropic.requestBody e.model messages tools e.extra

/-- One request attempt. No body, URL, credential, or response headers are retained. -/
structure Attempt where
  number : Nat
  status : Option Nat
  elapsedMs : Nat
  /-- `none` means no further attempt, including on success. -/
  retryWaitMs : Option Nat
  /-- The `Retry-After` header of the reply, as sent. It is not part of `toJson`. -/
  retryAfter : Option String := none
deriving Repr, Inhabited

def Attempt.toJson (a : Attempt) : Json := Json.mkObj [
  ("attempt", Lean.toJson a.number), ("status", Lean.toJson a.status),
  ("elapsed_ms", Lean.toJson a.elapsedMs), ("retry_wait_ms", Lean.toJson a.retryWaitMs)]

def retryable (status : Nat) : Bool := [408, 429, 500, 502, 503, 504].contains status

/-- Some providers return errors inside HTTP 200. A numeric code takes precedence over the
message. Without a code, accept only the explicit internal-server-error message, including an
upstream prefix such as `Upstream error from <provider>: `. Unknown errors are terminal. -/
def retryableBodyError (body : String) : Bool :=
  let error := ((Json.parse body).toOption.map (·.getObjValD "error")).getD .null
  let code := error.getObjValD "code"
  match code.getNat?.toOption <|> (code.getStr?.toOption.bind String.toNat?) with
  | some status => retryable status
  | none =>
    if code != .null then false else
      let message := (error.getObjValAs? String "message").toOption.getD "" |>.toLower
      message == "internal server error" || message.endsWith ": internal server error"

/-- The error message of an OpenAI error body, else the start of the body. OpenRouter puts the reply of
the upstream provider in `error.metadata.raw` (its message is then only "Provider returned error"):
the start of that text follows the message. -/
def errorText (body : String) : String :=
  let error := ((Json.parse body).toOption.map (·.getObjValD "error")).getD .null
  match (error.getObjValAs? String "message").toOption with
  | none => (body.take 500).toString
  | some m =>
    match ((error.getObjValD "metadata").getObjValAs? String "raw").toOption with
    | some raw => m ++ ": " ++ (raw.take 500).toString
    | none => m

def complete (e : Endpoint) (messages : Array Chat.Message) (tools : Array Json)
    (sleep : Nat → IO Unit := fun ms => IO.sleep ms.toUInt32)
    (onAttempt : Attempt → IO Unit := fun _ => pure ()) : IO (Except String Chat.Completion) := do
  let body ← match e.requestBody messages tools with
    | .ok body => pure body.compress.toUTF8
    | .error error => return .error error
  let headers := #[("Content-Type", "application/json")] ++ match e.api with
    | .anthropicMessages => #[("x-api-key", e.apiKey), ("anthropic-version", "2023-06-01")]
    | .responses => #[("Authorization", s!"Bearer {e.apiKey}")] ++ e.routing.headers
    | .chatCompletions => #[("Authorization", s!"Bearer {e.apiKey}")]
  let route := match e.api with
    | .responses => "responses"
    | .chatCompletions => "chat/completions"
    | .anthropicMessages => "messages"
  let url := (if e.baseUrl.endsWith "/" then e.baseUrl else e.baseUrl ++ "/") ++ route
  let mut attempt := 0
  let mut last := ""
  while true do
    let started ← IO.monoMsNow
    let r ← Http.request "POST" url headers body e.timeoutMs
    let elapsedMs := (← IO.monoMsNow) - started
    let again ← match r with
      | .error err => do last := err; pure true
      | .ok resp =>
        if resp.status == 200 then
          let parsed : Except String Chat.Completion := match e.api with
            | .chatCompletions => Json.parse resp.text >>= Chat.parseCompletion
            | .anthropicMessages => Json.parse resp.text >>= Anthropic.parseCompletion
            | .responses => (Responses.parseStream resp.text).map fun c =>
                { c with turnState := (e.routing.capture (resp.header "x-codex-turn-state")).turnState }
          match parsed with
          | .ok completion =>
            onAttempt { number := attempt + 1, status := some resp.status, elapsedMs, retryWaitMs := none }
            return .ok completion
          | .error error =>
            last := s!"the response: {error}"
            pure (retryableBodyError resp.text)
        else
          last := s!"HTTP {resp.status}: {errorText resp.text}"
          pure (retryable resp.status)
    let retryWaitMs := if again && attempt < e.maxRetries then some (min (e.backoffMs * 2 ^ attempt) 60000) else none
    onAttempt { number := attempt + 1, status := r.toOption.map (·.status), elapsedMs, retryWaitMs,
                retryAfter := r.toOption.bind (·.header "retry-after") }
    let some wait := retryWaitMs | return .error last
    sleep wait
    attempt := attempt + 1
  return .error last

end LeanTools.OpenAI
