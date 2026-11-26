import LeanTools.OpenAI
import Test.Http

/-! Tests of the OpenAI client against the chat endpoints of `Test/mock_http.py`. -/

open Lean LeanTools Chat OpenAI Test

namespace Test.OpenAI

def endpoint (base path : String) (retries : Nat := 3) : Endpoint :=
  { baseUrl := s!"{base}/v1/{path}", apiKey := "sk-test", model := "m1", maxRetries := retries }

def noSleep : Nat → IO Unit := fun _ => pure ()

def count (base key : String) : IO Nat := do
  match ← Http.request "GET" s!"{base}/count/{key}" with
  | .ok r => return r.text.toNat!
  | .error _ => return 0

def suite : T Unit := Test.Http.withServer fun base => do
  let msgs := #[Chat.Message.system "S", .user "U"]
  match ← complete (endpoint base "ok") msgs #[] noSleep with
  | .error e => check "ok" false e
  | .ok c =>
    let j := (Json.parse c.message.content).toOption.getD .null
    checkEq "the key is sent as a bearer token" (j.getObjValAs? String "auth" |>.toOption) (some "Bearer sk-test")
    checkEq "the model is sent" (j.getObjValAs? String "model" |>.toOption) (some "m1")
    checkEq "the messages are sent" (j.getObjValAs? Nat "n_messages" |>.toOption) (some 2)
    checkEq "usage" (c.usage.prompt, c.usage.cached, c.usage.completion) (100, 50, 10)
  -- rate limits are tried again, up to maxRetries
  match ← complete (endpoint base "flaky/a/2" (retries := 3)) msgs #[] noSleep with
  | .ok _ => checkEq "two 429, then success: requests" (← count base "a") 3
  | .error e => check "two 429, then success" false e
  match ← complete (endpoint base "flaky/b/5" (retries := 2)) msgs #[] noSleep with
  | .ok _ => check "more 429 than retries" false "no error"
  | .error e =>
    check "more 429 than retries: error" (e.startsWith "HTTP 429") e
    checkEq "more 429 than retries: requests" (← count base "b") 3
  -- the waits grow: 1, 2, 4 times the base wait
  let waits ← IO.mkRef #[]
  let _ ← complete { endpoint base "flaky/c/3" (retries := 3) with backoffMs := 100 } msgs #[]
    fun ms => waits.modify (·.push ms)
  checkEq "back-off" (← waits.get) #[100, 200, 400]
  let attempts ← IO.mkRef (#[] : Array Attempt)
  let record := fun a => attempts.modify (·.push a)
  let _ ← complete (endpoint base "flaky502/log-success/1") msgs #[] noSleep record
  let got ← attempts.get
  checkEq "502 then success: attempts" (got.map fun a => (a.number, a.status, a.retryWaitMs))
    #[(1, some 502, some 2000), (2, some 200, none)]
  let encoded := got.foldl (fun s a => s ++ a.toJson.compress) ""
  check "attempt logs exclude credentials and response text"
    ((encoded.splitOn "sk-test").length == 1 && (encoded.splitOn "retry\"").length == 1) encoded
  -- the Retry-After header of a reply is in the attempt (and not in its JSON)
  attempts.set #[]
  let _ ← complete (endpoint base "flakyra/ra/1") msgs #[] noSleep record
  checkEq "429 with Retry-After: the header of each attempt" ((← attempts.get).map (·.retryAfter))
    #[some "7", none]
  check "the header is not in the JSON of the log"
    ((← attempts.get).all fun a => (a.toJson.getObjVal? "retryAfter").toOption.isNone) "retryAfter in the log"
  attempts.set #[]
  let _ ← complete (endpoint base "flaky502/log-exhausted/3" (retries := 1)) msgs #[] noSleep record
  checkEq "exhausted: last attempt has no wait"
    ((← attempts.get).map fun a => (a.number, a.status, a.retryWaitMs))
    #[(1, some 502, some 2000), (2, some 502, none)]
  -- a client error is not tried again
  match ← complete (endpoint base "bad") msgs #[] noSleep with
  | .ok _ => check "400" false "no error"
  | .error e =>
    check "400: error with the message" (e.startsWith "HTTP 400: bad request: no model") e
    checkEq "400: one request" (← count base "bad") 1
  -- A provider can send a transient error with HTTP 200. Keep the HTTP status in the
  -- attempt log, but apply the retry limit and back-off to the error in the body.
  for code in ["408", "429", "500", "502", "503", "504", "s500", "missing", "bare"] do
    let key := s!"body-{code}"
    attempts.set #[]
    waits.set #[]
    let result ← complete { endpoint base s!"error200/{key}/2/{code}" (retries := 2) with backoffMs := 100 }
      msgs #[] (fun ms => waits.modify (·.push ms)) record
    check s!"HTTP 200 error {code}: recovers" result.isOk
    checkEq s!"HTTP 200 error {code}: requests" (← count base key) 3
    checkEq s!"HTTP 200 error {code}: waits" (← waits.get) #[100, 200]
    checkEq s!"HTTP 200 error {code}: attempts"
      ((← attempts.get).map fun a => (a.number, a.status, a.retryWaitMs))
      #[(1, some 200, some 100), (2, some 200, some 200), (3, some 200, none)]
  for retries in [0, 1] do
    let key := s!"body-exhausted-{retries}"
    attempts.set #[]
    let result ← complete (endpoint base s!"error200/{key}/5/500" (retries := retries))
      msgs #[] noSleep record
    checkEq s!"HTTP 200 exhausted {retries}: error" result.toOption.isNone true
    if let .error error := result then
      checkEq s!"HTTP 200 exhausted {retries}: keeps the message" error
        "the response: Upstream error from DeepInfra: Internal server error"
    checkEq s!"HTTP 200 exhausted {retries}: requests" (← count base key) (retries + 1)
    checkEq s!"HTTP 200 exhausted {retries}: last attempt has no wait"
      ((← attempts.get).back?.bind (·.retryWaitMs)) none
  -- Permanent errors, unknown errors and malformed completions still fail at once.
  for code in ["400", "401", "sunknown", "unknown", "malformed", "choices"] do
    let key := s!"body-permanent-{code}"
    attempts.set #[]
    let result ← complete (endpoint base s!"error200/{key}/5/{code}") msgs #[] noSleep record
    checkEq s!"HTTP 200 permanent {code}: error" result.toOption.isNone true
    checkEq s!"HTTP 200 permanent {code}: requests" (← count base key) 1
    checkEq s!"HTTP 200 permanent {code}: one terminal attempt"
      ((← attempts.get).map fun a => (a.number, a.status, a.retryWaitMs)) #[(1, some 200, none)]
  -- the text of an error body
  checkEq "error text: the message" (errorText "{\"error\":{\"message\":\"too long\",\"code\":400}}") "too long"
  checkEq "error text: the reply of the upstream provider of OpenRouter"
    (errorText "{\"error\":{\"message\":\"Provider returned error\",\"code\":400,\"metadata\":{\"raw\":\"maximum context length is 10 tokens\",\"provider_name\":\"DeepInfra\"}}}")
    "Provider returned error: maximum context length is 10 tokens"
  checkEq "error text: a raw text that is no string is left out"
    (errorText "{\"error\":{\"message\":\"m\",\"metadata\":{\"raw\":3}}}") "m"
  checkEq "error text: no message, the start of the body" (errorText "{\"detail\":\"x\"}") "{\"detail\":\"x\"}"
  checkEq "error text: not JSON" (errorText "plain") "plain"
  checkEq "error text: the raw text is cut"
    (errorText s!"\{\"error\":\{\"message\":\"m\",\"metadata\":\{\"raw\":\"{"".pushn 'x' 900}\"}}}").length
    (3 + 500)
  -- a transport failure is tried again, then reported
  match ← complete { endpoint base "ok" (retries := 1) with baseUrl := "http://127.0.0.1:1/v1" } msgs #[] noSleep with
  | .ok _ => check "refused" false "no error"
  | .error e => check "refused: error" (e.startsWith "Could") e

end Test.OpenAI
