import Lean.Data.Json
import LeanTools.Http
import Test.Harness

/-! Tests of the libcurl binding against `Test/mock_http.py` (needs python3). -/

open Lean LeanTools.Http Test

namespace Test.Http

def echo (r : Except String Response) : Option Json :=
  match r with
  | .ok resp => (Json.parse resp.text).toOption
  | .error _ => none

def errorOf (r : Except String Response) : String :=
  match r with
  | .ok resp => s!"(no error: status {resp.status})"
  | .error e => e

def statusOf (r : Except String Response) : Option Nat :=
  match r with
  | .ok resp => some resp.status
  | .error _ => none

def withServer (k : String → T Unit) : T Unit := do
  let child ← IO.Process.spawn {
    cmd := "python3", args := #["Test/mock_http.py"]
    stdout := .piped, stdin := .null, stderr := .null }
  let port := (← child.stdout.getLine).trimAscii.toString
  try k s!"http://127.0.0.1:{port}" finally child.kill

def suite : T Unit := withServer fun base => do
  checkEq "final response header block"
    (responseHeaders "HTTP/1.1 100 Continue\r\nX-Old: old\r\n\r\nHTTP/1.1 200 OK\r\nX-Codex-Turn-State: a:b \r\n\r\n")
    #[("x-codex-turn-state", "a:b")]
  let response ← request "GET" s!"{base}/redirect"
  checkEq "response header names ignore case"
    (response.toOption.bind (·.header "LOCATION")) (some "/echo")
  let response ← request "GET" s!"{base}/interim"
  checkEq "capture the final response header"
    (response.toOption.bind (·.header "x-codex-turn-state")) (some "final")
  let e := errorOf (← request "GET" s!"{base}/headers/70000")
  check "response headers are bounded" (e.startsWith "response headers: longer than the limit") e
  -- the body goes as bytes: its length is the UTF-8 length
  let text := "⊢ ⦃P⦄ prog ⦃Q⦄ ok"
  let j := echo (← request "POST" s!"{base}/echo" #[("Content-Type", "application/json")] text.toUTF8)
  checkEq "UTF-8 body: byte length" (j.bind (·.getObjValAs? Nat "length" |>.toOption)) (some text.utf8ByteSize)
  checkEq "UTF-8 body: text" (j.bind (·.getObjValAs? String "body" |>.toOption)) (some text)
  -- a body larger than a command-line argument may be, and larger than 1 MiB, above which curl
  -- would send Expect: 100-continue
  let big := String.ofList (List.replicate 2000000 'x')
  let j := echo (← request "POST" s!"{base}/echo" #[] big.toUTF8)
  checkEq "2 MB body" (j.bind (·.getObjValAs? Nat "length" |>.toOption)) (some 2000000)
  checkEq "2 MB body: no Expect header"
    (j.bind fun j => (j.getObjValD "headers").getObjValAs? String "expect" |>.toOption) none
  -- the length is the byte count, also with a NUL byte
  let j := echo (← request "POST" s!"{base}/echo" #[] (ByteArray.mk #[0x61, 0x00, 0x62]))
  checkEq "body with NUL" (j.bind (·.getObjValAs? Nat "length" |>.toOption)) (some 3)
  -- the headers arrive as given, and no Expect: 100-continue
  let j := echo (← request "POST" s!"{base}/echo" #[("Authorization", "Bearer k3y"), ("X-Test", "a b")] "x".toUTF8)
  let hdr (k : String) := j.bind fun j => (j.getObjValD "headers").getObjValAs? String k |>.toOption
  checkEq "Authorization header" (hdr "authorization") (some "Bearer k3y")
  checkEq "custom header" (hdr "x-test") (some "a b")
  checkEq "no Expect header" (hdr "expect") none
  -- GET with no body
  let j := echo (← request "GET" s!"{base}/echo")
  checkEq "GET" (j.bind (·.getObjValAs? String "method" |>.toOption)) (some "GET")
  -- statuses are values, not errors; redirects are not followed
  checkEq "status 500" (statusOf (← request "GET" s!"{base}/status/500")) (some 500)
  checkEq "status 429" (statusOf (← request "GET" s!"{base}/status/429")) (some 429)
  checkEq "redirect not followed" (statusOf (← request "GET" s!"{base}/redirect")) (some 302)
  -- failures
  let e := errorOf (← request "GET" s!"{base}/sleep/3000" (timeoutMs := 300))
  check "timeout" (e.startsWith "Timeout was reached") e
  let e := errorOf (← request "GET" "http://127.0.0.1:1/")
  check "refused connection" (e.startsWith "Could not connect to server" || e.startsWith "Couldn't connect to server") e
  let e := errorOf (← request "GET" s!"{base}/big/5000" (maxBytes := 1000))
  check "size limit" (e.startsWith "response: longer than the limit") e
  checkEq "under the size limit" ((← request "GET" s!"{base}/big/1000" (maxBytes := 1000)).toOption.map (·.body.size)) (some 1000)
  let e := errorOf (← request "GET" "ftp://127.0.0.1/")
  check "only http and https" (!e.startsWith "(no error") e
  -- inputs that could add a header are refused before C
  let e := errorOf (← request "GET" s!"{base}/echo" #[("X-A", "v\r\nX-B: injected")])
  check "header value with CRLF" (e.startsWith "the value of header X-A holds CR, LF or NUL") e
  let e := errorOf (← request "GET" s!"{base}/echo" #[("X A", "v")])
  check "header name with a space" (e.startsWith "header name") e
  let e := errorOf (← request "GE T" s!"{base}/echo")
  check "method with a space" (e.startsWith "method") e
  let e := errorOf (← request "GET" s!"{base}/echo\x00x")
  check "URL with NUL" (e.startsWith "the URL holds") e
  -- requests on several threads at once
  let tasks ← (List.range 16).mapM fun i => IO.asTask
    (request "POST" s!"{base}/echo" #[] (toString i).toUTF8)
  let bodies ← tasks.mapM fun t => do
    match ← IO.wait t with
    | .ok r => pure ((echo r).bind (·.getObjValAs? String "body" |>.toOption))
    | .error _ => pure none
  checkEq "parallel requests" bodies ((List.range 16).map (some ∘ toString))

end Test.Http
