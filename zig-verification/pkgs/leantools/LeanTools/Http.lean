/-!
# HTTP requests with libcurl

`request` performs one HTTP request through the C shim `c/http.c`. The shim follows no redirects,
allows only http and https, and reads the proxy from the environment. The inputs are checked
before they reach C: the method and the header names are tokens, and no header value, URL or
method holds CR, LF or NUL, so that a value cannot add a header and C sees the whole string.
-/

namespace LeanTools.Http

@[extern "leantools_http_request"]
opaque requestRaw (method url : @& String) (headers : @& Array String) (body : @& ByteArray)
    (timeoutMs : UInt32) (maxBytes : USize) : IO (UInt32 × ByteArray × ByteArray)

structure Response where
  status : Nat
  body : ByteArray
  headers : Array (String × String) := #[]

def Response.text (r : Response) : String := String.fromUTF8! r.body

def Response.header (r : Response) (name : String) : Option String :=
  (r.headers.find? (fun h => h.1 == name.toLower)).map (·.2)

/-- Keep only the last header block, after proxy CONNECT or informational responses. -/
def responseHeaders (text : String) : Array (String × String) :=
  (text.splitOn "\n").foldl (fun headers line =>
    if line.startsWith "HTTP/" then #[]
    else match line.splitOn ":" with
    | name :: value :: rest => headers.push
        (name.trimAscii.toString.toLower, (String.intercalate ":" (value :: rest)).trimAscii.toString)
    | _ => headers) #[]

/-- An HTTP token (RFC 9110): the characters of a method or a header name. -/
def isToken (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun (c : Char) => c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

def noControl (s : String) : Bool := s.toList.all fun (c : Char) => c != '\r' && c != '\n' && c != '\x00'

/-- The request after the checks of its inputs, as the shim takes it. -/
def checked (method url : String) (headers : Array (String × String)) :
    Except String (Array String) := do
  unless isToken method do throw s!"method {method.quote} is not a token"
  unless noControl url do throw "the URL holds CR, LF or NUL"
  headers.mapM fun (name, value) => do
    unless isToken name do throw s!"header name {name.quote} is not a token"
    unless noControl value do throw s!"the value of header {name} holds CR, LF or NUL"
    return s!"{name}: {value}"

/-- One request. The call blocks, so it runs on a dedicated task. -/
def request (method url : String) (headers : Array (String × String) := #[])
    (body : ByteArray := .empty) (timeoutMs : Nat := 600000) (maxBytes : Nat := 64 * 1024 * 1024) :
    IO (Except String Response) := do
  match checked method url headers with
  | .error e => return .error e
  | .ok lines =>
    let t ← IO.asTask (prio := .dedicated)
      (requestRaw method url lines body (min timeoutMs 0xffffffff).toUInt32 maxBytes.toUSize)
    match ← IO.wait t with
    | .ok (status, b, h) => return .ok {
        status := status.toNat, body := b, headers := responseHeaders (String.fromUTF8! h) }
    | .error e => return .error (toString e)

end LeanTools.Http
