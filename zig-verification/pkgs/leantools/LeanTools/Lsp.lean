import Lean.Data.Lsp
import Std.Sync.Mutex
import LeanTools.Pos

/-!
# A client of the Lean language server

One `lake serve` for the project. Several requests can be in flight at once: a reader task gives
each response to the promise of its request, and keeps the diagnostics of each document from the
`publishDiagnostics` notifications. The server elaborates each open file in its own worker, and
keeps its snapshots between edits, so a check after an edit elaborates only from the change.
-/

open Lean Lsp JsonRpc

namespace LeanTools

/-- The text and version of an open document, and its diagnostics for that version. -/
structure Doc where
  version : Nat
  text : String
  diagnostics : Array Diagnostic := #[]

structure LspState where
  nextId : Nat := 1
  pending : Std.HashMap Nat (IO.Promise (Except String Json)) := {}
  docs : Std.HashMap DocumentUri Doc := {}
  /-- The order in which documents were last used, the most recent last. -/
  recent : Array DocumentUri := #[]
  /-- Active operations can share a document; none may lose its worker to LRU eviction. -/
  active : Std.HashMap DocumentUri Nat := {}
  dead : Option String := none

structure Lsp where
  root : System.FilePath
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }
  stdin : IO.FS.Stream
  state : Std.Mutex LspState
  writer : Std.Mutex Unit
  /-- Orders document state changes with their didOpen/didChange/didClose notifications. -/
  documents : Std.Mutex Unit
  /-- The index of the semantic token type `leanSorryLike`. -/
  sorryToken : Option Nat
  /-- The most documents kept open; each open document has a worker process. -/
  maxOpen : Nat

def Lsp.uriOf (lsp : Lsp) (path : System.FilePath) : DocumentUri :=
  System.Uri.pathToUri (if path.isAbsolute then path else lsp.root / path)

private def send (stdin : IO.FS.Stream) (writer : Std.Mutex Unit) (msg : JsonRpc.Message) : IO Unit :=
  writer.atomically (stdin.writeLspMessage msg)

/-- JSON-RPC parameters must be an object or an array. -/
def structured : Json → Option Json.Structured
  | .obj kvs => some (.obj kvs)
  | .arr a => some (.arr a)
  | _ => none

private def mergeDiagnostics (doc : Doc) (p : PublishDiagnosticsParams) : Doc :=
  if p.version?.map (·.toNat) != some doc.version then doc
  else if p.isIncremental?.getD false then { doc with diagnostics := doc.diagnostics ++ p.diagnostics }
  else { doc with diagnostics := p.diagnostics }

/-- Reads messages until the server's output ends; then fails the pending requests. -/
private partial def readLoop (stdout : IO.FS.Stream) (stdin : IO.FS.Stream) (writer : Std.Mutex Unit)
    (state : Std.Mutex LspState) : IO Unit := do
  let msg ← try some <$> stdout.readLspMessage catch e => do
    if (← IO.getEnv "LEANTOOLS_TRACE").isSome then IO.eprintln s!"[lsp] read failed: {e}"
    pure none
  if (← IO.getEnv "LEANTOOLS_TRACE").isSome then
    IO.eprintln s!"[lsp] <- {(msg.map fun m => (toJson m).compress.take 1500).getD "EOF"}"
  match msg with
  | none =>
    let pending ← state.atomically do
      let s ← get
      set { s with pending := {}, dead := some "the Lean server stopped" }
      return s.pending
    for (_, p) in pending do p.resolve (.error "the Lean server stopped")
  | some msg =>
    match msg with
    | .response (.num id) result => resolve id.mantissa (.ok result)
    | .responseError (.num id) _ message _ => resolve id.mantissa (.error message)
    | .notification "textDocument/publishDiagnostics" (some params) =>
      if let .ok (p : PublishDiagnosticsParams) := fromJson? (toJson params) then
        state.atomically do
          modify fun s => match s.docs[p.uri]? with
            | some doc => { s with docs := s.docs.insert p.uri (mergeDiagnostics doc p) }
            | none => s
    | .request id _ _ =>
      -- registerCapability, workDoneProgress/create, semanticTokens/refresh: acknowledge
      send stdin writer (.response id Json.null)
    | _ => pure ()
    readLoop stdout stdin writer state
where
  resolve (id : Int) (r : Except String Json) : IO Unit := do
    let p? ← state.atomically do
      let s ← get
      let p? := s.pending[id.toNat]?
      set { s with pending := s.pending.erase id.toNat }
      return p?
    if let some p := p? then p.resolve r

/-- Why a request has no answer. -/
inductive Lsp.Failure where
  | timeout
  | error (why : String)

/-- Sends a request and waits for its response, at most `timeoutMs`. -/
def Lsp.requestOrTimeout (lsp : Lsp) (method : String) (params : Json) (timeoutMs : Nat) :
    IO (Except Lsp.Failure Json) := do
  let p : IO.Promise (Except String Json) ← IO.Promise.new
  let id? ← lsp.state.atomically do
    let s ← get
    if let some why := s.dead then return Except.error why
    set { s with nextId := s.nextId + 1, pending := s.pending.insert s.nextId p }
    return .ok s.nextId
  match id? with
  | .error why => return .error (.error why)
  | .ok id =>
    send lsp.stdin lsp.writer (.request (.num id) method (structured params))
    -- Sleep outside the shared task pool, so concurrent timers cannot delay replies or each other.
    -- Sleep in steps, so the task ends with the request and does not keep the process alive.
    let timeout ← IO.asTask (prio := .dedicated) do
      let mut waited := 0
      while waited < timeoutMs && !(← p.isResolved) do
        IO.sleep 50
        waited := waited + 50
      return Except.error Lsp.Failure.timeout
    let answer := p.result?.map fun r => (r.getD (.error "the Lean server stopped")).mapError .error
    let r ← IO.waitAny [answer, timeout.map fun r => match r with | .ok e => e | .error e => .error (.error (toString e))]
    -- the answer can come when the wait ends, and the timeout task can be first: take the answer
    if let .error .timeout := r then
      if ← p.isResolved then return ← IO.wait answer
    if let .error _ := r then
      lsp.state.atomically (modify fun s => { s with pending := s.pending.erase id })
    return r

/-- Sends a request and waits for its response, at most `timeoutMs`. There is no default time: a
request of a tool call uses `Lsp.query`, which has the deadline of the call. -/
def Lsp.request (lsp : Lsp) (method : String) (params : Json) (timeoutMs : Nat) :
    IO (Except String Json) := do
  return (← lsp.requestOrTimeout method params timeoutMs).mapError fun
    | .timeout => s!"{method}: no answer after {timeoutMs / 1000} s"
    | .error why => why

/-- The end of a wait that has several steps, such as a check: its first step is the wait for the
diagnostics, and the next steps are requests. `ms` is the whole wait; `stop` is a time of the
monotonic clock. -/
structure Deadline where
  ms : Nat
  stop : Nat

def Deadline.start (ms : Nat) : IO Deadline := return { ms, stop := (← IO.monoMsNow) + ms }

/-- The ms to the deadline; 0 after it. -/
def Deadline.left (d : Deadline) : IO Nat := return d.stop - (← IO.monoMsNow)

/-- Runs `act` in a task and waits for it until `d`; none after `d`. The task is then still
running: the caller must end what it waits for, for example a process that it reads. -/
def Deadline.run {α : Type} (d : Deadline) (act : IO α) : IO (Option α) := do
  let task ← IO.asTask act (prio := .dedicated)
  while !(← IO.hasFinished task) && 0 < (← d.left) do IO.sleep 50
  unless ← IO.hasFinished task do return none
  return some (← IO.ofExcept (← IO.wait task))

def Lsp.notify (lsp : Lsp) (method : String) (params : Json) : IO Unit :=
  send lsp.stdin lsp.writer (.notification method (structured params))

/-- Starts `lake serve` in `root` and initializes it. `env` changes the environment of the server,
and of the Lean code that it runs: `(name, none)` removes a variable. A test can name another
server with `cmd` and `args`. -/
def Lsp.start (root : System.FilePath) (maxOpen : Nat := 16)
    (env : Array (String × Option String) := #[]) (cmd : String := "lake")
    (args : Array String := #["serve"]) : IO Lsp := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := root, env
    stdin := .piped, stdout := .piped, stderr := .null }
  let stdin := IO.FS.Stream.ofHandle child.stdin
  let stdout := IO.FS.Stream.ofHandle child.stdout
  let state ← Std.Mutex.new ({} : LspState)
  let writer ← Std.Mutex.new ()
  let documents ← Std.Mutex.new ()
  let _ ← IO.asTask (prio := .dedicated) (readLoop stdout stdin writer state)
  let lsp0 : Lsp := { root, child, stdin, state, writer, documents, sorryToken := none, maxOpen }
  let rootUri := System.Uri.pathToUri root
  let init ← lsp0.request "initialize" (Json.mkObj [
    ("processId", Json.null), ("rootUri", toJson rootUri),
    ("capabilities", Json.mkObj [
      ("textDocument", Json.mkObj [("semanticTokens", Json.mkObj [
        ("requests", Json.mkObj [("full", true)]),
        ("tokenTypes", toJson (#[] : Array String)), ("tokenModifiers", toJson (#[] : Array String)),
        ("formats", toJson #["relative"])])])])]) (timeoutMs := 120000)
  let init ← IO.ofExcept (init.mapError IO.userError)
  lsp0.notify "initialized" (Json.mkObj [])
  let legend := init.getObjValD "capabilities" |>.getObjValD "semanticTokensProvider"
    |>.getObjValD "legend" |>.getObjValD "tokenTypes"
  let types : Array String := (fromJson? legend).toOption.getD #[]
  return { lsp0 with sorryToken := types.idxOf? "leanSorryLike" }

/-- Stops the server; the reader task ends with its output. -/
def Lsp.stop (lsp : Lsp) : IO Unit := do
  let _ ← lsp.request "shutdown" Json.null (timeoutMs := 10000)
  lsp.notify "exit" Json.null
  let _ ← lsp.child.wait

/-- Closes idle documents beyond `maxOpen`. The caller holds `documents`. Active operations may
temporarily exceed the limit. The document just synced also stays open. -/
private def Lsp.evict (lsp : Lsp) (keep : Option DocumentUri := none) : IO Unit := do
  let gone ← lsp.state.atomically do
    let s ← get
    let n := s.recent.size - min s.recent.size lsp.maxOpen
    let gone := (s.recent.filter fun uri => s.active[uri]?.getD 0 == 0 && keep != some uri).extract 0 n
    set { s with recent := s.recent.filter (!gone.contains ·),
                 docs := gone.foldl (·.erase ·) s.docs }
    return gone
  for uri in gone do
    IO.eprintln s!"[lsp] close {uri}: LRU (maxOpen={lsp.maxOpen})"
    lsp.notify "textDocument/didClose" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)])])

/-- Keeps `path` open for a full operation, including follow-up goal and token requests. Nested
operations use a reference count. The lease is released on success and on exceptions. -/
def Lsp.withDocument {α : Type} (lsp : Lsp) (path : System.FilePath) (action : IO α) : IO α := do
  let uri := lsp.uriOf path
  lsp.documents.atomically do
    lsp.state.atomically (modify fun s => { s with active := s.active.insert uri (s.active[uri]?.getD 0 + 1) })
  try action
  finally
    lsp.documents.atomically do
      lsp.state.atomically (modify fun s =>
        let n := s.active[uri]?.getD 0
        { s with active := if n ≤ 1 then s.active.erase uri else s.active.insert uri (n - 1) })
      lsp.evict

/-- Makes the server's copy of `path` equal to `text`; returns the uri and the version. Use
`withDocument` around this call and all follow-up requests to prevent eviction between them. -/
def Lsp.sync (lsp : Lsp) (path : System.FilePath) (text : String) : IO (DocumentUri × Nat) := lsp.documents.atomically do
  let uri := lsp.uriOf path
  let action ← lsp.state.atomically do
    let s ← get
    let recent := s.recent.filter (· != uri) |>.push uri
    match s.docs[uri]? with
    | some doc =>
      if doc.text == text then
        set { s with recent }
        return (none, doc.version)
      let v := doc.version + 1
      set { s with recent, docs := s.docs.insert uri { version := v, text } }
      return (some false, v)
    | none =>
      set { s with recent, docs := s.docs.insert uri { version := 1, text } }
      return (some true, 1)
  match action with
  | (none, v) => return (uri, v)
  | (some isNew, v) =>
    if isNew then
      lsp.notify "textDocument/didOpen" (Json.mkObj [("textDocument", Json.mkObj [
        ("uri", toJson uri), ("languageId", "lean4"), ("version", toJson v), ("text", toJson text)])])
      lsp.evict (some uri)
    else
      lsp.notify "textDocument/didChange" (Json.mkObj [
        ("textDocument", Json.mkObj [("uri", toJson uri), ("version", toJson v)]),
        ("contentChanges", toJson #[Json.mkObj [("text", toJson text)]])])
    return (uri, v)

/-- Closes `uri`; the server ends its file worker. The next `sync` opens it again. -/
def Lsp.close (lsp : Lsp) (uri : DocumentUri) (reason : String := "requested") : IO Unit := lsp.documents.atomically do
  lsp.state.atomically (modify fun s => { s with recent := s.recent.filter (· != uri), docs := s.docs.erase uri })
  IO.eprintln s!"[lsp] close {uri}: {reason}"
  lsp.notify "textDocument/didClose" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)])])

/-- Waits until the server has elaborated `uri` at `version`; returns its diagnostics. An
elaboration that takes more than the time left to `d` is stopped: the document is closed. -/
def Lsp.diagnostics (lsp : Lsp) (uri : DocumentUri) (version : Nat) (d : Deadline) :
    IO (Except String (Array Diagnostic)) := do
  match ← lsp.requestOrTimeout "textDocument/waitForDiagnostics"
      (Json.mkObj [("uri", toJson uri), ("version", toJson version)]) (← d.left) with
  | .error .timeout =>
    lsp.close uri s!"diagnostics timeout after {d.ms} ms"
    return .error s!"the check did not end in {d.ms / 1000} s, and it was stopped. A step that \
      takes this long is too expensive: split it into smaller lemmas, or use a targeted tactic \
      (`bv_omega only [h]`, `simp only [...]`, an explicit lemma) in place of a search"
  | .error (.error e) => return .error e
  | .ok _ =>
    let doc? ← lsp.state.atomically do return (← get).docs[uri]?
    match doc?.filter (·.version == version) with
    | some doc => return .ok doc.diagnostics
    | none => return .error "the document changed or closed before its diagnostics were read"

/-- A request about the open document `uri`, after its diagnostics, that must end in the time left
to `d`. After a timeout the document is closed, as for the diagnostics: the server ends its worker,
which may be stuck on the request. -/
def Lsp.queryOrTimeout (lsp : Lsp) (uri : DocumentUri) (method : String) (params : Json) (d : Deadline) :
    IO (Except Lsp.Failure Json) := do
  let r ← lsp.requestOrTimeout method params (← d.left)
  if let .error .timeout := r then lsp.close uri s!"{method} timeout after {d.ms} ms"
  return r

/-- The message of a timeout of `Lsp.queryOrTimeout`. -/
def Lsp.timeoutMessage (method : String) (d : Deadline) : String :=
  s!"{method}: no answer in the {d.ms / 1000} s of the check, and the file was closed in the server"

/-- As `queryOrTimeout`, with an error text for each failure. -/
def Lsp.query (lsp : Lsp) (uri : DocumentUri) (method : String) (params : Json) (d : Deadline) :
    IO (Except String Json) := do
  return (← lsp.queryOrTimeout uri method params d).mapError fun
    | .timeout => Lsp.timeoutMessage method d
    | .error why => why

def positionJson (uri : DocumentUri) (line char : Nat) : Json :=
  Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)]),
              ("position", Json.mkObj [("line", toJson line), ("character", toJson char)])]

/-- Decode the relative semantic tokens. Missing or malformed data does not establish that a
file has no proof holes. Each token has five nonnegative integers and a positive length. -/
def sorryPositionsOfTokens (kind : Nat) (response : Json) : Except String (Array (Nat × Nat)) := do
  let data ← (response.getObjValAs? (Array Nat) "data").mapError fun _ =>
    "proof-hole detection failed: semanticTokens/full has no array of nonnegative token data"
  unless data.size % 5 == 0 do
    throw "proof-hole detection failed: semanticTokens/full token data is not a multiple of five"
  let mut line := 0
  let mut char := 0
  let mut out := #[]
  for i in [0:data.size / 5] do
    let dl := data[5 * i]!
    let dc := data[5 * i + 1]!
    unless data[5 * i + 2]! > 0 do
      throw "proof-hole detection failed: semanticTokens/full contains a zero-length token"
    line := line + dl
    char := if dl == 0 then char + dc else dc
    if data[5 * i + 3]! == kind then out := out.push (line, char)
  return out

/-- The start positions (line, UTF-16 character, from 0) of the `sorry`-like semantic tokens.
Lean does not emit these for term `sorry`; `Workspace.check` also reads source syntax. -/
def Lsp.sorryPositions (lsp : Lsp) (uri : DocumentUri) (d : Deadline) :
    IO (Except Lsp.Failure (Array (Nat × Nat))) := do
  let some kind := lsp.sorryToken
    | return .error (.error "proof-hole status is unknown: the Lean server has no leanSorryLike token type")
  match ← lsp.queryOrTimeout uri "textDocument/semanticTokens/full"
      (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)])]) d with
  | .error e => return .error e
  | .ok r => return (sorryPositionsOfTokens kind r).mapError .error

end LeanTools
