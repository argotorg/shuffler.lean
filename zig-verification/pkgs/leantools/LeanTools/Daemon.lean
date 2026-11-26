import Std.Async.TCP
import LeanTools.Tools

/-!
# The background process and its client

`leantools daemon` keeps the Lean server, the histories and loogle of one project, and answers
tool calls: one JSON line per connection, `{"token", "tool", "args"}`, answered by one JSON line,
`{"ok", "text"}`. It listens on 127.0.0.1; `.leantools/daemon.json` (mode 600) holds its port,
its pid and the token that a request must carry. Each connection is served in a task of its own,
so tools on different files run in parallel.
-/

open Lean Std Async TCP Net

namespace LeanTools

structure DaemonInfo where
  port : Nat
  token : String
  pid : Nat
deriving ToJson, FromJson

def infoPath (root : System.FilePath) : System.FilePath := stateDir root / "daemon.json"

def loopback (port : Nat) : SocketAddress := .v4 ⟨⟨#v[127, 0, 0, 1]⟩, port.toUInt16⟩

def reply (ok : Bool) (text : String) : Json := Json.mkObj [("ok", toJson ok), ("text", toJson text)]

def handleRequest (ws : Workspace) (token : String) (line : String) : IO (Json × Bool) := do
  match Json.parse line with
  | .error e => return (reply false s!"bad request: {e}", false)
  | .ok j =>
    if argStr? j "token" != some token then return (reply false "bad token", false)
    let name := (argStr? j "tool").getD ""
    if name == "stop" then return (reply true "stopped", true)
    match tools.find? (·.name == name) with
    | none => return (reply false s!"unknown tool {name}; `leantools tools` lists them", false)
    | some t =>
      match ← (t.call ws (j.getObjValD "args")).toBaseIO with
      | .ok (.ok text) => return (reply true text, false)
      | .ok (.error e) => return (reply false e, false)
      | .error e => return (reply false s!"{name} failed: {e}", false)

/-- Reads until a newline or the end of the stream. -/
partial def readLine (c : Socket.Client) (acc : ByteArray := .empty) : Async ByteArray := do
  match ← c.recv? 65536 with
  | none => return acc
  | some b =>
    let acc := acc ++ b
    if b.toList.contains 10 then return acc else readLine c acc

/-- Reads to the end of the stream. -/
partial def readAll (c : Socket.Client) (acc : ByteArray := .empty) : Async ByteArray := do
  match ← c.recv? 65536 with
  | none => return acc
  | some b => readAll c (acc ++ b)

def randomToken : IO String := do
  let bytes ← IO.getRandomBytes 16
  return String.join (bytes.toList.map fun b =>
    let h := "0123456789abcdef".toList
    s!"{h[(b / 16).toNat]!}{h[(b % 16).toNat]!}")

/-- Answers one request. A `stop` removes the info file first, so that later calls start a new
daemon, and answers when the Lean server has stopped. -/
def serveClient (ws : Workspace) (token : String) (c : Socket.Client) : Async Unit := do
  let line := String.fromUTF8! (← readLine c)
  -- Tool calls block on locks, processes and LSP replies. Keep them off the async task pool,
  -- which must remain free to accept clients and run response and timeout continuations.
  let task ← IO.asTask (prio := .dedicated) do
    let (r, stop) ← handleRequest ws token line.trimAscii.toString
    if stop then
      try IO.FS.removeFile (infoPath ws.root) catch _ => pure ()
      ws.lsp.stop
    return (r, stop)
  let (r, stop) ← Async.ofAsyncTask task
  c.sendAll #[(r.compress ++ "\n").toUTF8]
  c.shutdown
  if stop then (IO.Process.exit 0 : IO Unit)

/-- Serves the workspace until a `stop` request. -/
def serve (ws : Workspace) : IO Unit := do
  let token ← randomToken
  let server ← Socket.Server.mk
  server.bind (loopback 0)
  server.listen 128
  let port := match ← server.getSockName with
    | .v4 a => a.port.toNat
    | .v6 a => a.port.toNat
  let info : DaemonInfo := { port, token, pid := (← IO.Process.getPID).toNat }
  IO.FS.createDirAll (stateDir ws.root)
  IO.FS.writeFile (infoPath ws.root) (toJson info).compress
  IO.setAccessRights (infoPath ws.root) { user := { read := true, write := true } }
  IO.eprintln s!"leantools daemon for {ws.root} on port {port}; maxConcurrentChecks={ws.config.maxConcurrentChecks.val}, maxOpen={ws.config.maxOpen}"
  Async.block do
    while true do
      let c ← server.accept
      background (serveClient ws token c)

def readInfo? (root : System.FilePath) : IO (Option DaemonInfo) := do
  let p := infoPath root
  unless ← p.pathExists do return none
  return (Json.parse (← IO.FS.readFile p) >>= fromJson?).toOption

/-- Sends one request and returns the reply, or none if no daemon answers. -/
def send? (info : DaemonInfo) (tool : String) (args : Json) : IO (Option Json) := do
  let req := Json.mkObj [("token", toJson info.token), ("tool", toJson tool), ("args", args)]
  try
    let bytes ← Async.block do
      let c ← Socket.Client.mk
      c.connect (loopback info.port)
      c.sendAll #[(req.compress ++ "\n").toUTF8]
      readAll c
    return (Json.parse (String.fromUTF8! bytes)).toOption
  catch _ => return none

/-- Starts a daemon for `root`, detached from the caller, and waits for its info file. -/
def startDaemon (root : System.FilePath) : IO DaemonInfo := do
  IO.FS.createDirAll (stateDir root)
  if ← (infoPath root).pathExists then IO.FS.removeFile (infoPath root)
  let self ← IO.appPath
  let log := stateDir root / "daemon.log"
  let _ ← IO.Process.spawn {
    cmd := "sh", cwd := root, stdin := .null, stdout := .null, stderr := .null
    args := #["-c", "exec setsid \"$0\" daemon --root \"$1\" >>\"$2\" 2>&1 </dev/null &",
      self.toString, root.toString, log.toString] }
  for _ in [0:600] do
    IO.sleep 100
    if let some info ← readInfo? root then return info
  throw (IO.userError s!"the daemon did not start; see {log}")

/-- Calls `tool` on the daemon of `root`, started if none answers. -/
def call (root : System.FilePath) (tool : String) (args : Json) : IO Json := do
  if let some info ← readInfo? root then
    if let some r ← send? info tool args then return r
  if tool == "stop" then return reply true "no daemon was running"
  let info ← startDaemon root
  match ← send? info tool args with
  | some r => return r
  | none => throw (IO.userError "the daemon does not answer")

end LeanTools
