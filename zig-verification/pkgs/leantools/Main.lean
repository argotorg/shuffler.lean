import LeanTools

/-!
# leantools

    leantools tools [--json]          list the tools (as JSON schemas with --json)
    leantools <tool> [ARGS]           call a tool; ARGS is a JSON object, `-` (JSON on stdin),
                                      or `--name value` pairs
    leantools stop                    stop the daemon of the project
    leantools validate ORIG SUB       validate SUB against ORIG (run it with `lake env`)
    leantools daemon [--root DIR]     run the daemon (the client starts it)
    leantools prove FILE [--config C] run the h1 loop on FILE (config: leantools-prove.json)
    leantools ask ARGS                one model call with a budget guard (see LeanTools.AskMain)
    leantools coordinate ARGS         run the repository coordinator

The project is the nearest directory upward with a lakefile, or `$LEANTOOLS_ROOT`.
-/

open Lean LeanTools

partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) then return dir
  match dir.parent with
  | some p => if p == dir then throw (IO.userError "no lakefile found upward") else findRoot p
  | none => throw (IO.userError "no lakefile found upward")

def projectRoot : IO System.FilePath := do
  match ← IO.getEnv "LEANTOOLS_ROOT" with
  | some r => IO.FS.realPath r
  | none => findRoot (← IO.FS.realPath (← IO.currentDir))

/-- `--name value` pairs as a JSON object; a value that parses as JSON is kept as JSON. -/
def parsePairs : List String → Except String (List (String × Json))
  | [] => .ok []
  | k :: v :: rest =>
    if k.startsWith "--" then do
      let val := match Json.parse v with
        | .ok j@(.num _) | .ok j@(.bool _) => j
        | _ => .str v
      return ((k.drop 2).toString, val) :: (← parsePairs rest)
    else .error s!"expected --name, not {k}"
  | [k] => .error s!"{k} has no value"

def loadConfig (root : System.FilePath) : IO Config := do
  let p := root / "leantools.json"
  unless ← p.pathExists do return {}
  match Json.parse (← IO.FS.readFile p) >>= fromJson? with
  | .ok c => return c
  | .error e => throw (IO.userError s!"leantools.json: {e}")

def runDaemon (root : System.FilePath) : IO Unit := do
  let config ← loadConfig root
  let self ← IO.appPath
  -- $LEANTOOLS_LOOGLE (set by the nix package), else the lake build tree:
  -- .lake/build/bin/leantools → .lake/packages/loogle/.lake/build/bin/loogle
  let lakeDir := ((self.parent.bind (·.parent)).bind (·.parent)).getD "."
  let loogleBin : System.FilePath := (← IO.getEnv "LEANTOOLS_LOOGLE").getD
    (lakeDir / "packages" / "loogle" / ".lake" / "build" / "bin" / "loogle").toString
  let lsp ← Lsp.start root config.maxOpen
  let loogle ← Std.Mutex.new none
  let files ← Std.Mutex.new {}
  let ws : Workspace := { root, config, lsp, self, loogleBin, loogle, files, checks := ← Std.Semaphore.new config.maxConcurrentChecks.val }
  serve ws

def main (args : List String) : IO UInt32 := do
  match args with
  | ["tools"] =>
    IO.println ("\n\n".intercalate (tools.toList.map Tool.usage))
    return 0
  | ["tools", "--json"] =>
    IO.println (toJson (tools.map Tool.schema)).pretty
    return 0
  | ["validate", orig, sub] =>
    initSearchPath (← findSysroot)
    unsafe enableInitializersExecution
    let v ← validate orig sub
    IO.println (Json.mkObj [("problems", toJson v.problems), ("theorems", toJson (v.theorems.map toString)),
      ("disproved", toJson (v.disproved.map toString))]).compress
    return 0
  | ["prove", file] =>
    let root ← projectRoot
    runProve root file (root / "leantools-prove.json")
  | ["prove", file, "--config", c] => runProve (← projectRoot) file (← IO.FS.realPath c)
  | "ask" :: rest => runAsk (← projectRoot) rest
  | "coordinate" :: rest =>
    let root ← projectRoot
    let child ← IO.Process.spawn { cmd := "lake", args := #["exe", "coordinator"] ++ rest.toArray, cwd := root }
    child.wait
  | ["daemon"] => runDaemon (← projectRoot); return 0
  | ["daemon", "--root", r] => runDaemon (← IO.FS.realPath r); return 0
  | tool :: rest =>
    let args ← match rest with
      | [] => pure (Json.mkObj [])
      | ["-"] => IO.ofExcept ((Json.parse (← (← IO.getStdin).readToEnd)).mapError IO.userError)
      | [j] => if j.startsWith "{" then IO.ofExcept ((Json.parse j).mapError IO.userError)
               else IO.ofExcept ((parsePairs rest).map Json.mkObj |>.mapError IO.userError)
      | _ => IO.ofExcept ((parsePairs rest).map Json.mkObj |>.mapError IO.userError)
    let r ← call (← projectRoot) tool args
    let text := (r.getObjValD "text").getStr?.toOption.getD r.compress
    IO.print (if text.endsWith "\n" then text else text ++ "\n")
    return if (r.getObjValD "ok") == .bool true then 0 else 1
  | [] =>
    IO.println "usage: leantools tools | leantools <tool> [ARGS] | leantools stop | leantools validate ORIG SUB"
    return 2
