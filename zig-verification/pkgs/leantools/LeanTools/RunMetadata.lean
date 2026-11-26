import Lean

/-! The hashes and settings that identify a proof run. Credentials are never copied here. -/

open Lean

namespace LeanTools.RunMetadata

def sha256 (text : String) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum" } (some text)
  unless out.exitCode == 0 do throw (IO.userError "sha256sum failed")
  let digest := (out.stdout.splitOn " ").head!
  unless digest.length == 64 && digest.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw (IO.userError "sha256sum returned no digest")
  return digest

def normalizedKey (key : String) : String :=
  key.toLower.replace "_" "" |>.replace "-" ""

def sensitive (key : String) : Bool :=
  let key := normalizedKey key
  ["apikey", "authorization", "password", "secret", "accesstoken", "refreshtoken", "headers"].any
    fun part => (key.splitOn part).length > 1

/-- URL settings with userinfo, queries, or fragments may carry credentials. -/
def sensitiveUrl (key : String) (value : Json) : Bool :=
  if !(normalizedKey key).endsWith "url" then false
  else match value with
    | .str url =>
      let afterScheme := ((url.splitOn "://").drop 1).headD url
      let authority := afterScheme.toList.takeWhile fun c => c != '/' && c != '?' && c != '#'
      authority.contains '@' || url.contains '?' || url.contains '#'
    | _ => false

/-- Keep the shape of nested configuration data, replacing credential fields and URLs. -/
partial def redact : Json → Json
  | .obj fields => Json.mkObj (fields.toArray.toList.map fun (key, value) =>
      (key, if sensitive key || sensitiveUrl key value then toJson "[redacted]" else redact value))
  | .arr values => .arr (values.map redact)
  | value => value

/-- Hash bounded batches. NUL records preserve file names that contain newlines. -/
private def fileHashes (root : System.FilePath) (paths : Array String) : IO (List (String × String)) := do
  let present ← paths.filterM fun (path : String) => do
    let full := root / path
    return (← full.pathExists) && !(← full.isDir)
  let batches ← (List.range ((present.size + 127) / 128)).mapM fun i => do
    let batch := present.extract (128 * i) (128 * (i + 1))
    let out ← IO.Process.output { cmd := "sha256sum", args := #["-z", "--"] ++ batch.map (fun (p : String) => (root / p).toString) }
    unless out.exitCode == 0 do throw (IO.userError "cannot hash source files")
    let records := (out.stdout.splitOn "\x00").filter (!·.isEmpty)
    unless records.length == batch.size do throw (IO.userError "sha256sum returned the wrong record count")
    batch.toList.zip records |>.mapM fun (path, record) => do
      let digest := (record.take 64).toString
      unless digest.length == 64 && digest.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
        throw (IO.userError "sha256sum returned no digest")
      return (path, digest)
  let found := batches.flatten
  return paths.toList.map fun path => (path, (found.lookup path).getD "[absent]")

/-- Hash Git's working source manifest, including untracked source and excluding ignored state. -/
private def gitSource (root : System.FilePath) : IO Json := do
  let commit ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"], cwd := root }
  let files ← IO.Process.output {
    cmd := "git", args := #["ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd := root }
  if files.exitCode != 0 then return Json.mkObj [("source_commit", .null), ("source_sha256", .null)]
  let paths := ((files.stdout.splitOn "\x00").filter (!·.isEmpty)).toArray.qsort (· < ·)
  let entries ← fileHashes root paths
  return Json.mkObj [
    ("source_commit", if commit.exitCode == 0 then toJson commit.stdout.trimAscii.toString else .null),
    ("source_sha256", toJson (← sha256 (toJson entries).compress))]

private structure PathDependency where
  name : String
  dir : String

private def pathDependencies (manifest : Json) : Except String (Array PathDependency) := do
  let packages ← manifest.getObjValAs? (Array Json) "packages"
  let mut dependencies := #[]
  for package in packages do
    if (← package.getObjValAs? String "type") == "path" then
      dependencies := dependencies.push {
        name := ← package.getObjValAs? String "name"
        dir := ← package.getObjValAs? String "dir" }
  return dependencies

/-- A path dependency can be a source archive. Hash its files without build state.
Directory cycles and special files are refused instead of omitting source. -/
private partial def treeEntries (root : System.FilePath) (relative : String)
    (ancestors : List System.FilePath) : IO (List String) := do
  let path := root / relative
  let real ← IO.FS.realPath path
  if ancestors.contains real then throw (IO.userError s!"source directory cycle: {path}")
  let entries ← (← path.readDir).toList.mapM fun entry => do
    if [".git", ".lake", ".leantools", ".skel"].contains entry.fileName then return []
    let rel := if relative.isEmpty then entry.fileName else (System.FilePath.mk relative / entry.fileName).toString
    match (← entry.path.metadata).type with
    | .dir => treeEntries root rel (real :: ancestors)
    | .file => return [rel]
    | _ => throw (IO.userError s!"unsupported source file: {entry.path}")
  return entries.flatten

private def treeSource (path : System.FilePath) : IO Json := do
  let paths := (← treeEntries path "" []).toArray.qsort (· < ·)
  let entries ← fileHashes path paths
  return Json.mkObj [("status", toJson "tree"), ("source_commit", .null),
    ("source_sha256", toJson (← sha256 (toJson entries).compress))]

private def dependencySource (root : System.FilePath) (dependency : PathDependency) : IO Json := do
  let base := Json.mkObj [("name", toJson dependency.name), ("dir", toJson dependency.dir)]
  let unavailable (status : String) := base.mergeObj (Json.mkObj [
    ("status", toJson status), ("source_commit", .null), ("source_sha256", .null)])
  let path := root / dependency.dir
  unless ← path.isDir do return unavailable "missing"
  let top ← IO.Process.output { cmd := "git", args := #["rev-parse", "--show-toplevel"], cwd := path }
  if top.exitCode != 0 then return base.mergeObj (← treeSource path)
  -- An archive must not inherit the enclosing project's Git identity.
  if (← IO.FS.realPath path) != (← IO.FS.realPath top.stdout.trimAscii.toString) then
    return base.mergeObj (← treeSource path)
  return base.mergeObj (← gitSource path) |>.mergeObj (Json.mkObj [("status", toJson "git")])

/-- Identify the root source and the path dependencies listed in its Lake manifest.
Git dependencies use their ignore rules; archives omit build state. Dependency identities enter the aggregate hash. -/
def source (root : System.FilePath) : IO Json := do
  let rootSource ← gitSource root
  if rootSource.getObjValD "source_sha256" == .null then return rootSource
  let manifest := root / "lake-manifest.json"
  let dependencies ← if !(← manifest.pathExists) then pure #[] else do
    let parsed := Json.parse (← IO.FS.readFile manifest) >>= pathDependencies
    let packages ← match parsed with
      | .ok packages => pure packages
      | .error e => throw (IO.userError s!"cannot read Lake path dependencies: {e}")
    packages.mapM (dependencySource root)
  let identity := Json.mkObj [
    ("root", rootSource.getObjValD "source_sha256"), ("dependencies", toJson dependencies)]
  return rootSource.mergeObj (Json.mkObj [
    ("source_dependencies", toJson dependencies),
    ("source_sha256", toJson (← sha256 identity.compress))])

end LeanTools.RunMetadata
