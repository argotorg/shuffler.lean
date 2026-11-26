import LeanTools.RunMetadata
import Test.Harness

open Lean LeanTools.RunMetadata Test

namespace Test.RunMetadata

def git (root : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output {
    cmd := "git", cwd := root
    args := #["-c", "user.name=RunMetadata test", "-c", "user.email=metadata@example.invalid",
      "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null"] ++ args }
  unless out.exitCode == 0 do throw (IO.userError s!"fixture Git command failed: {out.stderr}")
  return out.stdout.trimAscii.toString

def digest (metadata : Json) : IO String :=
  match metadata.getObjValAs? String "source_sha256" with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def sourceSuite : T Unit := IO.FS.withTempDir fun temp => do
  let repo := temp / "repo"
  let outside := temp / "outside"
  IO.FS.createDirAll repo
  IO.FS.createDirAll outside
  let missing ← source outside
  checkEq "source: non-repository commit" (missing.getObjValD "source_commit").compress "null"
  checkEq "source: non-repository digest" (missing.getObjValD "source_sha256").compress "null"

  let _ ← git repo #["init", "--quiet", "--template="]
  let _ ← git repo #["config", "core.excludesFile", "/dev/null"]
  IO.FS.writeFile (repo / ".gitignore") ".leantools/\n.lake/\nignored-state/\n"
  let tracked := repo / "Tracked.lean"
  IO.FS.writeFile tracked "def trackedValue : Nat := 1\n"
  let _ ← git repo #["add", "--", ".gitignore", "Tracked.lean"]
  let _ ← git repo #["commit", "--quiet", "--message", "Seed source fixture"]
  let commit ← git repo #["rev-parse", "HEAD"]
  let baseline ← source repo
  checkEq "source: identifies HEAD" (baseline.getObjValD "source_commit").compress (toJson commit).compress
  checkEq "source: unchanged source has the same digest" (← source repo).compress baseline.compress

  let untracked := repo / "Untracked source.lean"
  IO.FS.writeFile untracked "def untrackedValue : Nat := 2\n"
  let added ← source repo
  check "source: untracked source changes the digest" ((← digest added) != (← digest baseline))
  IO.FS.writeFile untracked "def untrackedValue : Nat := 3\n"
  let edited ← source repo
  check "source: content edits change the digest" ((← digest edited) != (← digest added))
  checkEq "source: working edits keep the baseline commit" (edited.getObjValD "source_commit").compress (toJson commit).compress

  for dir in [".leantools", ".lake", "ignored-state"] do
    IO.FS.createDirAll (repo / dir)
    IO.FS.writeFile (repo / dir / "state") "first state\n"
  checkEq "source: ignored state does not change the digest" (← source repo).compress edited.compress
  IO.FS.writeFile (repo / ".leantools" / "state") "second state\n"
  checkEq "source: ignored state edits do not change the digest" (← source repo).compress edited.compress

  IO.FS.writeFile tracked "def trackedValue : Nat := 4\n"
  let trackedEdit ← source repo
  check "source: tracked content edits change the digest" ((← digest trackedEdit) != (← digest edited))
  IO.FS.writeFile tracked "def trackedValue : Nat := 1\n"
  checkEq "source: restoring tracked content restores the digest" (← source repo).compress edited.compress

  IO.FS.removeFile tracked
  let deleted ← source repo
  check "source: tracked deletion changes the digest" ((← digest deleted) != (← digest edited))
  checkEq "source: tracked deletion keeps the baseline commit" (deleted.getObjValD "source_commit").compress (toJson commit).compress

  for i in List.range 130 do
    IO.FS.writeFile (repo / s!"Batch {i}.lean") s!"def value{i} := {i}\n"
  IO.FS.writeFile (repo / "Line\nbreak.lean") "def newlineValue := 1\n"
  let batched ← source repo
  IO.FS.writeFile (repo / "Batch 129.lean") "def value129 := 130\n"
  check "source: edits after a hash batch boundary change identity" ((← digest (← source repo)) != (← digest batched))
  IO.FS.writeFile (repo / "Batch 129.lean") "def value129 := 129\n"
  IO.FS.writeFile (repo / "Line\nbreak.lean") "def newlineValue := 2\n"
  check "source: newline file names keep their content hash" ((← digest (← source repo)) != (← digest batched))

def dependencyNamed (metadata : Json) (name : String) : Json :=
  let dependencies : Array Json := (fromJson? (metadata.getObjValD "source_dependencies")).toOption.getD #[]
  (dependencies.find? fun dep => (dep.getObjValAs? String "name").toOption == some name).getD .null

def pathDependencySuite : T Unit := IO.FS.withTempDir fun repo => do
  let _ ← git repo #["init", "--quiet", "--template="]
  let _ ← git repo #["config", "core.excludesFile", "/dev/null"]
  IO.FS.writeFile (repo / ".gitignore") ".dependency/\nnot-git-dependency/\nmissing-dependency/\n"
  let manifest := Json.mkObj [("packages", toJson ([
    Json.mkObj [("name", "Dependency"), ("type", "path"), ("dir", ".dependency")],
    Json.mkObj [("name", "Missing"), ("type", "path"), ("dir", "missing-dependency")],
    Json.mkObj [("name", "NonGit"), ("type", "path"), ("dir", "not-git-dependency")],
    Json.mkObj [("name", "Remote"), ("type", "git")]
    ] : List Json))]
  IO.FS.writeFile (repo / "lake-manifest.json") manifest.compress
  IO.FS.createDirAll (repo / "not-git-dependency")
  IO.FS.writeFile (repo / "not-git-dependency" / "Source.lean") "def nonGitValue := 0\n"
  let _ ← git repo #["add", "--", ".gitignore", "lake-manifest.json"]
  let _ ← git repo #["commit", "--quiet", "--message", "Seed root manifest"]

  let dep := repo / ".dependency"
  IO.FS.createDirAll dep
  let _ ← git dep #["init", "--quiet", "--template="]
  let _ ← git dep #["config", "core.excludesFile", "/dev/null"]
  IO.FS.writeFile (dep / ".gitignore") ".lake/\n.leantools/\nignored-state/\n"
  let depSource := dep / "Dependency.lean"
  IO.FS.writeFile depSource "def dependencyValue := 1\n"
  let _ ← git dep #["add", "--", ".gitignore", "Dependency.lean"]
  let _ ← git dep #["commit", "--quiet", "--message", "Seed dependency source"]
  let depCommit ← git dep #["rev-parse", "HEAD"]

  let baseline ← source repo
  let metadata := dependencyNamed baseline "Dependency"
  checkEq "dependency: records its commit" (metadata.getObjValD "source_commit").compress (toJson depCommit).compress
  check "dependency: records its content digest" ((metadata.getObjValAs? String "source_sha256").isOk) metadata.compress
  checkEq "dependency: missing path is explicit"
    ((dependencyNamed baseline "Missing").getObjValD "status").compress (toJson "missing").compress
  checkEq "dependency: ignored non-Git path is explicit"
    ((dependencyNamed baseline "NonGit").getObjValD "status").compress (toJson "tree").compress
  checkEq "dependency: non-path packages are omitted" (dependencyNamed baseline "Remote").compress "null"
  let nonGit := dependencyNamed baseline "NonGit"
  check "dependency: non-Git content has a digest" ((nonGit.getObjValAs? String "source_sha256").isOk)
  checkEq "dependency: non-Git content has no commit" (nonGit.getObjValD "source_commit").compress "null"
  IO.FS.writeFile (repo / "not-git-dependency" / "Source.lean") "def nonGitValue := 1\n"
  let nonGitEdited ← source repo
  check "dependency: non-Git source edits change the aggregate digest" ((← digest nonGitEdited) != (← digest baseline))
  IO.FS.createDirAll (repo / "not-git-dependency" / ".lake")
  IO.FS.writeFile (repo / "not-git-dependency" / ".lake" / "state") "build state\n"
  checkEq "dependency: non-Git build state does not change identity" (← source repo).compress nonGitEdited.compress
  IO.FS.writeFile (repo / "not-git-dependency" / "Source.lean") "def nonGitValue := 0\n"

  IO.FS.writeFile depSource "def dependencyValue := 2\n"
  let edited ← source repo
  check "dependency: source edits change the aggregate digest" ((← digest edited) != (← digest baseline))
  check "dependency: source edits change its content digest"
    (((dependencyNamed edited "Dependency").getObjValD "source_sha256").compress !=
      (metadata.getObjValD "source_sha256").compress)
  for dir in [".lake", ".leantools", "ignored-state"] do
    IO.FS.createDirAll (dep / dir)
    IO.FS.writeFile (dep / dir / "state") "ignored dependency state\n"
  checkEq "dependency: ignored state does not change source identity" (← source repo).compress edited.compress
  IO.FS.writeFile (dep / ".lake" / "state") "changed ignored state\n"
  checkEq "dependency: ignored state edits do not change source identity" (← source repo).compress edited.compress
  IO.FS.writeFile (dep / "Untracked.lean") "def helperValue := 3\n"
  let untracked ← source repo
  check "dependency: untracked source changes the aggregate digest" ((← digest untracked) != (← digest edited))
  let _ ← git dep #["add", "--all"]
  let _ ← git dep #["commit", "--quiet", "--message", "Record dependency edit"]
  let committed ← source repo
  check "dependency: its commit enters the aggregate digest" ((← digest committed) != (← digest untracked))
  checkEq "dependency: committing leaves its content digest"
    ((dependencyNamed committed "Dependency").getObjValD "source_sha256").compress
    ((dependencyNamed untracked "Dependency").getObjValD "source_sha256").compress
  IO.FS.removeFile depSource
  let deleted ← source repo
  check "dependency: tracked deletion changes the aggregate digest" ((← digest deleted) != (← digest committed))
  IO.FS.writeFile (repo / "lake-manifest.json") "{\"packages\":[{\"type\":\"path\",\"name\":\"Broken\"}]}"
  let rejected ← try
    let _ ← source repo
    pure false
  catch _ => pure true
  check "dependency: a malformed path entry is rejected" rejected
  IO.FS.writeFile (repo / "lake-manifest.json") manifest.compress
  let link ← IO.Process.output { cmd := "ln", args := #["-s", ".", (repo / "not-git-dependency" / "cycle").toString] }
  unless link.exitCode == 0 do throw (IO.userError "cannot create source cycle fixture")
  let rejected ← try
    let _ ← source repo
    pure false
  catch _ => pure true
  check "dependency: a source directory cycle is rejected" rejected

def suite : T Unit := do
  checkEq "sha256: empty" (← sha256 "") "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  checkEq "sha256: text" (← sha256 "abc") "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  let j := Json.mkObj [("model", "m"), ("apiKey", "secret"), ("extra", Json.arr #[Json.mkObj [
    ("Authorization", "Bearer secret"), ("reasoning", Json.mkObj [("effort", "high")])]])]
  let redacted := (redact j).compress
  check "redact: nested credentials" ((redacted.splitOn "secret").length == 1 && (redacted.splitOn "Bearer").length == 1) redacted
  check "redact: model and effort remain" ((redacted.splitOn "high").length == 2 && (redacted.splitOn "model").length == 2) redacted
  checkEq "redact: idempotent" (redact (redact j)).compress redacted
  for (key, endpoint) in [("baseUrl", "https://user:fixture@example.invalid/v1"),
      ("base_url", "https://example.invalid/v1?api_key=fixture"),
      ("baseURL", "https://example.invalid/v1#fixture")] do
    checkEq s!"redact: credential URL {key}"
      (redact (Json.mkObj [(key, toJson endpoint)])).compress
      (Json.mkObj [(key, toJson "[redacted]")]).compress
  for endpoint in ["https://example.invalid/v1", "http://127.0.0.1:8082/v1", "https://example.invalid/path@version"] do
    let safeEndpoint := Json.mkObj [("baseUrl", toJson endpoint)]
    checkEq s!"redact: retains a URL with no credentials {endpoint}"
      (redact safeEndpoint).compress safeEndpoint.compress
  sourceSuite
  pathDependencySuite

end Test.RunMetadata
