import LeanTools
import LeanTools.Http
import Test.Harness

/-!
Integration tests against a real Lean project: `integration <project root>`. The project must
build `Kraken`; the fixtures are written to `<root>/.leantools/test/`.
-/

open LeanTools Test Lean Lsp

namespace Test.Integration

def fixture (thm : String) (third : String) : String := s!"import Kraken.StateCfg
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open scoped Program.WP

set_option experimental.vcgen true

def touch : Program := parse(\"
touch:
  ret
\")

theorem {thm} [Host] [FunDecls] [Embeds touch] (c : MachineData) (ra : Int64) :
    ⦃ fun s₀ => s₀ = c.push64 ra ⦄ touch ⦃ fun _ _ => False; fun a t => a = ra ∧ t.regs.rsp = c.regs.rsp ⦄ := by
  vcgen [touch]
    invariants
    · fun \{s₀} l s' => match l with
        | \"touch\" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with skip
  case vc1 => sorry
  case vc2 => sorry
  case vc3 => {third}
"

def errors (ds : Array Diagnostic) : Array Diagnostic :=
  ds.filter (·.severity? == some .error)

def suite (root : System.FilePath) : T Unit := do
  let dir := root / ".leantools" / "test"
  IO.FS.createDirAll dir
  let lsp ← Lsp.start root
  let path := dir / "Fixture.lean"
  let text := fixture "touch_go" "exact foo"
  IO.FS.writeFile path text
  let (uri, v) ← lsp.sync path text
  checkEq "first version" v 1
  match ← lsp.diagnostics uri v (← Deadline.start 600000) with
  | .error e => check "diagnostics" false e
  | .ok ds =>
    checkEq "one error" ((errors ds).map (·.message)) #["Unknown identifier `foo`"]
  match ← lsp.sorryPositions uri (← Deadline.start 600000) with
  | .error _ => check "sorry positions" false
  | .ok ps =>
    checkEq "sorry positions (line, char from 0)" ps #[(24, 14), (25, 14)]
    if let some (l, c) := ps[0]? then
      match ← lsp.query uri "$/lean/plainGoal" (positionJson uri l c) (← Deadline.start 600000) with
      | .error e => check "goal at sorry" false e
      | .ok g =>
        let goals : Array String := (fromJson? (g.getObjValD "goals")).toOption.getD #[]
        check "goal at sorry" (goals.any (·.endsWith "⊢ t✝ = c.push64 ra")) s!"{goals}"
  -- an edit: the server elaborates the new version
  let text2 := fixture "touch_go" "sorry"
  let (_, v2) ← lsp.sync path text2
  checkEq "second version" v2 2
  match ← lsp.diagnostics uri v2 (← Deadline.start 600000) with
  | .error e => check "diagnostics after edit" false e
  | .ok ds => checkEq "no errors after edit" (errors ds).size 0
  -- the same text again is not a new version
  let (_, v3) ← lsp.sync path text2
  checkEq "unchanged text keeps the version" v3 2
  -- two files at once
  let paths := #[dir / "A.lean", dir / "B.lean"]
  for p in paths do IO.FS.writeFile p (fixture "t" "exact foo")
  let tasks ← paths.mapM fun p => IO.asTask do
    let t ← IO.FS.readFile p
    let (u, v) ← lsp.sync p t
    lsp.diagnostics u v (← Deadline.start 600000)
  for t in tasks do
    match ← IO.wait t with
    | .ok (.ok ds) => checkEq "parallel file has one error" (errors ds).size 1
    | .ok (.error e) => check "parallel file" false e
    | .error e => check "parallel file" false (toString e)
  lsp.stop

end Test.Integration

/-- With `LEANTOOLS_TEST_HTTPS_URL` set, an HTTPS GET of it must give status 200: TLS, the
certificate check and the proxy of the environment. -/
def https : T Unit := do
  let some url ← IO.getEnv "LEANTOOLS_TEST_HTTPS_URL" | return
  match ← LeanTools.Http.request "GET" url (timeoutMs := 30000) with
  | .ok r => checkEq s!"HTTPS GET {url}" r.status 200
  | .error e => check s!"HTTPS GET {url}" false e

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "."
  Test.run [("HTTPS", https), ("Integration", Test.Integration.suite (← IO.FS.realPath root))]
