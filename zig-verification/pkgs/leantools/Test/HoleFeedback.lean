import LeanTools.Workspace
import Test.Harness

/-! Proof-hole feedback from the production workspace. Run with
`tests --holes`. Fixtures use private temporary servers. -/

open Lean Lsp LeanTools Test

namespace Test.HoleFeedback

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def fakeServer : String := r#"
import json
import os
import sys

mode = os.environ.get('HOLE_TEST_MODE', '')
texts = {}
versions = {}

def send(body):
    data = json.dumps(body).encode()
    sys.stdout.buffer.write(b'Content-Length: %d\r\n\r\n' % len(data) + data)
    sys.stdout.buffer.flush()

while True:
    length = None
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            sys.exit(0)
        if not line.strip():
            break
        if line.lower().startswith(b'content-length:'):
            length = int(line.split(b':')[1])
    msg = json.loads(sys.stdin.buffer.read(length))
    method = msg.get('method', '')
    params = msg.get('params') or {}
    doc = params.get('textDocument', {})
    uri = doc.get('uri') or params.get('uri')
    if method == 'textDocument/didOpen':
        texts[uri] = doc['text']
        versions[uri] = doc['version']
    elif method == 'textDocument/didChange':
        texts[uri] = params['contentChanges'][-1]['text']
        versions[uri] = doc['version']
    elif method == 'textDocument/didClose':
        texts.pop(uri, None)
    elif method == 'exit':
        break
    elif 'id' in msg:
        result = None
        if method == 'initialize':
            result = {'capabilities': {'semanticTokensProvider': {'legend': {'tokenTypes': ['leanSorryLike']}}}}
        elif method == 'textDocument/waitForDiagnostics':
            diagnostics = []
            if mode == 'diagnostic':
                diagnostics = [{'range': {'start': {'line': 1, 'character': 0}, 'end': {'line': 1, 'character': 7}}, 'severity': 2, 'message': 'declaration uses `sorry`'}]
            send({'jsonrpc': '2.0', 'method': 'textDocument/publishDiagnostics', 'params': {'uri': uri, 'version': versions[uri], 'diagnostics': diagnostics}})
        elif method == 'textDocument/semanticTokens/full':
            result = {
                'missing-data': {},
                'null': None,
                'bad-data': {'data': 'not tokens'},
                'negative': {'data': [0, 0, -1, 0, 0]},
                'short': {'data': [0, 0, 5, 0]},
                'tail': {'data': [0, 0, 5, 0, 0, 1]},
                'zero-length': {'data': [0, 0, 0, 0, 0]},
            }.get(mode, {'data': []})
            if mode == 'query-error':
                send({'jsonrpc': '2.0', 'id': msg['id'], 'error': {'code': -32603, 'message': 'token request failed'}})
                continue
        elif method == '$/lean/plainGoal':
            result = {'goals': ['⊢ True']}
        send({'jsonrpc': '2.0', 'id': msg['id'], 'result': result})
"#

def withWorkspace (mode : Option String) (k : Workspace → T Unit) : T Unit := do
  let root ← IO.FS.createTempDir
  IO.FS.writeFile (root / "lakefile.lean") "import Lake\nopen Lake DSL\npackage holeFeedbackFixture\n"
  let lsp ← match mode with
    | some mode => Lsp.start root (env := #[("HOLE_TEST_MODE", some mode)]) (cmd := "python3") (args := #["-c", fakeServer])
    | none => Lsp.start root (env := #[("LEAN_NUM_THREADS", some "2")])
  let ws : Workspace := {
    root, lsp, self := "/unused-validator", loogleBin := "/unused-loogle"
    config := { checkSeconds := 20 }
    loogle := ← Std.Mutex.new none
    files := ← Std.Mutex.new {}
    checks := ← Std.Semaphore.new 1 }
  try k ws finally
    lsp.stop
    IO.FS.removeDirAll root

def suite : T Unit := do
  for mode in ["missing-data", "null", "bad-data", "negative", "short", "tail", "zero-length", "query-error"] do
    withWorkspace (some mode) fun ws => do
      let r ← ws.check "A.lean" "import Lean\nexample : True := True.intro\n"
      check s!"{mode}: unknown hole status is an error" (match r with
        | .error e => has e "proof-hole" || has e "semanticTokens"
        | .ok _ => false)
  withWorkspace (some "empty") fun ws => do
    let ws := { ws with lsp := { ws.lsp with sorryToken := none } }
    check "missing legend: unknown hole status is an error" (match ← ws.check "A.lean" "import Lean\n" with
      | .error e => has e "proof-hole" || has e "leanSorryLike"
      | .ok _ => false)
  withWorkspace (some "diagnostic") fun ws => do
    match ← ws.check "A.lean" "import Lean\nexample : True := generatedHole\n" with
    | .error e => check "uses-sorry warning is retained" (has e "sorry") e
    | .ok c => check "uses-sorry warning prevents a complete report" (!has (c.format "") "No `sorry`.") (c.format "")

def runtimeSuite : T Unit := withWorkspace none fun ws => do
  for (name, body, count) in [
      ("term sorry", "theorem target : True := sorry\n", 1),
      ("exact sorry", "theorem target : True := by exact sorry\n", 1),
      ("tactic sorry", "theorem target : True := by sorry\n", 1),
      ("custom tactic then term hole", "macro \"noop\" : tactic => `(tactic| skip)\ntheorem target : True := by\n  noop\n  exact sorry\n", 1),
      ("multiple term holes", "theorem target : True ∧ True := ⟨sorry, sorry⟩\n", 2),
      ("live antiquotation", "set_option warn.sorry false\ndef quoted : Lean.MacroM Lean.Syntax := `($((sorry : Lean.TSyntax `term)))\ntheorem target : True := True.intro\n", 1),
      ("suppressed sorry warning", "set_option warn.sorry false\ntheorem target : True := sorry\n", 1),
      ("comments and strings", "-- sorry\n/- sorry /- sorry -/ -/\ndef word := \"sorry\"\ndef raw := r#\"sorry\"#\ntheorem target : True := True.intro\n", 0),
      ("quoted syntax", "def quoted : Lean.MacroM Lean.Syntax := `(sorry)\ntheorem target : True := True.intro\n", 0),
      ("quoted tactic syntax", "def quoted : Lean.MacroM Lean.Syntax := `(tactic| sorry)\ntheorem target : True := True.intro\n", 0),
      ("complete proof", "theorem target : True := True.intro\n", 0)] do
    let text := "import Lean\n" ++ body
    match ← ws.check "A.lean" text with
    | .error e => check s!"{name}: check returns" false e
    | .ok c =>
      check s!"{name}: Lean accepts source" c.errors.isEmpty (c.format text)
      checkEq s!"{name}: hole count" c.sorries.size count
      if 0 < count then
        check s!"{name}: incomplete report" (!has (c.format text) "No `sorry`.") (c.format text)
        check s!"{name}: hole goals" (c.sorries.all fun s => has s.goal "⊢" || has s.goal "Syntax") (c.format text)
  let generated := "import Lean\nmacro \"generatedHole\" : term => `(sorry)\ntheorem target : True := generatedHole\n"
  match ← ws.check "A.lean" generated with
  | .error e => check "generated hole is not complete" (has e "sorry") e
  | .ok c => check "generated hole is not complete" (!has (c.format generated) "No `sorry`.") (c.format generated)
  let original := "import Lean\ntheorem target : True := by sorry\n"
  IO.FS.writeFile (ws.root / "Edited.lean") original
  match ← ws.edit "Edited.lean" "by sorry" "by exact sorry" false with
  | .error e => check "edit reports term hole" false e
  | .ok out => check "edit reports term hole" (has out "1 `sorry`" && has out "True") out
  match ← ws.submit "Edited.lean" "The target still has a hole." with
  | .error e => check "submission rejects hole before validator" (has e "file must have no errors and no `sorry`" && has e "True") e
  | .ok out => check "submission rejects hole before validator" false out
  match ← ws.edit "Edited.lean" "exact sorry" "exact True.intro" false with
  | .error e => check "edit clears the last hole" false e
  | .ok out => check "edit clears the last hole" (has out "No `sorry`.") out

end Test.HoleFeedback
