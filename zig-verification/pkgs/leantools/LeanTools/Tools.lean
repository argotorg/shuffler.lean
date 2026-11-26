import LeanTools.Workspace

/-!
# The tool registry

Each tool has a name, a description for the agent, its parameters, and its action on a workspace.
The names and the limits follow h1 (Moalla et al. 2026, Table 3).
-/

open Lean

namespace LeanTools

structure Param where
  name : String
  type : String
  description : String
  required : Bool := true
  /-- The JSON schema of the elements, for a parameter of type `array`. -/
  items : Option Json := none

structure Tool where
  name : String
  description : String
  params : Array Param
  run : Workspace → Json → IO (Except String String)

def argStr (j : Json) (k : String) : Except String String :=
  match j.getObjValD k with
  | .str s => .ok s
  | .null => .error s!"{k} is required"
  | v => .error s!"{k} must be a string, not {v.compress}"

def argStr? (j : Json) (k : String) : Option String := (j.getObjValD k).getStr?.toOption

/-- An optional string argument: none when it is missing, an error when it is not a string. -/
def argOptStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjValD k with
  | .null => .ok none
  | .str s => .ok (some s)
  | v => .error s!"{k} must be a string, not {v.compress}"

def argNat? (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjValD k with
  | .null => .ok none
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then .ok (some n.mantissa.toNat) else .error s!"{k} must be a natural number"
  | .str s => match s.toNat? with
    | some n => .ok (some n)
    | none => .error s!"{k} must be a natural number"
  | v => .error s!"{k} must be a natural number, not {v.compress}"

def argNat (j : Json) (k : String) : Except String Nat := do
  match ← argNat? j k with
  | some n => .ok n
  | none => .error s!"{k} is required"

def argBool (j : Json) (k : String) (default : Bool) : Except String Bool :=
  match j.getObjValD k with
  | .null => .ok default
  | .bool b => .ok b
  | .str "true" => .ok true
  | .str "false" => .ok false
  | v => .error s!"{k} must be true or false, not {v.compress}"

def file : Param := { name := "file", type := "string", description := "The working file, relative to the project root." }
def line : Param := { name := "line", type := "integer", description := "The line, from 1." }
def column : Param := { name := "column", type := "integer", description := "The column, in characters from 1." }

/-- Runs `k` with the resolved working file; a file on the deny list is refused. -/
def withPath (ws : Workspace) (j : Json) (k : String → IO (Except String String)) : IO (Except String String) :=
  match argStr j "file" >>= ws.resolve with
  | .ok f => do
    if ← ws.isDenied f then return .error (denyMessage f)
    k f
  | .error e => return .error e

def lift {α : Type} (x : Except String α) (k : α → IO (Except String String)) : IO (Except String String) :=
  match x with
  | .ok a => k a
  | .error e => return .error e

/-- The edits of an `edit_working_file` call: `old_string` and `new_string` (the flag is false), or
`edits` (true). -/
def parseEdits (j : Json) : Except String (Bool × List Edit) := do
  let given (k : String) := j.getObjValD k != .null
  if given "edits" then
    if given "old_string" || given "new_string" || given "replace_all" then
      throw "give either old_string and new_string, or edits, not both"
    let some es := (j.getObjValD "edits").getArr?.toOption | throw "edits must be a list of objects with old_string and new_string"
    if es.isEmpty then throw "edits must not be empty"
    let parsed ← es.toList.zipIdx.mapM fun (e, i) => do
      let at_ (m : String) := s!"edits[{i + 1}]: {m}"
      let old ← (argStr e "old_string").mapError at_
      let new ← (argStr e "new_string").mapError at_
      let all ← (argBool e "replace_all" false).mapError at_
      return ({ old, new, all } : Edit)
    return (true, parsed)
  else
    return (false, [{ old := ← argStr j "old_string", new := ← argStr j "new_string", all := ← argBool j "replace_all" false }])

def tools : Array Tool := #[
  { name := "view_working_file"
    description := "Show the working file with line numbers (at most 40,000 bytes; use offset and limit for more)."
    params := #[file,
      { name := "offset", type := "integer", description := "The first line, from 1.", required := false },
      { name := "limit", type := "integer", description := "The most lines to show.", required := false }]
    run := fun ws j => withPath ws j fun f =>
      lift (do return ((← argNat? j "offset").getD 1, ← argNat? j "limit")) fun (o, l) => ws.viewWorking f o l },
  { name := "view_original_file"
    description := "Show the original of the working file (the frozen statements, the target of submit_working_file) and its first check."
    params := #[file,
      { name := "offset", type := "integer", description := "The first line, from 1.", required := false },
      { name := "limit", type := "integer", description := "The most lines to show.", required := false }]
    run := fun ws j => withPath ws j fun f =>
      lift (do return ((← argNat? j "offset").getD 1, ← argNat? j "limit")) fun (o, l) => ws.viewOriginal f o l },
  { name := "view_file"
    description := "Show a file of the project, of Kraken (`.kraken/`) or of the Lean sources with line numbers (at most 40,000 bytes; use offset and limit for more), for example an example proof or a spec library. The path is as grep prints it: relative to the project root, or absolute for the Lean sources. Read-only. A file on the deny list of the project is refused."
    params := #[{ name := "path", type := "string", description := "The file, as grep prints it." },
      { name := "offset", type := "integer", description := "The first line, from 1.", required := false },
      { name := "limit", type := "integer", description := "The most lines to show.", required := false }]
    run := fun ws j => lift (do return (← argStr j "path", (← argNat? j "offset").getD 1, ← argNat? j "limit"))
      fun (p, o, l) => ws.viewFile p o l },
  { name := "edit_working_file"
    description := "Replace old_string by new_string in the working file, then check it: reports the errors (each with its source line), the messages that start with `fuzz:` (a fuzz test of the invariants that runs at a `vcgen` of a loop that leaves VCs open), and the goal at each `sorry` (a goal that the last report of the file showed and that did not change is one line; lean_goal shows it). An exact match is used if there is one; else whitespace runs match any whitespace. The match must be unique unless replace_all. To fix several independent errors with one check, give `edits` (a list of old_string/new_string pairs, with an optional replace_all) in place of old_string and new_string: the edits apply in order, each to the result of the one before, all or none. An edit that breaks the imports is undone. Helpers must use explicit declaration binders; `variable` commands are refused."
    params := #[file,
      { name := "old_string", type := "string", description := "The text to replace (with new_string, instead of edits).", required := false },
      { name := "new_string", type := "string", description := "The new text.", required := false },
      { name := "replace_all", type := "boolean", description := "Replace every match.", required := false },
      { name := "edits", type := "array", required := false
        description := "Several edits in one call, instead of old_string and new_string: applied in order, all or none, with one check."
        items := some (Json.mkObj [("type", "object"),
          ("properties", Json.mkObj [("old_string", Json.mkObj [("type", "string")]),
            ("new_string", Json.mkObj [("type", "string")]), ("replace_all", Json.mkObj [("type", "boolean")])]),
          ("required", toJson #["old_string", "new_string"])]) }]
    run := fun ws j => withPath ws j fun f => lift (parseEdits j) fun
      | (false, [e]) => ws.edit f e.old e.new e.all
      | (_, es) => ws.editAll f es },
  { name := "undo_edit_working_file"
    description := "Go back `steps` versions of the working file (default 1), then check it (the report of edit_working_file). Restored helpers must use explicit declaration binders; `variable` commands are refused."
    params := #[file, { name := "steps", type := "integer", description := "How many versions back.", required := false }]
    run := fun ws j => withPath ws j fun f => lift (argNat? j "steps") fun s => ws.undo f (s.getD 1) },
  { name := "history_working_file"
    description := "List the kept versions of the working file, the newest first, with their numbers of errors and `sorry`."
    params := #[file]
    run := fun ws j => withPath ws j fun f => ws.history f },
  { name := "submit_working_file"
    description := "Submit the working file. It must have no errors and no `sorry`; then a validator compiles it and checks it against the original: the same statements, no new axioms, only the axioms propext, Classical.choice, Quot.sound and the axioms of bv_decide that the validator checks again, and a kernel replay. A rejected submission is an error, with the reasons. Helpers must use explicit declaration binders; `variable` commands are refused."
    params := #[file, { name := "reasoning", type := "string", description := "Why you submit now." }]
    run := fun ws j => withPath ws j fun f => lift (argStr j "reasoning") fun r => ws.submit f r },
  { name := "lean_loogle"
    description := "Search declarations by name, constant or type pattern (Loogle), for example `Mem.loadInt`, `\"push64\"`, `Mem.loadInt (Mem.storeInt _ _ _ _) _ _`, `_ → label _ ≠ label _`."
    params := #[{ name := "query", type := "string", description := "The Loogle query." },
      { name := "num_results", type := "integer", description := "At most this many results (default 6).", required := false }]
    run := fun ws j => lift (do return (← argStr j "query", (← argNat? j "num_results").getD 6))
      fun (q, n) => ws.loogleQuery q n },
  { name := "grep"
    description := "Search the sources of the project and of Lean with ripgrep, or only one file or directory (path); at most 50 lines. Files on the deny list of the project are left out."
    params := #[{ name := "pattern", type := "string", description := "A regular expression (or a fixed string with fixed)." },
      { name := "path", type := "string", description := "Search only this file or directory, as grep prints it: relative to the project root, or absolute for the Lean sources.", required := false },
      { name := "glob", type := "string", description := "Only files that match this glob, for example `*.lean`.", required := false },
      { name := "context", type := "integer", description := "Lines of context around each match.", required := false },
      { name := "fixed", type := "boolean", description := "Search for the pattern as a fixed string.", required := false }]
    run := fun ws j => lift (do return (← argStr j "pattern", ← argOptStr j "path", ← argOptStr j "glob",
        (← argNat? j "context").getD 0, ← argBool j "fixed" false))
      fun (p, d, g, c, x) => ws.grep p d g c x },
  { name := "lean_run_scratch_code"
    description := "Elaborate a code fragment and report all messages, for example of #check, #print, #eval or example. By default it runs after the imports of the working file only (its own imports are ignored). With after_file true it runs after the whole working file, with its `open` lines, definitions and lemmas (do not send again a declaration that the file has). It does not change the working file."
    params := #[file, { name := "code", type := "string", description := "The Lean code." },
      { name := "after_file", type := "boolean", description := "Run the code after the working file (default false: after its imports).", required := false }]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argStr j "code", ← argBool j "after_file" false)) fun (c, a) => ws.scratch f c a },
  { name := "fuzz"
    description := "Run `#fuzz` commands after the working file's declarations, with the project's fuzz module imported; it does not change the working file. `#fuzz` runs a program on random start states and checks, at each visit of a label, each conjunct of the invariant of a vcgen proof, on each edge between labels the variant, and at the exit a postcondition; a failure shows a wrong invariant, variant or spec (with the label, the conjunct and the state), before you try to prove it. Syntax: `#fuzz prog args (c : MachineData) (ra : Int64) (bs : List UInt8) (h : bs.length = c.regs.rdx.toNat) with (start := c.push64 ra) (invariant := fun {s₀} l s' => …) (variant := fun l s' => …) (post := fun a t => …)`; `post` and `(gen := …)`, `(pre := P)` (before `start`), `(runs := 200)`, `(seed := 0)`, `(fuel := 100000)` are optional. `args` are the theorem's variables and hypotheses; each sample satisfies the hypotheses and `pre`. Without `gen`, the samples come from the binders: a `Mem.Mapped` or `Mem.Contains` block at a register gets a buffer there, `c.regs.r.toNat = n` sets the register. With `gen`, it gives the values of the variables as a tuple (helpers: Fuzz.machine, Fuzz.stack, Fuzz.buffer s .rsi bytes, Fuzz.setReg, Fuzz.bytes n, Fuzz.nat n, Fuzz.range lo hi, Fuzz.ret)."
    params := #[file, { name := "code", type := "string", description := "The #fuzz commands." }]
    run := fun ws j => withPath ws j fun f => lift (argStr j "code") fun c => ws.fuzz f c },
  { name := "lean_goal"
    description := "The proof goals at a position; without column, the goals before and after the line. Shows each complete conclusion first, followed by context with line numbers. Use offset and limit to page the context."
    params := #[file, line, { column with required := false },
      { name := "offset", type := "integer", description := "The first context line, from 1 (default 1).", required := false },
      { name := "limit", type := "integer", description := "The most context lines to show.", required := false }]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argNat j "line", ← argNat? j "column", (← argNat? j "offset").getD 1, ← argNat? j "limit"))
        fun (l, c, o, n) => ws.goal f l c o n },
  { name := "lean_term_goal"
    description := "The expected type of the term at a position."
    params := #[file, line, column]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argNat j "line", ← argNat j "column")) fun (l, c) => ws.termGoal f l c },
  { name := "lean_diagnostic_messages"
    description := "All errors, warnings and messages of the working file, with their positions."
    params := #[file]
    run := fun ws j => withPath ws j fun f => ws.diagnosticsOf f },
  { name := "lean_hover_info"
    description := "The type and documentation of the identifier at a position."
    params := #[file, line, column]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argNat j "line", ← argNat j "column")) fun (l, c) => ws.hover f l c },
  { name := "lean_declaration_file"
    description := "The source of the declaration of the identifier at a position."
    params := #[file, line, column]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argNat j "line", ← argNat j "column")) fun (l, c) => ws.declaration f l c },
  { name := "lean_references"
    description := "The places that use the identifier at a position, its declaration included; at most 40."
    params := #[file, line, column]
    run := fun ws j => withPath ws j fun f =>
      lift (do return (← argNat j "line", ← argNat j "column")) fun (l, c) => ws.references f l c },
  { name := "lean_file_outline"
    description := "The imports and declarations of a file, with their lines."
    params := #[file]
    run := fun ws j => withPath ws j fun f => ws.outline f }
]

/-- Refuses the arguments that are not parameters of `t`, so that the caller learns its interface. -/
def Tool.checkArgs (t : Tool) (j : Json) : Except String Unit :=
  let names := t.params.map (·.name)
  let unknown := match j with
    | .obj kvs => kvs.keysArray.filter (!names.contains ·)
    | _ => #[]
  if unknown.isEmpty then .ok ()
  else .error s!"unknown argument{if unknown.size == 1 then "" else "s"} {", ".intercalate (unknown.toList.map (toJson · |>.compress))} for {t.name}; its parameters are {", ".intercalate names.toList}"

/-- Runs `t` when its arguments pass `checkArgs`. -/
def Tool.call (t : Tool) (ws : Workspace) (j : Json) : IO (Except String String) :=
  lift (t.checkArgs j) fun () => do
    -- All other tools can initialize a working file or send an elaboration request.
    if t.name == "view_file" || t.name == "grep" then return ← t.run ws j
    let permit ← ws.checks.acquire
    let _ ← IO.wait permit.result!
    try t.run ws j finally ws.checks.release

def Tool.usage (t : Tool) : String :=
  let ps := t.params.toList.map fun p =>
    s!"  {p.name} ({p.type}{if p.required then "" else ", optional"}): {p.description}"
  s!"{t.name}: {t.description}\n" ++ "\n".intercalate ps

/-- The tools as JSON schemas, for a harness that gives them to a model. -/
def Tool.schema (t : Tool) : Json :=
  Json.mkObj [("name", toJson t.name), ("description", toJson t.description),
    ("input_schema", Json.mkObj [("type", "object"),
      ("properties", Json.mkObj (t.params.toList.map fun p =>
        (p.name, Json.mkObj ([("type", toJson p.type), ("description", toJson p.description)]
          ++ (p.items.map fun i => [("items", i)]).getD [])))),
      ("required", toJson (t.params.filter (·.required) |>.map (·.name)))])]

end LeanTools
