import Skel.Types
import Skel.Render
import Lean.Data.Json

/-! The prove rung of the skeleton (`docs/research/class-r-coordinator-deepseek-20261118.md`, section 5, R9; decision D18
(2)): the last rung of the proof ladder. For a row that the other rungs leave open, `leantools prove` works on a frozen
file until its validator accepts a proof. The skeleton then checks that proof again with its own check; the row is closed
only by that check.

The parts:

* `Request`: the frozen file of a row, as the text before the theorem, the text of the theorem up to its proof, and the
  text after the proof. The file is the check file of the row (`Skel.checkFile`) with `sorry` as the proof.
  `Request.proofOf` reads the helpers and the proof back from the final file, as one proof text (`Skel.Proof.text`).
* `Reply`: what a run gives back, as the text that the loop keeps in the ledger: the outcome of the run, the model, its
  cost, the directory of its run record, and the proof text (none when the run gave none).
* The loop asks for a run with the ask action: its prompt is `marker`, and the driver replaces it with the text of a
  `Request` (`refreshAsk`). The asker (`asker`) runs the process; its reply is the text of a `Reply`. The rung of the
  ladder (`Skel.proveRung`) reads the reply from the history.
* The asker honours a cap for one run (`--prove-max-usd`) and the budget file. The bound of a run is the `budgetUsd` of
  the config of `leantools prove` (20 when the config has none): a run starts only if the bound is within the cap and
  spent plus the reservations of the runs in flight plus the bound is within the budget. The decision and the
  reservation of the bound are one change of the budget file under its lock, as in `leantools ask`. After a run its
  reservation goes, and the cost goes to the budget file, with one entry.

Helpers may be outside or inside the target's generated namespace. The frozen imports, model and dependency commands
stay exact; helper commands inserted at their boundaries move to the helper slot. The target header is compared by
lexical tokens, so whitespace changes do not change it. Comments do not count as code. Helper namespaces must balance.
Supported linter and bounded resource options are removed before checking.
A changed statement, axiom, helper `sorry`, syntax change, or kernel-control option gives no proof and a reason.
The row checker checks the reconstructed file again, with the original statement fixed before the helpers
(`Skel.theoremText`) and the gate. A checked disproof has a separate result and never closes the forward obligation. -/

namespace Skel.Prove

open Lean (Json JsonNumber)
open System (FilePath)
open Skel.Source

/-- The prompt of the ask action of the rung. A triple prompt is never this text. -/
def marker : String := "skel-prove"

/-- The candidate of the ask action of the rung. -/
def candidate : Candidate := .ask marker

/-! ## The request -/

/-- The frozen file of a row: the name of the row, the text before the theorem (the imports, the model, the answers of
the deps), the text of the theorem up to its proof (`theorem c : S := `, with its namespace line for a dotted name), and
the text after the proof. The helper slot is between `head` and `decl`. -/
structure Request where (row head decl after : String) deriving DecidableEq, Repr

/-- The text before the proof. -/
def Request.before (r : Request) : String := r.head ++ r.decl

/-- The frozen file: `sorry` is the proof. -/
def Request.frozen (r : Request) : String := r.before ++ "sorry" ++ r.after

/-- The text of the request, as the prompt of the ask. -/
def Request.encode (r : Request) : String :=
  Json.compress <| Json.mkObj
    [("kind", Lean.toJson "skel-prove"), ("row", Lean.toJson r.row), ("head", Lean.toJson r.head),
     ("decl", Lean.toJson r.decl), ("after", Lean.toJson r.after)]

/-- The request of a prompt; a prompt that is not the text of a request gives none. -/
def Request.decode? (s : String) : Option Request := do
  let j ← (Json.parse s).toOption
  guard ((j.getObjValAs? String "kind").toOption == some "skel-prove")
  let field (k : String) : Option String := (j.getObjValAs? String k).toOption
  return { row := ← field "row", head := ← field "head", decl := ← field "decl", after := ← field "after" }

/-- Select saved working text only for an exact frozen request. Saved text is proof input;
the normal editor, submission validator and row checker still check it. -/
def proofSeedOf (req : Request) (manifest : Json) : Except String (Option String) := do
  unless (manifest.getObjValAs? Nat "version").toOption == some 1 do
    throw "proofSeeds: expected manifest version 1"
  let items ← (manifest.getObjValAs? (Array Json) "seeds").mapError
    (fun _ => "proofSeeds: expected an array of seeds")
  let mut selected := none
  for item in items do
    let encoded ← (item.getObjValAs? String "request").mapError
      (fun _ => "proofSeeds: seed needs an encoded request")
    let some saved := Request.decode? encoded
      | throw "proofSeeds: invalid saved request"
    let text ← (item.getObjValAs? String "working").mapError
      (fun _ => "proofSeeds: seed needs working text")
    if saved == req then
      if selected.isSome then throw "proofSeeds: duplicate seed for the frozen request"
      selected := some text
  return selected

/-- The words of a text: the runs of letters, digits, `_`, `'`, `#` and `!`. -/
private def words (s : String) : List String :=
  let inWord (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '#' || c == '!'
  let (ws, cur) := s.toList.foldl (fun (ws, cur) c =>
    if inWord c then (ws, c :: cur) else if cur.isEmpty then (ws, cur) else (String.ofList cur.reverse :: ws, [])) ([], [])
  (if cur.isEmpty then ws else String.ofList cur.reverse :: ws).reverse

/-- The words that neither the helpers nor the proof may hold: an axiom, a command that changes the syntax or the
elaboration of the text after it, and code that the kernel does not check. -/
def deniedWords : List String :=
  ["axiom", "macro", "macro_rules", "syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "elab",
   "elab_rules", "declare_syntax_cat", "#exit", "run_cmd", "run_elab", "run_meta", "#eval", "initialize",
   "builtin_initialize", "unsafe", "implemented_by", "extern"]

/-- Added helper commands cannot change imports, introduce variables, or bypass proof and option checks. -/
def deniedHelperWords : List String :=
  ["sorry", "admit", "native_decide", "import", "variable", "section", "set_option"]

/-- Interpolated string bodies can contain terms. Their grammar is outside this lexical importer. -/
private def checkLiterals (text : String) : Except String Unit := do
  for t in sourceTokens 0 text.toList do
    if let some error := t.error then throw error
    if t.text.startsWith "\"" && (t.text.contains '{' || t.text.contains '}') then
      throw "brace-containing string literals are not supported in recovered proofs"

/-- Search code words only. Comment and string contents cannot hide a header or trigger a code rejection. -/
private def denied (deny : List String) (s : String) : Option String :=
  if (s.splitOn helperSep.trimAscii.toString).length > 1 then some helperSep.trimAscii.toString
  else
    let ts := codeTokens s
    let codeWords := ts.flatMap (fun t => words t.text)
    let hashWords := (ts.zip ts.tail).filterMap fun (t, next) =>
      if t.text == "#" && t.stop == next.start then some (t.text ++ next.text) else none
    (codeWords ++ hashWords).find? deny.contains

/-- Namespace commands are copied only as balanced blocks. They cannot close the frozen file's namespace. -/
private def namespaceStackFrom (text : String) (initial : List String) : Except String (List String) := do
  let rec go : List SourceToken → List String → Except String (List String)
    | [], stack => .ok stack
    | t :: ts, stack => do
      if t.text != "namespace" && t.text != "end" then go ts stack
      else
        unless t.column == 0 do throw "a helper namespace command is not at column zero"
        let lineLength := ((text.drop t.stop).toString.splitOn "\n").head!.length
        let name := String.join ((ts.takeWhile (·.start < t.stop + lineLength)).map (·.text))
        if t.text == "namespace" then
          unless !name.isEmpty && (name.splitOn ".").all (fun p => !p.isEmpty && p != "_root_" && p.toList.all wordChar) do
            throw "a helper namespace has an unsupported name"
          go ts (name :: stack)
        else match stack with
          | [] => throw "a helper closes a frozen namespace"
          | current :: rest =>
            unless name.isEmpty || name == current do throw "a helper namespace closing name changed"
            go ts rest
  go (codeTokens text) initial

private def namespaceStack (text : String) : Except String (List String) := namespaceStackFrom text []

/-- Boundaries in the generated frozen prefix. An insertion inside a frozen declaration is refused. -/
private def commandStart (t : SourceToken) : Bool :=
  t.column == 0 && (isComment t ||
    ["import", "namespace", "end", "open", "def", "abbrev", "theorem", "lemma", "private", "protected",
     "noncomputable", "opaque", "instance", "structure", "class", "inductive", "mutual", "attribute",
     "export", "universe", "set_option", "@", "#"].contains t.text)

private def frozenChunks (text : String) : List String :=
  let starts := 0 :: ((sourceTokens 0 text.toList).filter fun t => t.start != 0 && commandStart t).map (·.start)
  (starts.zip (starts.drop 1 ++ [text.length])).map fun (a, b) => ((text.drop a).take (b - a)).toString

/-- Opens in an active helper namespace also scope over the target proof. Closed namespaces
and command-local opens contribute nothing. The helper slot keeps its outer opens. -/
private def activeNamespaceOpens (text : String) : List String :=
  let scopes := (frozenChunks text).foldl (fun scopes chunk =>
    let tokens := codeTokens chunk
    match tokens with
    | [] => scopes
    | first :: _ =>
      if first.text == "namespace" then [] :: scopes
      else if first.text == "end" then scopes.tail
      else if first.text == "open" && !(tokens.any (·.text == "in")) then
        match scopes with
        | current :: rest =>
          let command := (chunk.take tokens.getLast!.stop).toString.trimAscii.toString
          (current ++ [command]) :: rest
        | [] => scopes
      else scopes) [[]]
  scopes.dropLast.reverse.flatten

/-- An appended plain namespace open can move to the helper slot. Original names keep their order. -/
private def appendedOpen (expected rest : String) : Option (String × String) := do
  let line := (rest.splitOn "\n").head!
  let original := (expected.splitOn "\n").head!
  let names (line : String) : Option (List String) := do
    let parts := ((line.splitOn "\t").flatMap (·.splitOn " ")).filter (!·.isEmpty)
    let "open" :: names := parts | none
    guard (!names.isEmpty && names.all fun n => (n.splitOn ".").all fun p =>
      !p.isEmpty && !p.toList.head!.isDigit && p.toList.all wordChar)
    pure names
  let before ← names original
  let after ← names line
  guard (after.length > before.length && after.take before.length == before)
  let suffix := (expected.drop original.length).toString
  let tail := (rest.drop line.length).toString
  guard (suffix.toList.all Char.isWhitespace && tail.startsWith suffix)
  pure ("open " ++ " ".intercalate (after.drop before.length), (tail.drop suffix.length).toString)

private def splitHead (head final : String) : Except String (String × String) := do
  unless head.endsWith "\n" do throw "the frozen prefix does not end at a command boundary"
  let tokens := sourceTokens 0 head.toList
  let lastCode := ((tokens.reverse.find? (!isComment ·)).map (·.stop)).getD 0
  let trailing := tokens.find? fun t => t.start ≥ lastCode && t.column == 0 && isComment t
  let (head, comments) := match trailing with
    | some t => ((head.take t.start).toString, (head.drop t.start).toString.trimAsciiEnd.toString)
    | none => (head, "")
  let base ← namespaceStack head
  let wrapHelper (added : String) (stack : List String) : Except String String := do
    unless (← namespaceStack added).isEmpty do throw "a helper namespace crosses a frozen command"
    let relative := stack.take (stack.length - base.length)
    unless stack.drop relative.length == base do throw "a helper has no scope at the helper slot"
    return "\n".intercalate <|
      relative.reverse.map (s!"namespace {·}") ++ [added] ++ relative.map (s!"end {·}")
  let rec go : List String → String → List String → Bool → List String → Except String (String × String)
    | [], rest, helpers, _, _ => .ok (rest, "\n".intercalate helpers.reverse)
    | expected :: more, rest, helpers, allowAdd, stack => do
      let allowNext := allowAdd || expected.startsWith "namespace "
      let next ← namespaceStackFrom expected stack
      if rest.startsWith expected then go more (rest.drop expected.length).toString helpers allowNext next
      else if let some (added, remaining) := appendedOpen expected rest then
        let added ← wrapHelper added stack
        go more remaining (added :: helpers) allowNext next
      else
        unless allowAdd do throw "the frozen import and namespace prefix changed"
        let some start := (sourceTokens 0 rest.toList).find? fun t =>
            commandStart t && (rest.drop t.start).toString.startsWith expected
          | throw "the text before the theorem changed (an edit of the imports, the model or the answers)"
        let added ← wrapHelper (rest.take start.start).toString.trimAscii.toString stack
        go more (rest.drop (start.start + expected.length)).toString (added :: helpers) allowNext next
  let (remaining, additions) ← go (frozenChunks head) final [] false []
  if comments.isEmpty then return (remaining, additions)
  -- Frozen trailing comments may occur before or after the target. They carry no declarations.
  let some marker := (sourceTokens 0 remaining.toList).find? fun t =>
      isComment t && (remaining.drop t.start).toString.startsWith comments
    | throw "the trailing comments of the frozen prefix changed"
  return ((remaining.take marker.start).toString ++ (remaining.drop (marker.start + comments.length)).toString, additions)

/-- Numeric resource options keep their scope after their bounds are checked. Linter options are removed. -/
private def resourceOptions (text : String) : Except String String := do
  let tokens := codeTokens text
  let rec optionName (name : String) : List SourceToken → String × List SourceToken
    | dot :: part :: rest =>
      if dot.text == "." then optionName (name ++ "." ++ part.text) rest else (name, dot :: part :: rest)
    | rest => (name, rest)
  let rec go : List SourceToken → Nat → String → Except String String
    | [], offset, out => .ok (out ++ (text.drop offset).toString)
    | t :: ts, offset, out =>
      if t.text != "set_option" then go ts offset out
      else match ts with
        | first :: rest => do
          let (name, rest) := optionName first.text rest
          let value :: rest := rest | throw "an option is incomplete"
          if name == "maxHeartbeats" then
            let some n := value.text.toNat? | throw "a resource option is not a natural number"
            unless n > 0 && n ≤ 400000 do throw "maxHeartbeats must be between 1 and 400000"
          else if name == "maxRecDepth" then
            let some n := value.text.toNat? | throw "a resource option is not a natural number"
            unless n > 0 do throw "maxRecDepth must be positive"
          else if ["linter.deprecated", "linter.unusedVariables"].contains name then
            unless value.text == "true" || value.text == "false" do throw "a linter option is not a Boolean"
          else throw s!"the option '{name}' is not allowed"
          let out := out ++ ((text.drop offset).take (t.start - offset)).toString
          let stop := match rest with
            | scope :: _ => if scope.text == "in" then scope.stop else value.stop
            | [] => value.stop
          let kept := if name == "maxHeartbeats" || name == "maxRecDepth" then
              ((text.drop t.start).take (stop - t.start)).toString
            else ""
          go ts stop (out ++ kept)
        | _ => .error "an option is incomplete"
  go tokens 0 ""

private def checkExtracted (helpers proof : String) : Except String String := do
  checkLiterals helpers
  checkLiterals proof
  let helpers ← resourceOptions helpers
  let proof ← resourceOptions proof
  if proof.trimAscii.isEmpty then throw "the proof is empty"
  if let some w := denied (deniedWords ++ deniedHelperWords.filter (· != "set_option")) helpers then
    throw s!"a helper has the word '{w}'"
  unless (← namespaceStack helpers).isEmpty do throw "a helper namespace is not closed"
  if let some w := denied deniedWords proof then throw s!"the proof has the word '{w}'"
  return Proof.text { helpers := helpers.trimAscii.toString, proof := proof.trimAscii.toString }

/-- Extracts a checked final file without requiring a byte-identical theorem header. Frozen commands remain exact;
additional helper commands at their boundaries and target whitespace can move. The row check
then checks the reconstructed file with the original statement pinned before all helpers. -/
private def Request.structuredProofOf (r : Request) (final : String) : Except String String := do
  let (after, checkCommands) ← if final.endsWith r.after then pure (r.after, false) else do
    let [before, after] := r.after.splitOn s!"\n#print axioms {r.row}\n"
      | throw "the text after the proof changed"
    -- Lean accepts the generated diagnostic without a line break before `#print`.
    let compact := before ++ s!"#print axioms {r.row}\n" ++ after
    if final.endsWith compact then pure (compact, true) else do
      let reduced := before ++ "\n" ++ after
      unless !reduced.isEmpty && final.endsWith reduced do throw "the text after the proof changed"
      pure (reduced, true)
  let (remaining, additions) ← splitHead r.head final
  let mid := (remaining.dropEnd after.length).toString
  let ns := ".".intercalate (r.row.splitOn ".").dropLast
  let nsPrefix := if ns.isEmpty then "" else s!"namespace {ns}\n"
  let declaration := (r.decl.drop nsPrefix.length).toString
  let target := (sourceTokens 0 declaration.toList).map (·.text)
  let tokens := sourceTokens 0 mid.toList
  let rec find : List SourceToken → Option (Nat × Nat)
    | [] => none
    | ts@(t :: rest) =>
      if (ts.take target.length).map (·.text) == target then
        some (t.start, (ts.take target.length).getLast!.stop)
      else find rest
  let some (start, stop) := find tokens
    | throw "the text of the theorem up to its proof changed (an edit of the statement)"
  let helpers := (mid.take start).toString.trimAscii.toString
  let proof := (mid.drop stop).toString.trimAscii.toString
  let proofTokens := codeTokens proof
  for t in proofTokens do
    let line := ((proof.take t.start).toString.splitOn "\n").getLast!
    let lineStart := line.toList.all Char.isWhitespace
    let fromToken := (proof.drop t.start).toString
    let directive := t.text == "#" && !fromToken.startsWith "#[" && !fromToken.startsWith "#v["
    if directive || (checkCommands && lineStart && commandStart { t with column := 0 } && t.text != "@" && t.text != "#") then
      throw "a command was added after the target proof"
  unless (← namespaceStack helpers) == (if ns.isEmpty then [] else [ns]) do
    throw "the generated theorem namespace changed"
  -- Options before the theorem scope over its proof. Move them into the proof term.
  let helperTokens := codeTokens helpers
  let trailingOption := helperTokens.reverse.takeWhile (fun t => t.text != "set_option")
  let optionStart := if trailingOption.length < helperTokens.length then
      let t := helperTokens[helperTokens.length - trailingOption.length - 1]!
      if (helperTokens.drop (helperTokens.length - trailingOption.length - 1)).length == 4 then some t.start else none
    else none
  let (helpers, proof) := match optionStart with
    | some i => ((helpers.take i).toString.trimAscii.toString, (helpers.drop i).toString ++ "\n" ++ proof)
    | none => (helpers, proof)
  -- Keep the implementation in its active command scope. A term-local `open scoped`
  -- does not preserve scoped notation expansion in this Lean version.
  let (helpers, proof) ← if (activeNamespaceOpens helpers).isEmpty then pure (helpers, proof) else do
    let names := words final
    let some index := (List.range (names.length + 1)).find? fun i => !names.contains s!"skel_target_{i}"
      | throw "no fresh scoped proof name"
    let name := s!"skel_target_{index}"
    let short := (r.row.splitOn ".").getLast!
    let header := (declaration.drop s!"theorem {short}".length).toString
    let some (binders, _) := splitAtTop ':' [] 0 header.toList
      | throw "the scoped theorem has no result type"
    let args := binderNames binders.trimAscii.toString
    let reference := "@" ++ ns ++ "." ++ name ++
      (if args.isEmpty then "" else " " ++ " ".intercalate args)
    pure (helpers ++ s!"\ntheorem {name}{header}{proof}", reference)
  let helpers := if helpers == nsPrefix.trimAscii.toString then ""
    else if ns.isEmpty then helpers else s!"{helpers}\nend {ns}"
  let extracted ← checkExtracted ("\n".intercalate ([additions, helpers].filter (!·.isEmpty))) proof
  let p := Proof.ofText extracted
  let original := ".".intercalate (← namespaceStack r.head).reverse
  let names := Source.declarationNames p.helpers
  let relocate (text : String) := Source.relocateQualifiedHelpers text original (r.row ++ ".skel_proof") names
  return Proof.text { helpers := relocate p.helpers, proof := relocate p.proof }

/-- Read the helpers and proof from the checked final source. Every imported proof is checked again against the frozen
statement; this function never accepts a changed model or an unbounded/kernel-control option. -/
def Request.proofOf (r : Request) (final : String) : Except String String := do
  r.structuredProofOf final

/-- Render a recovered proof with the exact frozen statement pinned before its helpers. The returned name is the
fully qualified target for the ordinary row checker. Open dependency binders become a quantified statement. -/
def Request.recoveredFile (r : Request) (proof : String) : Except String (String × String) := do
  let parts := r.row.splitOn "."
  let short := parts.getLast?.getD r.row
  let ns := ".".intercalate parts.dropLast
  let nsPrefix := if ns.isEmpty then "" else s!"namespace {ns}\n"
  let start := nsPrefix ++ s!"theorem {short}"
  unless r.decl.startsWith start && r.decl.endsWith " := " do throw "the frozen declaration is not a theorem header"
  let body := ((r.decl.drop start.length).dropEnd 4).toString
  let some (binders, statement) := splitAtTop ':' [] 0 body.toList
    | throw "the frozen declaration has no result type"
  let binders := binders.trimAscii.toString
  let statement := statement.trimAscii.toString
  let p := Proof.ofText proof
  let statement := if binders.isEmpty then statement else s!"∀ {binders}, {statement}"
  let proof := if binders.isEmpty then proof else
    Proof.text { p with proof := s!"by\n  intro {" ".intercalate (binderNames binders)}\n  exact ({p.proof})" }
  let after ← if ns.isEmpty then pure r.after else do
    let closing := s!"\nend {ns}"
    unless r.after.startsWith closing do throw "the frozen declaration has no namespace closing command"
    pure (r.after.drop closing.length).toString
  let outer := ((r.head.splitOn "\n").find? (·.startsWith "namespace ")).map (fun line => (line.drop 10).toString)
  let target := match outer with | some n => s!"{n}.{r.row}" | none => r.row
  return (target, withProofScopeImport (r.head ++ theoremText r.row statement proof ++ after))

/-- An accepted validator report can identify a disproof only for this exact frozen target. This is diagnostic evidence;
it never produces a forward proof or closes a row. -/
def Request.checkedDisproof (r : Request) (report : String) : Bool :=
  match r.recoveredFile "sorry" with
  | .error _ => false
  | .ok (target, _) =>
    let suffix := s!"{target} disproved, with the statements of the original and the standard axioms only."
    let report := report.trimAscii.toString
    report.startsWith "Accepted: " && (report.endsWith ("; " ++ suffix) || report == "Accepted: " ++ suffix)

/-- A text that is in no check file: the place of the proof. -/
private def placeholder : String := "⟪skel-proof⟫"

/-- The request of the obligation `ob`: its check file (the model, the closed answers of its deps) with the proof left out.
The text of the theorem up to the proof is `theoremText` of the obligation up to the proof. -/
def request (h : Header) (model : String) (answers : List String) (ob : Obligation) : Except String Request :=
  match (checkFile h model answers ob placeholder).splitOn placeholder,
      (theoremText ob.id.name ob.statement placeholder).splitOn placeholder with
  | [a, b], [d, _] =>
    if a.endsWith d then .ok { row := ob.id.name, head := (a.dropEnd d.length).toString, decl := d, after := b }
    else .error s!"the check file of {ob.id.name} does not end with its theorem before the proof"
  | _, _ => .error s!"the check file of {ob.id.name} does not have the place of the proof once"

/-- The action with the request in the prompt: an ask with the prompt `marker` gets the text of the request that `mk` makes
for its row; any other action is not changed. -/
def refreshAsk (mk : Ledger → Obligation → Option Request) (l : Ledger) : Action → Action
  | .ask p prompt =>
    if prompt == marker then
      match (l.records.find? (·.ob.id == p.ob)).bind (mk l ·.ob) with
      | some q => .ask p q.encode
      | none => .ask p prompt
    else .ask p prompt
  | a => a

/-! ## The money

An amount is a natural number of pico-USD (10⁻¹² USD), as in `leantools ask`. -/

/-- The amount of a JSON number of USD: `n * 10^12`, rounded up when `up`, else down. A negative number is an error. -/
private def scaled (n : JsonNumber) (up : Bool) : Except String Nat := do
  if n.mantissa < 0 then throw "the number is negative"
  if n.exponent > 100 then throw "the number has more than 100 decimals"
  let m := n.mantissa.toNat
  if n.exponent ≤ 12 then return m * 10 ^ (12 - n.exponent)
  let d := 10 ^ (n.exponent - 12)
  return if up then (m + d - 1) / d else m / d

/-- The amount of a number in a file, rounded up. -/
def picoOfJson : Json → Except String Nat
  | .num n => scaled n true
  | _ => .error "a number is expected"

/-- The amount of a decimal text (the cap of a run), rounded down. -/
def usdOfText (s : String) : Except String Nat :=
  match Json.parse s with
  | .ok (.num n) => scaled n false
  | _ => .error s!"{s.quote} is not a number"

/-- The exact decimal text of an amount. -/
def usdText (pico : Nat) : String := (Json.num ⟨pico, 12⟩).compress

/-- Whether a run starts: its bound within the cap, and spent plus the reservations of the runs in flight plus the bound
within the budget. -/
def decide (total spent reserved bound cap : Nat) : Except String Unit :=
  if cap < bound then
    .error s!"refused: --prove-max-usd {usdText cap} is below the cost bound {usdText bound}"
  else if total < spent + reserved + bound then
    .error (s!"refused: spentUsd {usdText spent} + reserved {usdText reserved} (runs in flight) + cost bound " ++
      s!"{usdText bound} is above budgetUsd {usdText total}")
  else .ok ()

/-! ## The reply -/

/-- The accepted result and its extraction state are separate from the worker's process outcome. -/
inductive ResultKind where
  | proof | disproof | extractionFailure | unfinished
  deriving DecidableEq, Repr

def ResultKind.text : ResultKind → String
  | .proof => "proof"
  | .disproof => "disproof"
  | .extractionFailure => "extraction-failure"
  | .unfinished => "unfinished"

def ResultKind.ofText? : String → Option ResultKind
  | "proof" => some .proof
  | "disproof" => some .disproof
  | "extraction-failure" => some .extractionFailure
  | "unfinished" => some .unfinished
  | _ => none

/-- What a run gives back: the outcome of `leantools prove` (`accepted` or another outcome of its summary), the model, the
cost, the directory of the run record, the proof text (`Proof.text`: the helpers and the proof; none when the run gave none
or the final file has no proof of the theorem), and why there is no proof. -/
structure Reply where
  (outcome : String) (model : String := "") (costPico : Nat) (runDir : String) (proof : Option String) (why : String)
  (budget : String := "") (link : Nat := 0) (earlier : List Failed := []) (result : Option ResultKind := none)
  deriving DecidableEq, Repr

/-- Old records derive their result from their existing outcome and proof fields. -/
def Reply.resultKind (r : Reply) : ResultKind :=
  r.result.getD (if r.proof.isSome then .proof else if r.outcome == "accepted" then .extractionFailure else .unfinished)

/-- What the run spent, with its link in the chain and the earlier attempts of the chain. -/
def Reply.spend (r : Reply) : Spend :=
  { model := r.model, costPico := r.costPico, runDir := r.runDir, budget := r.budget, link := r.link, earlier := r.earlier }

def Failed.toJson (f : Failed) : Json :=
  Json.mkObj [("model", Lean.toJson f.model), ("costUsd", .num ⟨f.costPico, 12⟩), ("budget", Lean.toJson f.budget),
    ("why", Lean.toJson f.why), ("reason", Lean.toJson f.reason)]

def Failed.decode? (j : Json) : Option Failed := do
  return { model := ← (j.getObjValAs? String "model").toOption, costPico := ← (picoOfJson (j.getObjValD "costUsd")).toOption,
           budget := ← (j.getObjValAs? String "budget").toOption, why := ← (j.getObjValAs? String "why").toOption,
           reason := (j.getObjValAs? String "reason").toOption.getD "" }

/-- The JSON value of the reply. -/
def Reply.toJson (r : Reply) : Json :=
  Json.mkObj
    [("outcome", Lean.toJson r.outcome), ("result", match r.result with | some k => Lean.toJson k.text | none => .null), ("model", Lean.toJson r.model), ("costUsd", .num ⟨r.costPico, 12⟩),
     ("runDir", Lean.toJson r.runDir), ("proof", match r.proof with | some t => Lean.toJson t | none => Json.null),
     ("why", Lean.toJson r.why), ("budget", Lean.toJson r.budget), ("link", Lean.toJson r.link),
     ("earlier", .arr (r.earlier.map Failed.toJson).toArray)]

/-- The text of the reply, which the ledger keeps. -/
def Reply.encode (r : Reply) : String := r.toJson.compress

/-- The reply of a text; a text that is not the text of a reply gives none. A text with no model has the model `""`, and a
text with no budget file, link or earlier attempts has `""`, 0 and none. Missing result kinds remain compatible with old
records. Unknown kinds and kinds inconsistent with the proof field are refused. -/
def Reply.decode? (s : String) : Option Reply := do
  let j ← (Json.parse s).toOption
  let proof ← match j.getObjVal? "proof" with
    | .ok .null => some none
    | .ok (.str t) => some (some t)
    | _ => none
  let result ← match j.getObjValD "result" with
    | .null => some none
    | .str t => some <$> ResultKind.ofText? t
    | _ => none
  guard (match result with
    | some .proof => proof.isSome
    | some .disproof | some .extractionFailure | some .unfinished => proof.isNone
    | none => true : Bool)
  let earlier ← match j.getObjValD "earlier" with
    | .null => some []
    | .arr a => a.toList.mapM Failed.decode?
    | _ => none
  return { outcome := ← (j.getObjValAs? String "outcome").toOption,
           model := (j.getObjValAs? String "model").toOption.getD "",
           costPico := ← (picoOfJson (j.getObjValD "costUsd")).toOption,
           runDir := ← (j.getObjValAs? String "runDir").toOption, proof := proof,
           why := ← (j.getObjValAs? String "why").toOption,
           budget := (j.getObjValAs? String "budget").toOption.getD "", link := (j.getObjValAs? Nat "link").toOption.getD 0,
           earlier, result }

/-! ## The settings and the flags -/

/-- One model of the chain: `cmd` is the command (`leantools` on the path, or a path); `config` is the config of
`leantools prove`; `budget` is the budget file of the model; `maxUsd` is the cap of one run, as decimal text. -/
structure Link where
  cmd : String := "leantools"
  config : String
  budget : String := "docs/deepseek-budget.json"
  maxUsd : String
  dryRun : Bool := false
  deriving DecidableEq, Repr

/-- The run-wide cap: the spent amounts and the reservations of all the `files` (the budget files of the chains of both rungs),
and the bound of a call, stay within `totalUsd` (decimal text). -/
structure Wide where (totalUsd : String) (files : List String) deriving DecidableEq, Repr

/-- The settings of the prover: the first model, and the final models after it (`later`), tried in order for a row that the
earlier models leave open and that the allow file `allow` names (none: no final model runs). `wide` is the run-wide cap; none:
only the budget file of each link limits it. -/
structure Cfg extends Link where
  later : List Link := []
  wide : Option Wide := none
  allow : Option String := none
  deriving DecidableEq, Repr

/-- The models of the chain, in order. -/
def Cfg.links (c : Cfg) : List Link := c.toLink :: c.later

private def isDecimal (s : String) : Bool :=
  (s.splitOn ".").length ≤ 2 && s.any Char.isDigit && s.all fun c => c.isDigit || c == '.'

/-- The prove flags of one model that the command line has given so far. -/
private structure Flags where
  config : Option String := none
  budget : Option String := none
  maxUsd : Option String := none
  cmd : Option String := none
  dryRun : Bool := false

private def once (flag : String) (cur : Option String) (v : String) : Except String (Option String) :=
  match cur with
  | none => .ok (some v)
  | some _ => .error s!"{flag} is given more than once"

/-- The flags of the models, oldest model last (`done` is newest first), and the other arguments of `args`, in order. A flag
with a value takes the next argument, which is not a flag. `--prove-config` starts a model; the other flags belong to the
model that was started last. -/
private def scan (done : List Flags) (cur : Option Flags) (rest : List String) : List String →
    Except String (List Flags × List String)
  | [] => .ok ((cur.toList ++ done).reverse, rest.reverse)
  | "--prove-dry-run" :: tl =>
    match cur with
    | none => .error "the prove flags need --prove-config"
    | some f =>
      if f.dryRun then .error "--prove-dry-run is given more than once" else scan done (some { f with dryRun := true }) rest tl
  | flag :: tl =>
    if !["--prove-config", "--prove-budget", "--prove-max-usd", "--prove-cmd"].contains flag then scan done cur (flag :: rest) tl
    else match tl with
      | v :: tl' =>
        if v.startsWith "--" then .error s!"{flag} has no value"
        else if flag == "--prove-config" then scan (cur.toList ++ done) (some { config := some v }) rest tl'
        else match cur with
          | none => .error "the prove flags need --prove-config"
          | some f => do
            match flag with
            | "--prove-budget" => scan done (some { f with budget := ← once flag f.budget v }) rest tl'
            | "--prove-max-usd" => scan done (some { f with maxUsd := ← once flag f.maxUsd v }) rest tl'
            | _ => scan done (some { f with cmd := ← once flag f.cmd v }) rest tl'
      | [] => .error s!"{flag} has no value"

/-- The model of the flags of one `--prove-config`: it needs `--prove-max-usd` (a decimal number). -/
private def Flags.link (f : Flags) : Except String Link := do
  let some config := f.config | .error "the prove flags need --prove-config"
  let some usd := f.maxUsd | .error s!"--prove-config {config} needs --prove-max-usd"
  unless isDecimal usd do .error s!"--prove-max-usd needs a decimal number, got '{usd}'"
  let d : Link := { config := config, maxUsd := usd }
  return { d with cmd := f.cmd.getD d.cmd, budget := f.budget.getD d.budget, dryRun := f.dryRun }

/-- The prove settings and the other arguments of the command line. No prove flag: no settings. `--prove-config` may be given
more than once: the models are tried in the order of the flags, and each takes the `--prove-max-usd`, `--prove-budget`,
`--prove-cmd` and `--prove-dry-run` that follow it. A model needs `--prove-max-usd` (a decimal number), and a flag before the
first `--prove-config` is an error. -/
def takeFlags (args : List String) : Except String (Option Cfg × List String) := do
  let (fs, rest) ← scan [] none [] args
  match ← fs.mapM Flags.link with
  | [] => .ok (none, rest)
  | l :: later => .ok (some { toLink := l, later }, rest)

/-! ## The prover -/

/-- The text of a file as JSON; an error has the path. -/
private def readJson (path : String) : IO (Except String Json) := do
  try
    pure ((Json.parse (← IO.FS.readFile path)).mapError fun e => s!"{path}: {e}")
  catch e => pure (.error s!"{path}: {e}")

/-- The bound of a run: the `budgetUsd` of the config of `leantools prove`, 20 when it has none. -/
private def boundOf (cfg : Json) : Except String Nat :=
  match cfg.getObjVal? "budgetUsd" with
  | .ok v => (picoOfJson v).mapError ("budgetUsd of the config: " ++ ·)
  | .error _ => .ok (20 * 10 ^ 12)

/-- The reservations of the budget file: the runs in flight, each `{run, boundUsd}`. A file with none has none. -/
private def reservationsOf (b : Json) : Except String (Array Json) :=
  match b.getObjValD "reservations" with
  | .null => .ok #[]
  | .arr a => .ok a
  | _ => .error "reservations: a list is expected"

/-- The total, the spent amount and the sum of the reservations of the budget file. -/
private def budgetOf (b : Json) : Except String (Nat × Nat × Nat) := do
  let total ← (picoOfJson (b.getObjValD "budgetUsd")).mapError ("budgetUsd: " ++ ·)
  let spent ← (picoOfJson (b.getObjValD "spentUsd")).mapError ("spentUsd: " ++ ·)
  let bounds ← (← reservationsOf b).mapM fun r =>
    (picoOfJson (r.getObjValD "boundUsd")).mapError ("reservations: boundUsd: " ++ ·)
  return (total, spent, bounds.foldl (· + ·) 0)

/-- The object without the field `k`. -/
private def withoutField (j : Json) (k : String) : Json :=
  match j with
  | .obj kvs => .obj (kvs.erase k)
  | j => j

/-- The budget file with the bound of the run `run` reserved, when the decision (`decide`, with the reservations of the
file) lets the run start. -/
def reserveIn (b : Json) (run : String) (bound cap : Nat) : Except String Json := do
  let (total, spent, reserved) ← budgetOf b
  decide total spent reserved bound cap
  let r := Json.mkObj [("run", Lean.toJson run), ("boundUsd", .num ⟨bound, 12⟩)]
  return b.setObjVal! "reservations" (.arr ((← reservationsOf b).push r))

/-- The budget file after the run `run`: its reservation is removed, and with a charge the cost goes to `spentUsd` and the
entry to `runs`. The other reservations stay as they are; the field `reservations` is removed when none is left. -/
def settleIn (b : Json) (run : String) (charge : Option (Nat × Json)) : Except String Json := do
  let (_, spent, _) ← budgetOf b
  let left := (← reservationsOf b).filter fun r => (r.getObjValAs? String "run").toOption != some run
  let b := if left.isEmpty then withoutField b "reservations" else b.setObjVal! "reservations" (.arr left)
  match charge with
  | none => return b
  | some (cost, entry) =>
    let runs := match b.getObjValD "runs" with
      | .arr a => a
      | _ => #[]
    return (b.setObjVal! "spentUsd" (.num ⟨spent + cost, 12⟩)).setObjVal! "runs" (.arr (runs.push entry))

/-- Changes the budget file with `f`, under the lock file `PATH.lock`, and writes it by a rename, as `leantools ask`
does. An error of `f` leaves the file as it is. -/
private def changeBudget (path : String) (f : Json → Except String Json) : IO (Except String Unit) := do
  try
    let lock ← IO.FS.Handle.mk s!"{path}.lock" .append
    lock.lock
    try
      match (← readJson path).bind f with
      | .error e => pure (.error e)
      | .ok b' =>
        let tmp := s!"{path}.tmp{← IO.Process.getPID}"
        IO.FS.writeFile tmp (b'.pretty ++ "\n")
        IO.FS.rename tmp path
        pure (.ok ())
    finally lock.unlock
  catch e => pure (.error s!"{path}: {e}")

/-- A reservation is settled in the same canonical book in which it was made. -/
structure Reservation where
  path : String
  run : String

/-- Locks each distinct canonical book in path order. No request runs in this action. -/
private def withBudgetLocks {α : Type} (paths : List String) (act : IO α) : IO α :=
  match paths with
  | [] => act
  | path :: rest => do
    let lock ← IO.FS.Handle.mk s!"{path}.lock" .append
    lock.lock
    try withBudgetLocks rest act finally lock.unlock

/-- Resolves aliases before sorting, so two callers use the same lock order and count each book once. -/
private def budgetPaths (paths : List String) : IO (List String) := do
  let paths ← paths.mapM fun p => return (← IO.FS.realPath (FilePath.mk p)).toString
  return (paths.toArray.qsort (· < ·)).toList.eraseDups

private def checkWide (w : Wide) (books : List Json) (bound : Nat) : Except String Unit := do
  let total ← usdOfText w.totalUsd
  let committed ← books.mapM fun b => do
    let (_, spent, reserved) ← budgetOf b
    return spent + reserved
  let sum := committed.foldl (· + ·) 0
  if total < sum + bound then
    throw (s!"refused: run-wide: spent + reserved of the budget files {usdText sum} + cost bound {usdText bound} " ++
      s!"is above --total-max-usd {usdText total}")

/-- A read-only view of the shared cap. A live call must use `reserveBudget` to check and reserve together. -/
def Wide.check (w : Wide) (bound : Nat) : IO (Except String Unit) := do
  try
    let paths ← budgetPaths w.files
    withBudgetLocks paths do
      return ((← paths.mapM readJson).mapM id).bind (checkWide w · bound)
  catch e => return .error s!"run-wide budget: {e}"

/-- Checks all books and reserves the target book in one locked action. A dry call only checks.
The target is always included, even when the caller omitted it from `wide.files`. -/
def reserveBudget (wide : Option Wide) (path run : String) (bound cap : Nat) (dryRun : Bool := false) :
    IO (Except String Reservation) := do
  try
    let target := (← IO.FS.realPath path).toString
    let paths ← budgetPaths (target :: (wide.map (·.files)).getD [])
    withBudgetLocks paths do
      let books := ((← paths.mapM readJson).mapM id)
      match books.bind (fun bs => do
        if let some w := wide then checkWide w bs bound
        let some b := (paths.zip bs).lookup target | throw s!"missing target book {target}"
        reserveIn b run bound cap) with
      | .error e => return .error e
      | .ok b =>
        unless dryRun do
          let tmp := s!"{target}.tmp{← IO.Process.getPID}"
          IO.FS.writeFile tmp (b.pretty ++ "\n")
          IO.FS.rename tmp target
        return .ok { path := target, run }
  catch e => return .error s!"{path}: {e}"

/-- Replaces a reservation by its charge, or releases it when the process did not start. -/
def Reservation.settle (r : Reservation) (charge : Option (Nat × Json)) : IO (Except String Unit) :=
  changeBudget r.path (settleIn · r.run charge)

/-- The directory of the run record, from the stdout of `leantools prove`. -/
def runDirOf (stdout : String) : Option String :=
  (stdout.splitOn "\n").reverse.findSome? fun line =>
    match line.splitOn "run record " with
    | _ :: rest@(_ :: _) => some (rest.getLast!.trimAscii.toString)
    | _ => none

/-- The model of a run: the `model` of its summary, else the first of its `models`, else the `model` of the config, else
`""`. -/
def modelOf (summary cfg : Json) : String :=
  let first : Option String := match summary.getObjValD "models" with
    | .arr a => a[0]?.bind (·.getStr?.toOption)
    | _ => none
  ((summary.getObjValAs? String "model").toOption <|> first <|> (cfg.getObjValAs? String "model").toOption).getD ""

/-- The name of a file for a row: the characters that a path and a Lean module name accept. -/
private def fileStem (row : String) : String := row.map fun c => if c.isAlphanum || c == '_' || c == '.' || c == '-' then c else '_'

/-- The result of one prover invocation. A reply is not a row closure: the row checker decides that. -/
private inductive InvocationResult where
  | replied (reply : Reply)
  | noReply (why : String)
  | dryRun

private def InvocationResult.reply? : InvocationResult → Option Reply
  | .replied reply => some reply
  | .noReply _ | .dryRun => none

private def InvocationResult.toJson : InvocationResult → Json
  | .replied reply => Json.mkObj [("kind", "reply"), ("reply", reply.toJson)]
  | .noReply why => Json.mkObj [("kind", "no reply"), ("why", why)]
  | .dryRun => Json.mkObj [("kind", "dry run")]

/-- Claim a directory with an atomic create. Each invocation owns its result file, including repeated rows. -/
private partial def invocationDir (parent : FilePath) (name : String) (k : Nat := 0) : IO FilePath := do
  IO.FS.createDirAll parent
  let path := parent / s!"{name}-{k}"
  match ← (IO.FS.createDir path).toBaseIO with
  | .ok () => pure path
  | .error (.alreadyExists ..) => invocationDir parent name (k + 1)
  | .error e => throw e

/-- Write one result and its exact request without a shared append file. The frozen path can be absent after a refusal.
The request retains the source in that case. The completed JSON appears after the rename. -/
private def recordInvocation (dir : FilePath) (req : Request) (cfg : Option Link)
    (result : InvocationResult) (ms : Nat) : IO Unit := do
  let name := s!"{← IO.Process.getPID}-{← IO.monoNanosNow}"
  let target ← invocationDir (dir / "invocations") name
  let record := Json.mkObj
    [("id", s!"{dir}/{req.row}"), ("row", req.row), ("dir", dir.toString),
     ("request", req.encode), ("frozen", (dir / s!"{fileStem req.row}.lean").toString),
     ("config", (cfg.map (·.config)).getD ""), ("budget", (cfg.map (·.budget)).getD ""),
     ("dryRun", Lean.toJson ((cfg.map (·.dryRun)).getD false)), ("wallMs", Lean.toJson ms),
     ("result", result.toJson)]
  IO.FS.writeFile (target / "result.json.tmp") (record.compress ++ "\n")
  IO.FS.rename (target / "result.json.tmp") (target / "result.json")

/-- Lean reports an exec failure through the child output rather than an IO exception. An arbitrary exit 255
is not a launch failure: only the runtime's exact exec error permits release. A failed child can
flush output that the parent buffered before the fork, so stdout need not be empty. -/
def didNotStart (cmd : String) (out : IO.Process.Output) : Bool :=
  out.exitCode == 255 &&
    out.stderr.trimAscii.toString == s!"could not execute external process '{cmd}'"

private def readProofSeed (req : Request) (cfg : Json) : IO (Except String (Option String)) := do
  match cfg.getObjValD "proofSeeds" with
  | .null => return .ok none
  | .str path =>
    match ← readJson path with
    | .ok manifest => return proofSeedOf req manifest
    | .error why => return .error s!"proofSeeds: {why}"
  | _ => return .error "proofSeeds: expected a manifest path"

/-- Freeze the generated statement through the normal tool before editing in saved work.
No original is written directly, and no model call runs when either tool refuses. -/
private def applyProofSeed (c : Link) (dir file : FilePath) (req : Request) (saved : String) :
    IO (Except String Unit) := do
  try
    let root ← IO.FS.realPath (← IO.currentDir)
    let absolute ← IO.FS.realPath file
    let rootParts := root.components
    if rootParts.isPrefixOf absolute.components then
      let relative := FilePath.mk ("/".intercalate (absolute.components.drop rootParts.length))
      let original := root / ".leantools" / "orig" / relative
      if ← original.pathExists then
        unless (← IO.FS.readFile original) == req.frozen do
          return .error "proofSeeds: cached original differs from the frozen request; use a new output directory"
    IO.FS.writeFile (dir / s!"{fileStem req.row}.seed.json") <| (Json.mkObj
      [("request", Lean.toJson req.encode), ("working", Lean.toJson saved)]).compress ++ "\n"
    for (tool, args) in [
        ("view_original_file", Json.mkObj [("file", Lean.toJson file.toString)]),
        ("edit_working_file", Json.mkObj [("file", Lean.toJson file.toString),
          ("old_string", Lean.toJson req.frozen), ("new_string", Lean.toJson saved)])] do
      let out ← IO.Process.output { cmd := c.cmd, args := #[tool, "-"] } (some args.compress)
      unless out.exitCode == 0 do
        return .error s!"proofSeeds: {tool} refused saved work: {out.stderr}{out.stdout}"
    return .ok ()
  catch e => return .error s!"proofSeeds: cannot apply saved work: {e}"

/-- The run of `leantools prove` for the request, after its bound is reserved. Its result and the charge for the budget
file: the cost and the entry of a run that ran. A run without a reply keeps its reason. -/
private def runOne (c : Link) (cfgJson : Json) (dir : FilePath) (log : String → IO Unit) (req : Request) (bound : Nat) :
    IO (InvocationResult × Option (Nat × Json)) := do
  let seed ← match ← readProofSeed req cfgJson with
    | .ok seed => pure seed
    | .error why => log why; return (.noReply why, none)
  IO.FS.createDirAll dir
  let file := dir / s!"{fileStem req.row}.lean"
  IO.FS.writeFile file req.frozen
  if let some saved := seed then
    if saved != req.frozen then
      match ← applyProofSeed c dir file req saved with
      | .ok () => log "proofSeeds: apply saved work for the exact frozen request"
      | .error why => log why; return (.noReply why, none)
  else if cfgJson.getObjValD "proofSeeds" != .null then
    log "proofSeeds: no saved work matches the frozen request"
  let out ← try
      pure (Except.ok (← IO.Process.output { cmd := c.cmd, args := #["prove", file.toString, "--config", c.config] }))
    catch e => pure (Except.error s!"cannot run {c.cmd}: {e}")
  match out with
  | .error e => log e; return (.noReply e, none)
  | .ok out =>
    let unknown := some (bound, Json.mkObj [("tool", Lean.toJson "skel prove"),
      ("row", Lean.toJson req.row), ("model", Lean.toJson (modelOf Json.null cfgJson)),
      ("outcome", Lean.toJson "unknown"), ("costUsd", .num ⟨bound, 12⟩)])
    if out.exitCode != 0 && out.exitCode != 1 then
      let why := s!"no reply: exit {out.exitCode}: {out.stderr.trimAscii.toString}"
      log why
      return (.noReply why, if out.exitCode == 2 || didNotStart c.cmd out then none else unknown)
    let some runDir := runDirOf out.stdout
      | let why := s!"no reply: no run record in the output of {c.cmd}: {out.stdout.trimAscii.toString}; charge the bound"
        log why
        return (.noReply why, unknown)
    let summary ← readJson s!"{runDir}/summary.json"
    -- a run whose summary is lost is charged with its bound
    let (outcome, cost, report, model) : String × Nat × String × String := match summary with
      | .ok s =>
        ((s.getObjValAs? String "outcome").toOption.getD "unknown",
         (picoOfJson (s.getObjValD "cost_usd")).toOption.getD bound,
         (s.getObjValAs? String "report").toOption.getD "", modelOf s cfgJson)
      | .error e => ("unknown", bound, e, modelOf Json.null cfgJson)
    let entry := Json.mkObj
      [("tool", Lean.toJson "skel prove"), ("row", Lean.toJson req.row), ("run", Lean.toJson runDir),
       ("outcome", Lean.toJson outcome), ("model", Lean.toJson model), ("costUsd", .num ⟨cost, 12⟩)]
    let (proof, why, result) ← do
      if outcome == "accepted" && out.exitCode == 0 then
        if req.checkedDisproof report then
          pure (none, report, ResultKind.disproof)
        else match req.proofOf (← IO.FS.readFile file) with
          | .ok p => pure (some p, "", ResultKind.proof)
          | .error e => pure (none, e, ResultKind.extractionFailure)
      else pure (none, report, ResultKind.unfinished)
    log s!"{outcome}, {model}, {usdText cost} USD, {runDir}{if proof.isNone then s!" (no proof: {why})" else ""}"
    return (.replied { outcome, model, costPico := cost, runDir, proof, why, result := some result }, some (cost, entry))

/-- The prover of one model: the asker of the prove requests. With no settings it gives no reply and logs `no prover configured`. A
prompt that is not a request gets no reply. Otherwise it reads the config, and under the lock of the budget file it decides
(`decide`: the cap, and spent plus the reservations of the runs in flight plus the bound within the budget) and reserves the
bound (`reserveIn`). Then it writes the frozen file `dir/<row>.lean`, runs `CMD prove FILE --config C`, and reads
`summary.json` of the run record and the final file. Last, under the lock, it removes its reservation and adds the cost and
one entry (`settleIn`). The reservations count all runs in flight. A dry run decides with the reservations of the file,
writes the frozen file, and changes no budget file. The reply is the text of a `Reply`; a refused call, a run that did not
start or exit 2 gives no reply, with the reason in the log. The run-wide cap and target book are checked under the same locks
as the reservation. Each decoded request gets one record below `dir/invocations/`; every log line names its `dir/row`. -/
def askerLink (wide : Option Wide) (cfg : Option Link) (dir : FilePath) (log : String → IO Unit) : Asker := fun prompt => do
  let t0 ← IO.monoMsNow
  let some req := Request.decode? prompt
    | log "prove: the prompt is not a prove request"; return (none, (← IO.monoMsNow) - t0)
  let log (text : String) : IO Unit :=
    (text.splitOn "\n").forM fun line => log s!"prove {dir}/{req.row}: {line}"
  let done (result : InvocationResult) : IO (Option String × Nat) := do
    let ms := (← IO.monoMsNow) - t0
    recordInvocation dir req cfg result ms
    return (result.reply?.map Reply.encode, ms)
  let noReply (why : String) : IO (Option String × Nat) := do
    log why
    done (.noReply why)
  match cfg with
  | none => noReply "no prover configured"
  | some c =>
    match ← readJson c.config with
    | .error e => noReply s!"no reply: {e}"
    | .ok cfgJson =>
      match (do pure (← boundOf cfgJson, ← usdOfText c.maxUsd) : Except String (Nat × Nat)) with
      | .error e => noReply e
      | .ok (bound, cap) =>
        let run := s!"skel prove {req.row} pid {← IO.Process.getPID} t {← IO.monoNanosNow}"
        match ← reserveBudget wide c.budget run bound cap c.dryRun with
        | .error e => noReply e
        | .ok reservation =>
          if c.dryRun then
            IO.FS.createDirAll dir
            let file := dir / s!"{fileStem req.row}.lean"
            IO.FS.writeFile file req.frozen
            log s!"dry run: {file}: bound {usdText bound} USD, cap {c.maxUsd} USD: the run would start"
            done .dryRun
          else
            let (result, charge) ← try runOne c cfgJson dir log req bound
              catch e => do
                let why := s!"no reply: {e}; charge the bound {usdText bound}"
                log why
                pure (.noReply why, some (bound, Json.mkObj [("tool", Lean.toJson "skel prove"),
                  ("row", Lean.toJson req.row), ("outcome", Lean.toJson "unknown"), ("costUsd", .num ⟨bound, 12⟩)]))
            if let .error e ← reservation.settle charge then
              log s!"the budget file {c.budget} is NOT settled for {run} (charge {charge.map (usdText ·.1)}): {e}"
            done result

/-- The ids of the allow file of the final models (`--final-allow`): one id on each line; empty lines and lines that start with
`#` are left out. No file, or a file that cannot be read, allows nothing. -/
def readAllow (path : Option String) : IO (List String) := do
  match path with
  | none => return []
  | some p =>
    try
      return ((← IO.FS.readFile p).splitOn "\n").filterMap fun l =>
        let t := l.trimAscii.toString
        if t.isEmpty || t.startsWith "#" then none else some t
    catch _ => return []

/-- Appends the record of an obligation that the first model left open to the escalation list `file`, as one JSON line with
the fields `kind`, `id` and `fields`. A line with the same `kind` and `id` that is in the file already is not written again. -/
def escalate (file : FilePath) (kind id : String) (fields : List (String × Json)) : IO Unit := do
  let old ← if ← file.pathExists then pure ((← IO.FS.readFile file).splitOn "\n") else pure []
  let same (l : String) : Bool :=
    match Json.parse l with
    | .ok j => (j.getObjValAs? String "kind").toOption == some kind && (j.getObjValAs? String "id").toOption == some id
    | .error _ => false
  unless old.any same do
    IO.FS.createDirAll (file.parent.getD ".")
    IO.FS.withFile file .append fun h =>
      h.putStrLn (Json.compress (Json.mkObj ([("kind", Lean.toJson kind), ("id", Lean.toJson id)] ++ fields)))

private def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The class of the reason that a run gave no proof (`Failed.reason`): the validator accepted a proof that the filters refuse
(`filter`), the validator checked a disproof (`disproof`), the run ended on a time-out (`timeout`), or the run ended with
no accepted proof (`validator`). -/
def reasonOf (y : Reply) : String :=
  if y.resultKind == .disproof then "disproof"
  else if y.outcome == "accepted" then "filter"
  else if hasSub (y.outcome ++ " " ++ y.why).toLower "time" then "timeout"
  else "validator"

/-- The note for the frozen file of the next model: the model and the reason of each earlier attempt that did not close the row
(at most 40 lines of the reason), as comment lines. The note goes at the end of the text before the theorem. -/
def feedbackNote (earlier : List Failed) : String :=
  let lines (e : Failed) : List String :=
    s!"-- {if e.model.isEmpty then "an earlier run" else e.model} did not close this row:" ::
      (((e.why.splitOn "\n").filter (!·.trimAscii.isEmpty)).take 40).map ("-- " ++ ·)
  "\n".intercalate (["", "-- Earlier runs on this file did not close the theorem below."] ++ earlier.flatMap lines ++ [""])

/-- The request with the note of the earlier attempts in its text before the theorem. Without earlier attempts it is `r`. -/
def Request.withFeedback (r : Request) (earlier : List Failed) : Request :=
  if earlier.isEmpty then r else { r with head := r.head ++ feedbackNote earlier }

/-- The prover with a chain of models. The first model runs first (`askerLink`), with its rounds. The models after it are the
final models: they run only for a row that the first model left open (its run gave no proof: the cap or the budget file refused
the call, the run did not start, or its rounds ended with no accepted proof that passes the filters) AND that the allow file
(`Cfg.allow`, `--final-allow`) names, by the name of the row or `dir/row`. Without the name the chain stops: the row goes to the
escalation list `dir/escalate.jsonl` (its id, frozen file, the earlier attempts with their last errors, costs and reason class,
and the total cost) and the reply is that of the first model. A final model runs in its own directory `dir/link<k>`, with its
own budget file, and its frozen file has the errors of the earlier attempts as comment lines. The first run that gives a proof
ends the chain. The reply is that run's, with its budget file, its link, and the earlier attempts with their costs (`Failed`);
a checked disproof also ends the chain. When no run gives a proof it is the newest reply that a run gave (none if no run gave one).
With one model, or a dry run, it is the reply of `askerLink`. -/
def asker (cfg : Option Cfg) (dir : FilePath) (log : String → IO Unit) : Asker := fun prompt => do
  let t0 ← IO.monoMsNow
  match cfg, Request.decode? prompt with
  | none, _ | _, none => askerLink none none dir log prompt
  | some c, some req =>
    if c.later.isEmpty || c.dryRun then
      let (r, ms) ← askerLink c.wide (some c.toLink) dir log prompt
      let tag (t : String) : String := match Reply.decode? t with | some y => { y with budget := c.budget }.encode | none => t
      return (r.map tag, ms)
    let rec go : List (Nat × Link) → List Failed → Option String → IO (Option String)
      | [], _, last => pure last
      | (i, l) :: rest, earlier, last => do
        if i > 0 then
          let ids ← readAllow c.allow
          unless ids.contains req.row || ids.contains s!"{dir}/{req.row}" do
            if i == 1 then
              escalate (dir / "escalate.jsonl") "prove" req.row
                [("dir", Lean.toJson dir.toString), ("reason", Lean.toJson ((earlier.getLast?.map (·.reason)).getD "no-run")),
                 ("costUsd", .num ⟨((earlier.map (·.costPico)).foldl (· + ·) 0 : Nat), 12⟩),
                 ("earlier", .arr (earlier.map Failed.toJson).toArray), ("frozen", Lean.toJson req.frozen)]
              log s!"escalate {req.row}: the first model left it open; the final model is not allowed ({dir / "escalate.jsonl"})"
            return last
        let lines ← IO.mkRef ([] : List String)
        let note (s : String) : IO Unit := do lines.modify (· ++ [s]); log s
        let (r, _) ← askerLink c.wide (some l) (if i == 0 then dir else dir / s!"link{i}") note
          (req.withFeedback earlier).encode
        match r.bind Reply.decode? with
        | some y =>
          let y := { y with budget := l.budget, link := i, earlier }
          if y.proof.isSome || y.resultKind == .disproof then pure (some y.encode)
          else
            let f : Failed := { model := y.model, costPico := y.costPico, budget := l.budget, why := y.why, reason := reasonOf y }
            go rest (earlier ++ [f]) (some y.encode)
        | none =>
          let why := (← lines.get).getLastD "no reply"
          let reason := if hasSub why "refused" then "cap" else "no-run"
          go rest (earlier ++ [{ model := "", costPico := 0, budget := l.budget, why, reason }]) last
    let r ← go ((List.range c.links.length).zip c.links) [] none
    return (r, (← IO.monoMsNow) - t0)

end Skel.Prove
