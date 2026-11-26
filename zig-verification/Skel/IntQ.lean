import Skel.TempDir
import Skel.IntQ.Context
import Lift.Shuffler.Internal.Unit
import Lift.Shuffler.Internal.Fns
import Lift.Shuffler.Statement

/-! The proposer of the internal statements of the shuffler (task INT-Q, W7 c of `docs/design/llm-rungs-20261120.md`).

The targets are the functions of `Lift.Shuffler.Internal.Fns.fns` (a `Fn`) that have no moved statement
(`Lift.Shuffler.Internal.moved`) and no trusted statement (`trustedEntries`). For each target the statement has the form of the moved statements, with L3 the flat model
function of the same name (the naming rule: the last component of the label, without `solidity_shuffler_`; the first
`def <name>` of `Lift/Shuffler/Zig/*.lean`, else of `Lift/Shuffler/Ext/Flat*.lean`), and the objects of the shared encoding
`Lift.Shuffler.Internal.Proposed.Layout`. The inputs are the parameters of the model function, as its source text has them.
The holes take the environment `e : Layout.Env`; the statement binds the fields of `e` that the holes read, each as a
`BitVec 64` binder (`envReads`), as the moved statements bind their addresses.

The proposer fills six holes (`Holes`): the room, the contract `C`, the arguments, the objects, the written objects and the
result field. A reply has the fixed form of `parseHoles`. The filters, in order (`Stage`): parse; the filled template elaborates;
`#stmt_shape` reads it; `checkRoom`; the refuter (`Skel/IntQ/Refute.lean`) on samples. A refute file that does not elaborate
(an input type with no sampler, a contract that is not decidable) gives the verdict `unknown`, which is not a refusal. A proposal
that fails a filter is asked again, with the rejected replies and their errors in the prompt, for at most `maxAsks` asks (the
rule of the user, INT-Q2); after `maxAsks` refused replies the target is open for the final rung. The prompt has the type
context of the model function (`Skel/IntQ/Context.lean`), and the binders of the template are its binders by elaboration,
fully qualified. The prompt is a pure function of its input, so a stored reply replays with no call (`Skel.Ask.asker`). -/

namespace Skel.IntQ

open Lean (Json)
open Skel.Gen Skel.Report.Level3 Lift.Shuffler.Internal

/-! ## The targets -/

/-- The name of a label: its last component without `solidity_shuffler_` (`swapWith`, `workspaceSize`). -/
def shortOf (label : String) : String :=
  let last := ((label.splitOn ".").getLast?).getD label
  if last.startsWith "solidity_shuffler_" then (last.splitOn "solidity_shuffler_").getLastD last else last

/-- A target: the label, its symbol and the name of its `Fn` constant in `Fns`. -/
structure Target where
  label : String
  sym : Fns.Sym
  fnConst : String

/-- The name of the `Fn` constant of a label in `Fns`: the components of the label after `.Lshuffler.`, the first lower case,
the others capitalised (`emissionSwapWith`); a `solidity_shuffler_` label gives its short name. -/
def fnConstOf (label : String) : String :=
  if label.startsWith "solidity_shuffler_" then shortOf label
  else
    match ((label.splitOn ".").filter (· != "")).drop 1 with
    | [] => label
    | p :: ps => String.join (p.decapitalize :: ps.map String.capitalize)

/-- The statement name: the short name with a capital first letter (`SwapWith`). When another function of `Fns.fns` has the same
short name (`Planner.run`, `Emission.run`), the name of the `Fn` constant with a capital first letter (`PlannerRun`). -/
def stmtName (label : String) : String :=
  let clash := (Fns.fns.filter fun (l, _) => shortOf l == shortOf label).length > 1
  (if clash then fnConstOf label else shortOf label).capitalize

/-- The entries of the functions of the shuffler that have a trusted statement: the `Fn` of each trusted statement. -/
def trustedEntries : List Int64 := [Lift.Shuffler.Statement.shuffle.entry]

/-- The targets: the functions with a `Fn`, no moved statement and no trusted statement, in the order of `Fns.fns`. -/
def targets : List Target :=
  Fns.fns.filterMap fun (l, f) =>
    if (moved.map (·.entry)).contains l || trustedEntries.contains f.entry then none
    else (Fns.syms.find? (·.label == l)).map fun s => ⟨l, s, fnConstOf l⟩

/-! ## The model function and the sources -/

/-- The flat model function of a target, from its source text. -/
structure ModelSrc where
  name : String
  file : String
  module : String
  ns : String
  opens : List String
  text : String

/-- The constant of the model function. -/
def ModelSrc.const (m : ModelSrc) : String := if m.ns.isEmpty then m.name else s!"{m.ns}.{m.name}"

/-- The model function with its binders and its result type by elaboration (`TypeCtx`), fully qualified. -/
structure Model extends ModelSrc where
  params : List Param
  ret : String

/-- The source files of the model functions, in the order of the naming rule. -/
def modelFiles : List String :=
  ["Lift/Shuffler/Zig/Basic.lean", "Lift/Shuffler/Zig/Emission.lean", "Lift/Shuffler/Zig/Planner.lean",
   "Lift/Shuffler/Zig/Shuffle.lean", "Lift/Shuffler/Ext/FlatModel.lean", "Lift/Shuffler/Ext/FlatPlan.lean",
   "Lift/Shuffler/Ext/FlatPop.lean", "Lift/Shuffler/Ext/FlatSpill.lean", "Lift/Shuffler/Ext/FlatSurplus.lean",
   "Lift/Shuffler/Ext/FlatLowest.lean"]

/-- The module of a source path. -/
def moduleOfPath (p : String) : String := ((p.splitOn ".lean").headD p).replace "/" "."

/-- The `open` commands of the lines of a file, each on one line: a line `open …` and the indented lines after it. -/
def opensOf (ls : List String) : List String :=
  let step : List String × Bool → String → List String × Bool := fun (acc, inOpen) l =>
    if l.startsWith "open " then (l :: acc, true)
    else if inOpen && l.startsWith " " then
      match acc with
      | o :: rest => ((o ++ " " ++ l.trimAscii.toString) :: rest, true)
      | [] => (acc, false)
    else (acc, false)
  (ls.foldl step ([], false)).1.reverse

/-- The model function `name` in the source text `src` of the file `file`: the comment lines above its `def` line and the
lines up to the first blank line; the namespace and the `open` lines of the file. -/
def modelIn (file src name : String) : Option ModelSrc := do
  let ls := src.splitOn "\n"
  let i ← ls.findIdx? (·.startsWith s!"def {name} ")
  let body := (ls.drop i).takeWhile (·.trimAscii.toString != "")
  let dashes := ((ls.take i).reverse.takeWhile (·.startsWith "--")).reverse
  let doc := if dashes.isEmpty then docBlock (ls.take i) else dashes
  let ns := ((ls.find? (·.startsWith "namespace ")).map fun l => (l.splitOn "namespace ").getLastD "").getD ""
  pure { name, file, module := moduleOfPath file, ns, opens := opensOf ls,
         text := "\n".intercalate (doc ++ body) }
where
  /-- The doc comment `/-- … -/` that ends on the line above, if any. -/
  docBlock (pre : List String) : List String :=
    match pre.reverse with
    | last :: _ =>
      if last.trimAscii.toString.endsWith "-/" then
        let rev := pre.reverse
        match rev.findIdx? (·.trimAscii.toString.startsWith "/-") with
        | some k => (rev.take (k + 1)).reverse
        | none => []
      else []
    | [] => []

/-- The model function of a name: the first file of `modelFiles` that has it. -/
def findModelNamed (name : String) : IO (Option ModelSrc) := do
  for f in modelFiles do
    let src ← IO.FS.readFile f
    if let some m := modelIn f src name then return some m
  return none

/-- The model function of a label: the one of its short name (`swapWith`), else the one of its `Fn` constant name
(`Planner.run` has `plannerRun`). -/
def findModel (label : String) : IO (Option ModelSrc) := do
  match ← findModelNamed (shortOf label) with
  | some m => pure (some m)
  | none => findModelNamed (fnConstOf label)

/-- The Zig source of the function of a label in `shuffler.zig`: the doc lines (`///`) above its `fn` line and the lines up to
the `}` at its indentation. A label `.Lshuffler.S.f` is the first `fn f(` after the line `const S = `; a `solidity_shuffler_f`
label is a top-level `fn f(`. -/
def zigSource (zig label : String) : Option String := do
  let ls := zig.splitOn "\n"
  let parts := (label.splitOn ".").filter (· != "")
  let name := shortOf label
  let start ← match parts with
    | [_, s, _] => ls.findIdx? (·.startsWith s!"const {s} = ")
    | _ => some 0
  let rest := ls.drop start
  let k ← rest.findIdx? fun l => (l.splitOn s!"fn {name}(").length > 1
  let fnLine := rest[k]!
  let indent := (fnLine.toList.takeWhile (· == ' ')).length
  let close := String.ofList (List.replicate indent ' ') ++ "}"
  let body := (rest.drop k).takeWhile (· != close)
  let docs := ((rest.take k).reverse.takeWhile (·.trimAscii.toString.startsWith "///")).reverse
  pure ("\n".intercalate (docs ++ body ++ [close]))

/-- The signature of a label in `types.json`: `<unit>(<param type> <size> bytes, …) -> <ret type> <size> bytes`. -/
def signature (types : Json) (label : String) : Option String := do
  let unitName := "shuffler." ++ ((label.replace "solidity_shuffler_" "").replace ".Lshuffler." "")
  let units ← (types.getObjValAs? (Array Json) "units").toOption
  let tys ← (types.getObjValAs? (Array Json) "types").toOption
  let u ← units.find? fun u => (u.getObjValAs? String "name").toOption == some unitName
  let ty (id : Nat) : String := match tys.find? (fun t => (t.getObjValAs? Nat "id").toOption == some id) with
    | some t => s!"{(t.getObjValAs? String "name").toOption.getD "?"} ({(t.getObjValAs? Nat "size").toOption.getD 0} bytes)"
    | none => s!"type {id}"
  let ps ← (u.getObjValAs? (Array Nat) "params").toOption
  let r ← (u.getObjValAs? Nat "ret").toOption
  pure s!"{unitName}({", ".intercalate (ps.toList.map ty)}) -> {ty r}"

/-- Compiler record offsets reachable from the signature, including pointer targets and array elements.
The closure takes at most one round per type. A pointer cycle therefore ends without losing a record. -/
def recordLayouts (types : Json) (label : String) : Option String := do
  let unitName := "shuffler." ++ ((label.replace "solidity_shuffler_" "").replace ".Lshuffler." "")
  let units ← (types.getObjValAs? (Array Json) "units").toOption
  let tys ← (types.getObjValAs? (Array Json) "types").toOption
  let u ← units.find? fun u => (u.getObjValAs? String "name").toOption == some unitName
  let ps ← (u.getObjValAs? (Array Nat) "params").toOption
  let r ← (u.getObjValAs? Nat "ret").toOption
  let refs (t : Json) : List Nat :=
    ["to", "elem"].filterMap (fun k => (t.getObjValAs? Nat k).toOption) ++
      ((t.getObjValAs? (Array Json) "fields").toOption.getD #[]).toList.filterMap
        (fun f => (f.getObjValAs? Nat "type").toOption)
  let reachable := (List.range tys.size).foldl (fun seen _ =>
    (seen ++ tys.toList.flatMap (fun t =>
      if (t.getObjValAs? Nat "id").toOption.any seen.contains then refs t else [])).eraseDups)
    (ps.toList ++ [r])
  let records := tys.toList.filter fun t =>
    (t.getObjValAs? String "kind").toOption == some "record" &&
      (t.getObjValAs? Nat "id").toOption.any reachable.contains
  let rows ← records.mapM fun t => do
    let name ← (t.getObjValAs? String "name").toOption
    let size ← (t.getObjValAs? Nat "size").toOption
    let align ← (t.getObjValAs? Nat "align").toOption
    let fields ← (t.getObjValAs? (Array Json) "fields").toOption
    let fs ← fields.toList.mapM fun f => do
      let n ← (f.getObjValAs? String "name").toOption
      let o ← (f.getObjValAs? Nat "offset").toOption
      let s ← (f.getObjValAs? Nat "size").toOption
      pure s!"  {n}: offset {o}, size {s}"
    pure ("\n".intercalate (s!"{name}: size {size}, alignment {align}" :: fs))
  pure ("\n".intercalate rows)

/-- The words of a text: its maximal runs of identifier characters. `Layout.pend` has the words `Layout` and `pend`. -/
def words (s : String) : List String :=
  let (cur, acc) := s.toList.foldr
    (fun c (cur, acc) => if Lean.isIdRest c then (c :: cur, acc) else ([], if cur.isEmpty then acc else String.ofList cur :: acc))
    ([], [])
  if cur.isEmpty then acc else String.ofList cur :: acc

/-! ## The records of a function

A function takes a record by pointer (`self: *const Planner`). The model names the fields by the machine layout of the record
(`⟨e.self + 24, …⟩`), so the prompt has the Zig record of each such type, with its fields only: the layout of INT-Q3 found that
the statements of the planner functions had the layout of `Emission`. The record `Emission` has its layout in `Layout.lean`. -/

/-- The names of the records whose layout is in `Layout.lean`. -/
def layoutRecords : List String := ["Emission"]

/-- The lines of the record `name` in the Zig file `zig`: the doc comment above it, `const name = extern struct {`, each field
(with the doc lines above it) and `};`. None when there is no such record. The methods are not part of it. -/
def recordIn (zig name : String) : Option (List String) := do
  let ls := zig.splitOn "\n"
  let start ← ls.findIdx? fun l => l == s!"const {name} = extern struct \{" || l == s!"pub const {name} = extern struct \{"
  let docs := ((ls.take start).reverse.takeWhile (·.startsWith "///")).reverse
  let body := (ls.drop (start + 1)).takeWhile (· != "};")
  let isField (l : String) : Bool :=
    l.startsWith "    " && !l.startsWith "     " &&
      let w := (l.drop 4).toString
      let id := String.ofList (w.toList.takeWhile Lean.isIdRest)
      id != "" && (w.drop id.length).startsWith ": "
  let (_, kept) := body.foldl
    (fun (pending, kept) l =>
      if l.startsWith "    ///" then (pending ++ [l], kept)
      else if isField l then ([], kept ++ pending ++ [l])
      else ([], kept))
    (([] : List String), ([] : List String))
  pure (docs ++ [ls[start]!] ++ kept ++ ["};"])

/-- The field types of a record that are records by value: the type of a field is a name (no pointer, no array). -/
def recordFieldTypes (def_ : List String) : List String :=
  def_.filterMap fun l =>
    if l.startsWith "    " && !l.startsWith "     " && !l.startsWith "    ///" then
      let t := (((l.drop 4).toString).splitOn ": ").getD 1 ""
      let t := (t.splitOn ",").headD ""
      if (t.all Lean.isIdRest) && t != "" then some t else none
    else none

/-- The alias `const name = <type>;` of the Zig file `zig` on one line, with the doc comment above it. -/
def aliasIn (zig name : String) : Option (List String) := do
  let ls := zig.splitOn "\n"
  let i ← ls.findIdx? fun l => (l.startsWith s!"const {name} = " || l.startsWith s!"pub const {name} = ") && l.endsWith ";"
  pure (((ls.take i).reverse.takeWhile (·.startsWith "///")).reverse ++ [ls[i]!])

/-- The records that the signature of the Zig function `fnSrc` names, and the records and aliases that they use by value, in
order of first use, as text; none for the records of `layoutRecords`. The signature is the text up to the first line that ends
with `{`. -/
def recordDefs (zig fnSrc : String) : List String :=
  let ls := fnSrc.splitOn "\n"
  let sigLines := (ls.takeWhile fun l => !l.trimAsciiEnd.toString.endsWith "{") ++ (ls.dropWhile fun l => !l.trimAsciiEnd.toString.endsWith "{").take 1
  let rec go (fuel : Nat) (todo : List String) (seen : List (String × List String)) : List (String × List String) :=
    match fuel, todo with
    | 0, _ | _, [] => seen
    | fuel + 1, n :: rest =>
      if (seen.map (·.1)).contains n || layoutRecords.contains n then go fuel rest seen
      else match recordIn zig n with
        | some d => go fuel (rest ++ recordFieldTypes d) (seen ++ [(n, d)])
        | none => match aliasIn zig n with
          | some d => go fuel rest (seen ++ [(n, d)])
          | none => go fuel rest seen
  (go 64 (words ("\n".intercalate sigLines)) []).map fun (_, d) => "\n".intercalate d

/-! ## The holes and the template -/

/-- The scalar types allowed in extra interface inputs. Products are right-associative. -/
inductive InputScalar where
  | word (width : Width)
  | pair (left right : InputScalar)
  deriving BEq, Repr

def InputScalar.render : InputScalar → String
  | .word .W8 => "BitVec 8"
  | .word .W16 => "BitVec 16"
  | .word .W32 => "BitVec 32"
  | .word .W64 => "BitVec 64"
  | .pair a b => s!"({a.render} × {b.render})"

/-- A pointer marker selects an address sampler, but its statement type is `BitVec 64`. -/
inductive InputType where
  | pointer
  | scalar (type : InputScalar)
  | vector (type : InputScalar) (size : Fin 65537)
  deriving BEq, Repr

def InputType.render : InputType → String
  | .pointer => "BitVec 64"
  | .scalar t => t.render
  | .vector t n => s!"Vector ({t.render}) {n.val}"

structure InputBinder where
  name : String
  type : InputType
  deriving BEq, Repr

/-- Parse only words, products and parentheses. No Lean syntax is passed through this parser. -/
private def parseScalar : Nat → List String → Except String (InputScalar × List String)
  | 0, _ => .error "the extra input type is too deep"
  | fuel + 1, tokens => do
    let (a, rest) ← match tokens with
      | "BitVec" :: bits :: rest =>
        let w ← match bits with
          | "8" => pure Width.W8 | "16" => pure Width.W16
          | "32" => pure Width.W32 | "64" => pure Width.W64
          | _ => throw "extra words have width 8, 16, 32 or 64"
        pure (.word w, rest)
      | "(" :: rest => do
        let (a, rest) ← parseScalar fuel rest
        match rest with
        | ")" :: rest => pure (a, rest)
        | _ => throw "the extra input type has an unmatched parenthesis"
      | _ => throw "expected BitVec or a parenthesized product in the extra input type"
    match rest with
    | "×" :: rest => do
      let (b, rest) ← parseScalar fuel rest
      pure (.pair a b, rest)
    | _ => pure (a, rest)

/-- The closed type grammar of BINDERS. Vector lengths are explicit and at most 65536. -/
def parseInputType (text : String) : Except String InputType := do
  let tokens := ((text.replace "(" " ( ").replace ")" " ) ").replace "×" " × " |>.splitOn " "
    |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)
  if tokens == ["Ptr"] then return .pointer
  match tokens with
  | "Vector" :: rest =>
    let (t, rest) ← parseScalar (tokens.length + 1) rest
    let [size] := rest | throw "an extra vector needs one literal length"
    let some n := size.toNat? | throw "the extra vector length is not a number"
    if h : n < 65537 then pure (.vector t ⟨n, h⟩)
    else throw "the extra vector length exceeds 65536"
  | _ =>
    let (t, rest) ← parseScalar (tokens.length + 1) tokens
    unless rest.isEmpty do throw "unexpected text after the extra input type"
    pure (.scalar t)

/-- Lean keywords cannot be used as unescaped input names. -/
def inputKeywords : List String :=
  ["let", "in", "if", "then", "else", "match", "with", "do", "fun", "forall", "exists", "by", "where", "return",
   "unless", "for", "while", "break", "continue", "have", "show", "from", "as", "at", "case", "of", "deriving"]

/-- One input per line: an ASCII name, a colon and a closed type. -/
def parseInputs (text : String) : Except String (List InputBinder) := do
  let lines := text.splitOn "\n"
  if lines.length > 64 then throw "BINDERS has more than 64 inputs"
  lines.foldlM (init := []) fun inputs line => do
    let [name, ty] := line.splitOn ":" | throw "an extra input needs one name and one type separated by `:`"
    let name := name.trimAscii.toString
    let asciiAlpha (c : Char) := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
    unless name.toList.head?.any asciiAlpha && name.all (fun c => asciiAlpha c || c.isDigit || c == '_') do
      throw s!"invalid extra input name `{name}`"
    if inputKeywords.contains name then throw s!"extra input `{name}` is a keyword"
    if inputs.any (fun b => b.name == name) then throw s!"duplicate extra input `{name}`"
    let type ← parseInputType ty.trimAscii.toString
    pure (inputs ++ [⟨name, type⟩])

/-- The variable parts of a statement. Each text is Lean source of the template (`fill`). -/
structure Holes where
  room : Nat
  inputs : List InputBinder := []
  contract : String
  args : String
  objects : String
  written : String
  result : String
  deriving BEq, Repr

/-- The section names of a reply, in order. -/
def sections : List String := ["ROOM", "CONTRACT", "ARGS", "OBJECTS", "WRITTEN", "RESULT"]

/-- The words that a hole must not have: a hole is a term, not a command, and has no escape from the kernel. A word is a
maximal run of identifier characters (`words`): `pend` is not the word `end`. The entries that are not words (`#`, `@[`) are
found as text. -/
def badWords : List String :=
  ["sorry", "axiom", "native_decide", "import", "set_option", "theorem", "lemma", "def", "abbrev", "instance", "macro",
   "syntax", "elab", "#", "attribute", "opaque", "unsafe", "implemented_by", "extern", "namespace", "end", "open", "section",
   "noncomputable", "partial", "decreasing_by", "termination_by", "@["]

/-- Whether the entry `w` of `badWords` is in the text `b`: as a word, or as text when it is no word. -/
def hasBadWord (b w : String) : Bool :=
  if w.all Lean.isIdRest then (words b).contains w else (b.splitOn w).length > 1

/-- The holes of a reply. The form: a line `=== ROOM`, then the room (a number); a line `=== CONTRACT`, then a Lean
proposition (an optional `=== BINDERS` before CONTRACT declares extra interface inputs); `=== ARGS`, a `List Field`; `=== OBJECTS`, a `List Object`; `=== WRITTEN`, a `List Object` in `y`; `=== RESULT`, a
`Field` in `y`; then a line `=== END`. The lines before `=== ROOM` and after `=== END` are not read. Each section is not blank,
and no section has a word of `badWords`. -/
def parseHoles (reply : String) : Except String Holes := do
  let ls := (reply.splitOn "\n").map (·.trimAsciiEnd.toString)
  let some i := ls.findIdx? (· == "=== ROOM") | throw "the reply has no line `=== ROOM`"
  let ls := ls.drop i
  let some j := ls.findIdx? (· == "=== END") | throw "the reply has no line `=== END`"
  let ls := ls.take j
  let rec split (cur : Option (String × List String)) (acc : List (String × String)) : List String → List (String × String)
    | [] => match cur with
      | some (n, b) => acc ++ [(n, "\n".intercalate b.reverse)]
      | none => acc
    | l :: rest =>
      if l.startsWith "=== " then
        let acc := match cur with
          | some (n, b) => acc ++ [(n, "\n".intercalate b.reverse)]
          | none => acc
        split (some ((l.drop 4).toString, [])) acc rest
      else split (cur.map fun (n, b) => (n, l :: b)) acc rest
  let secs := split none [] ls
  let names := secs.map (·.1)
  unless names == sections || names == ["ROOM", "BINDERS"] ++ sections.drop 1 do
    throw s!"the sections are {names}, not {sections} with optional BINDERS after ROOM (then END)"
  for (n, b) in secs do
    if b.trimAscii.toString.isEmpty then throw s!"the section {n} is blank"
    for w in badWords do
      if hasBadWord b w then throw s!"the section {n} has the word `{w}`"
  let get (n : String) : String := ((secs.lookup n).getD "").trimAscii.toString
  let some room := (get "ROOM").toNat? | throw s!"the room `{get "ROOM"}` is not a number"
  let inputs ← match secs.lookup "BINDERS" with
    | some text => parseInputs text.trimAscii.toString
    | none => pure []
  pure { room, inputs, contract := get "CONTRACT", args := get "ARGS", objects := get "OBJECTS", written := get "WRITTEN",
         result := get "RESULT" }

/-- What the template needs of a target. -/
structure Ctx where
  target : Target
  model : Model

def Ctx.name (c : Ctx) : String := stmtName c.target.label

/-- The statement module. -/
def Ctx.module (c : Ctx) : String := s!"Lift.Shuffler.Internal.Proposed.{c.name}Statement"

/-- The statement constant. -/
def Ctx.const (c : Ctx) : String := s!"{c.module}.{c.name}Statement"

/-- The existing Call8 form covers eight integer arguments with two 64-bit stack words. -/
def Ctx.usesStack (c : Ctx) : Bool := c.target.sym.args.length == 8

/-- Unsupported ABI forms are refused before a statement can be accepted. -/
def supportedArgs (widths : List Width) : Bool :=
  widths.length ≤ 6 || (widths.length == 8 && widths.drop 6 == [.W64, .W64])

/-- The parameters of the model as binders of a definition: `(st : St) (pos : Word)`. -/
def Ctx.binders (c : Ctx) : String :=
  " ".intercalate (c.model.params.map fun p =>
    if p.implicit then s!"\{{" ".intercalate p.names} : {p.type}}" else s!"({" ".intercalate p.names} : {p.type})")

/-- The names of the parameters, in order. -/
def Ctx.names (c : Ctx) : List String := c.model.params.flatMap (·.names)

/-- `f` applied to the names of the parameters. -/
def Ctx.app (c : Ctx) (f : String) : String := " ".intercalate (f :: c.names)

/-- Interface inputs are independent of the parameters of the model. -/
def Ctx.interfaceBinders (c : Ctx) (h : Holes) : String :=
  " ".intercalate (([c.binders].filter (!·.isEmpty)) ++ h.inputs.map fun b => s!"({b.name} : {b.type.render})")

def Ctx.interfaceApp (c : Ctx) (h : Holes) (f : String) : String :=
  " ".intercalate (f :: c.names ++ h.inputs.map (·.name))

def widthCtor (w : Width) : String := match w with
  | .W8 => ".W8" | .W16 => ".W16" | .W32 => ".W32" | .W64 => ".W64"

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The text after `binders` in a definition header: a space when there is a binder. -/
private def sp (b : String) : String := if b.isEmpty then "" else " " ++ b

/-! ## The binders of the environment

The upper chain takes a binder of the type `BitVec 64` or `List (BitVec 64)` only (`Skel.Gen.binderOf`). So the statement has no
binder `e : Layout.Env`: it has one `BitVec 64` binder for each field of `Layout.Env` that the holes read (`envReads`), and gives
the holes the environment `envOf` of these binders. A field that no hole reads has no binder and the value 0. -/

/-- The fields of `Layout.Env` (`Lift/Shuffler/Internal/Proposed/Layout.lean`), in order, with their widths in bits. -/
def envFields : List (String × Nat) :=
  [("self", 64), ("target", 64), ("spills", 64), ("data", 64), ("trace", 64), ("mapping", 64), ("pad", 16)]

/-- The fields of `Layout.Env` that each definition of `Layout` with a parameter of the type `Env` reads. -/
def layoutReads : List (String × List String) :=
  [("targetPtr", ["self", "target"]), ("targetSize", ["self"]), ("spillsPtr", ["self", "spills"]),
   ("maxSwapDepth", ["self"]), ("maxDupDepth", ["self"]), ("dataPtr", ["self", "data"]), ("size", ["self"]),
   ("tracePtr", ["self", "trace"]), ("traceSize", ["self"]), ("mappingPtr", ["self", "mapping"]), ("pend", ["self"]),
   ("blocked", ["self"]), ("data", ["data"]), ("trace", ["trace"]), ("target", ["target"]), ("dest", ["mapping"]), ("pos", ["mapping"]),
   ("spillByte", ["spills"])]

/-- The fields that one use of the identifier `e` reads: `e.f` reads `f`; `Layout.h e` reads the fields of `h` in
`layoutReads`. Any other use reads each field. `before` is the text before `e` (reversed), `after` the text after it. -/
private def useReads (before after : List Char) : List String :=
  let all := envFields.map (·.1)
  match after with
  | '.' :: rest =>
    let f := String.ofList (rest.takeWhile Lean.isIdRest)
    if (envFields.map (·.1)).contains f then [f] else all
  | _ =>
    let name := String.ofList ((before.dropWhile Char.isWhitespace).takeWhile (fun c => Lean.isIdRest c || c == '.')).reverse
    match (name.splitOn ".").reverse, before.head? with
    | h :: "Layout" :: _, some c => if c.isWhitespace then (layoutReads.lookup h).getD all else all
    | _, _ => all

/-- The fields that the text `s` reads, by `useReads` at each use of the identifier `e` (an `e` that is no part of a longer
name, and no field of another name). -/
private def textReads (s : String) : List String :=
  let rec go (before : List Char) : List Char → List String
    | [] => []
    | c :: after =>
      let isUse := c == 'e' && !(after.head?.any Lean.isIdRest) && !(before.head?.any fun b => Lean.isIdRest b || b == '.')
      (if isUse then useReads before after else []) ++ go (c :: before) after
  go [] s.toList

/-- The fields of `Layout.Env` that the holes `args`, `objects` and `written` read, in the order of `envFields`. -/
def envReads (h : Holes) : List String :=
  let rs := [h.args, h.objects, h.written].flatMap textReads
  (envFields.map (·.1)).filter rs.contains

/-- The name of the binder of the field `f`: `f`, or `e_f` when an input has the name `f`. -/
def Ctx.fieldBinder (c : Ctx) (f : String) : String := if c.names.contains f then s!"e_{f}" else f

/-- Refuse names that would capture model inputs, environment fields or template locals. -/
def validateInputs (c : Ctx) (h : Holes) : Except String Unit := do
  let reserved := ["e", "y", "policy", "r", "m", "g", "junk", "run", "C", "args", "objects", "written", "result",
    "post", "fn", "envOf", "abiArgs", "stackArgs", "refuteCase", "BitVec", "Vector", "Option", "Prop", "Field", "Object", "Layout"] ++ c.names ++ envFields.map (·.1) ++ envFields.map (s!"e_{·.1}")
  for b in h.inputs do
    if reserved.contains b.name || badWords.contains b.name then throw s!"extra input `{b.name}` captures a reserved name"
  pure ()

/-- The `open` lines of the statement, in order. -/
def scopeOpens (c : Ctx) : List String :=
  ["open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Shuffler.Internal.Proposed"] ++ c.model.opens ++ [s!"open {c.model.ns}"]

/-- The imports of the statement of a model module (`Ctx.imports` without a context). -/
def importsFor (module : String) : List String :=
  ["Lift.Trusted.Call", "Lift.Trusted.Encode", "Lift.Pilot.Call", "Lift.Pilot.Encode", "Lift.Pilot.Slot", "Lift.Shuffler.Code",
   "Lift.Shuffler.Internal.Proposed.Layout", module]

/-- The imports of the statement module. -/
def Ctx.imports (c : Ctx) : List String :=
  importsFor c.model.module ++ (if c.usesStack then ["Lift.Level2z.Args8Statement"] else [])

/-- The body of the statement module (after the imports): the template filled with the holes `h`. `source` names where the
holes come from. -/
def fillBody (c : Ctx) (h : Holes) (source : String) : String :=
  let b := sp (c.interfaceBinders h)
  let modelBinders := sp c.binders
  let ind (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("  " ++ ·))
  let forallText := if c.model.params.isEmpty && h.inputs.isEmpty then "" else s!"∀{b}, "
  let reads := envReads h
  let names := reads.map c.fieldBinder
  let envBinders := if names.isEmpty then "" else s!" ({" ".intercalate names} : BitVec 64)"
  let envArg := if names.isEmpty then "envOf" else s!"({" ".intercalate ("envOf" :: names)})"
  let envForall := if names.isEmpty then "" else s!"∀ {" ".intercalate names} : BitVec 64, "
  let fieldValue (f : String) (bits : Nat) : String :=
    if reads.contains f then (if bits == 64 then c.fieldBinder f else s!"{c.fieldBinder f}.setWidth {bits}") else "0"
  let envValue := ", ".intercalate (envFields.map fun (f, bits) => s!"{f} := {fieldValue f bits}")
  let unread := (envFields.map (·.1)).filter (!reads.contains ·)
  let unreadText := if unread.isEmpty then "Each field has a binder." else
    s!"The fields that no hole reads have no binder: {", ".intercalate unread}."
  "\n".intercalate (
  [ "",
    s!"/-! The proposed statement of `{c.target.label}` (task INT-Q; source: {source}). A lemma, not a trusted statement. L3 is",
    s!"`{c.model.ns}.{c.model.name}` (`{c.model.file}`). The holes are the room, `C`, `args`, `objects`, `written` and `result`. -/",
    "",
    s!"namespace {c.module}",
    "" ] ++
  scopeOpens c ++
  [ "",
    s!"/-- `{c.target.label}` in `Lift.Shuffler.Code.code`: the entry of its symbol, the room of the proposal, the result width",
    "of its signature. -/",
    s!"def fn : Fn := ⟨Lift.Shuffler.Code.code, {hex c.target.sym.entry.toBitVec.toNat}, {h.room}, {widthCtor c.target.sym.ret}⟩",
    "",
    s!"/-- L3: `{c.model.name}` of the inputs. -/",
    s!"def run{modelBinders} : Option ({c.model.ret}) := some ({c.app c.model.const})",
    "",
    "/-- The contract. -/",
    s!"abbrev C{b} : Prop :=", ind h.contract,
    "",
    "/-- The argument fields, in the order of the argument registers. -/",
    s!"def args{b} (e : Layout.Env) : List Field :=", ind h.args ] ++
  (if c.usesStack then
    [ "", "/-- The complete ABI arguments. The type requires exactly eight fields. -/",
      s!"def abiArgs{b} (e : Layout.Env) : Vector Field 8 :=",
      s!"  ⟨({c.interfaceApp h "args"} e).toArray, rfl⟩",
      "", "/-- The two stack fields have width 64. -/",
      s!"def stackArgs{b} (e : Layout.Env) : BitVec 64 × BitVec 64 :=",
      s!"  ((({c.interfaceApp h "abiArgs"} e)[6]).v, (({c.interfaceApp h "abiArgs"} e)[7]).v)" ]
   else []) ++
  [ "",
    "/-- The objects of the call. -/",
    s!"def objects{b} (e : Layout.Env) : List Object :=", ind h.objects,
    "",
    "/-- The written objects at the return, with the contents of the L3 result `y`. -/",
    s!"def written{b} (e : Layout.Env) (y : {c.model.ret}) : List Object :=", ind h.written,
    "",
    "/-- The result field of the L3 result `y`. A `simp` lemma: `simp` with the encoding of `post` gives the field of `y`, as for",
    "the `Encode.encode y = [r]` of the moved statements. -/",
    s!"@[simp] def result{b} (y : {c.model.ret}) : Field :=", ind h.result,
    "",
    "/-- At the return, L3 gives `y`: the result field is `result y` (`Encode.encode t = [r]`, the form of the moved statements),",
    "and the written objects have the contents of `y` (no clause when `written` is `[]`). -/",
    s!"def post{b} (e : Layout.Env) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=",
    s!"  ∃ y, {c.app "run"} = some y ∧ Encode.encode ({c.interfaceApp h "result"} y) = [r]" ++
      (if h.written.trimAscii.toString == "[]" then "" else s!" ∧ ∀ o ∈ {c.interfaceApp h "written"} e y, Mem.has policy m o"),
    "",
    "/-- The environment of the statement: a field that a hole reads is a binder of the statement (a narrower field has the low",
    s!"bits of its binder); a field that no hole reads has the value 0. {unreadText} -/",
    s!"def envOf{envBinders} : Layout.Env :=",
    s!"  \{ {envValue} }",
    "",
    "/-- For each input in the contract and each value of the fields that the holes read, the call returns as L3 says. -/",
    s!"def {c.name}Statement : Prop :=",
    (if c.usesStack then
      let a := s!"({c.interfaceApp h "abiArgs"} {envArg})"
      let st := s!"({c.interfaceApp h "stackArgs"} {envArg})"
      s!"  {forallText}{c.interfaceApp h "C"} → {envForall}fn.Call8B ({a}.toList.take 6) {st}.1 {st}.2 ({c.interfaceApp h "objects"} {envArg}) ({c.interfaceApp h "post"} {envArg})"
     else
      s!"  {forallText}{c.interfaceApp h "C"} → {envForall}fn.CallB ({c.interfaceApp h "args"} {envArg}) ({c.interfaceApp h "objects"} {envArg}) ({c.interfaceApp h "post"} {envArg})"),
    "",
    s!"end {c.module}",
    "" ])

/-- The statement module: a header, the imports and the body. -/
def fill (c : Ctx) (h : Holes) (source : String) (extraImports : List String := []) : String :=
  "\n".intercalate (
    [s!"-- Generated by Skel/IntQ.lean (task INT-Q) from the holes of a proposal. Do not edit by hand."] ++
    (c.imports ++ extraImports).map ("import " ++ ·)) ++ "\n" ++ fillBody c h source

/-- The text of the refute file: the statement with the refuter imported, `refuteCase` and the verdict of `n` samples. A sample
outside the contract has no arguments, no objects and no result: the model is not run on it (its loop need not end there). -/
def refuteText (c : Ctx) (h : Holes) (n seed : Nat) : String :=
  let draws := c.model.params.flatMap fun p => p.names.map fun x => s!"  let ({x}, g) := (Skel.IntQ.Refute.draw g : ({p.type}) × _)"
  let extraDraws := h.inputs.zipIdx |>.map fun (b, i) => match b.type with
    | .pointer => s!"  let ({b.name}, g) := Skel.IntQ.Refute.pointer {i} g"
    | _ => s!"  let ({b.name}, g) := (Skel.IntQ.Refute.draw g : ({b.type.render}) × _)"
  let allArgs := c.interfaceApp h s!"{c.module}.args" ++ " e"
  let st := s!"({c.interfaceApp h s!"{c.module}.stackArgs"} e)"
  let regArgs := if c.usesStack then s!"({allArgs}).take 6" else allArgs
  let stack := if c.usesStack then s!", stack := some {st}" else ""
  fill c h "refute" ["Skel.IntQ.Refute", "Skel.IntQ.RefuteDraw"] ++ "\n" ++ "\n".intercalate (
    [ s!"open {c.module} in",
      "open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Shuffler.Internal.Proposed in"] ++
    c.model.opens.map (· ++ " in") ++
    [ s!"open {c.model.ns} in",
      "def refuteCase (g : Coordinator.Dst.Rng) : Skel.IntQ.Refute.Case :="] ++ draws ++ extraDraws ++
    [ s!"  if decide ({c.interfaceApp h s!"{c.module}.C"}) then",
      "    let (e, g) := Skel.IntQ.Refute.env g",
      "    let (junk, _) := Skel.IntQ.Refute.word g",
      s!"    Skel.IntQ.Refute.withExpected {c.module}.fn",
      s!"      \{ pre := true, args := {regArgs}{stack},",
      s!"        objs := {c.interfaceApp h s!"{c.module}.objects"} e, junk, expect := none }",
      s!"      (fun _ => ({c.app s!"{c.module}.run"}).map fun y => ({c.interfaceApp h s!"{c.module}.result"} y, {c.interfaceApp h s!"{c.module}.written"} e y))",
      "  else { pre := false, args := [], objs := [], junk := 0, expect := none }",
      "",
      s!"#eval IO.println (Skel.IntQ.Refute.verdict {c.module}.fn {n} {seed} refuteCase)",
      "" ])

/-- The text of the shape file: the statement and `#stmt_shape`. -/
def shapeText (c : Ctx) (h : Holes) : String :=
  fill c h "check" ["Skel.Lean.Shape"] ++ s!"\n#stmt_shape {c.const}\n"

/-! ## The prompt -/

/-- The input of a prompt: the context, the sources, the examples, and the rejected proposals with their errors. -/
structure PromptIn where
  ctx : Ctx
  zig : String
  signature : String
  layout : String
  examples : List (String × String)
  types : TypeCtx
  /-- The Zig records of the signature (`recordDefs`). -/
  records : List String := []
  /-- Compiler record offsets, including records behind pointers. -/
  recordLayouts : String := ""
  rejected : List (String × String) := []

/-- The most bytes of a prompt. `leantools ask` refuses a call whose bound is above `--max-usd` (0.12 USD): with the
config `bench/intq/ask.json` (`maxTokens` 393216 at 0.294 USD per M, input 0.098 USD per M byte of the bound) the bound is
0.1156 USD plus 0.098 USD per M bytes of the prompt, so a prompt has at most 44780 bytes. -/
def promptLimit : Nat := 44000

/-- The part of a reply from the line `=== ROOM` to the line `=== END`, or its first 1500 characters when it has no such
part: the text of a rejected reply in the prompt. -/
def holesPart (r : String) : String :=
  let ls := r.splitOn "\n"
  match ls.findIdx? (·.trimAsciiEnd.toString == "=== ROOM") with
  | some i =>
    let rest := ls.drop i
    let n := ((rest.findIdx? (·.trimAsciiEnd.toString == "=== END")).map (· + 1)).getD rest.length
    "\n".intercalate (rest.take n)
  | none => (r.take 1500).toString

/-- The prompt at a level of detail: `level` of `TypeCtx.render` for the type context, and from level 4 no examples. -/
def promptAt (p : PromptIn) (level : Nat) : String :=
  let c := p.ctx
  let h : Holes := { room := 0, contract := "<CONTRACT>", args := "<ARGS>", objects := "<OBJECTS>", written := "<WRITTEN>",
                     result := "<RESULT>" }
  let tmpl := (fill c h "template").replace "fn : Fn := ⟨Lift.Shuffler.Code.code, " "fn : Fn := ⟨Lift.Shuffler.Code.code, "
  let tmpl := tmpl.replace s!", 0, {widthCtor c.target.sym.ret}⟩" s!", <ROOM>, {widthCtor c.target.sym.ret}⟩"
  "\n".intercalate (
  [ s!"Write the Lean 4 statement (contract) of the internal function `{c.target.label}` of the Zig shuffler, as machine code in",
    "`Lift.Shuffler.Code.code` (x86-64, System V). The statement is a lemma that a later step proves; a wrong statement does not",
    "compose. Fill the holes of the template below. Give only the holes, in this form (nothing else is read):",
    "",
    "=== ROOM", "<the stack room in bytes, a number>", "=== CONTRACT", "<a decidable Lean proposition in the inputs>",
    "=== ARGS", "<a `List Field` in the inputs and `e`>", "=== OBJECTS", "<a `List Object` in the inputs and `e`>",
    "=== WRITTEN", "<a `List Object` in the inputs, `e` and the L3 result `y`>", "=== RESULT", "<a `Field` in the inputs and `y`>",
    "=== END",
    "",
    "Optional section after ROOM: `=== BINDERS`, then one `name : type` per line. Names must be distinct ASCII identifiers",
    "There are at most 64 inputs; names must not capture model inputs, environment fields or template locals. Types: Ptr (a BitVec 64 address), BitVec 8/16/32/64,",
    "products with × and parentheses, or Vector (scalar type) N with literal N from 0 to 65536. These inputs are bound before C",
    "and are in scope in every hole. They describe independent memory and are not arguments of the L3 model call.",
    "ARGS lists every ABI field in order. For eight arguments the template uses Call8: six register fields, followed by",
    "two 64-bit words at entry rsp + 8 and rsp + 16. Their pointees belong in OBJECTS, not the stack words themselves.",
    "",
    "Rules: a hole is a term, with no command and no `sorry`. The room is the room of frameFacts below. The objects come from the",
    "shared encoding `Layout` where it has the field. An object is writable only when the code writes it. The written objects",
    "are the writable objects with the contents of `y`. The result field has the width of the signature. The checks: the file",
    "elaborates; `#stmt_shape` reads it; the room is the room of frameFacts; a refuter runs the machine code on random entry",
    "states in the contract and compares the return with `post`.",
    "",
    s!"## The function: `{c.target.label}`",
    s!"Entry {hex c.target.sym.entry.toBitVec.toNat}, size {c.target.sym.size} bytes, room of frameFacts: " ++
      (match c.target.sym.room with | some r => s!"{r}" | none => "unknown") ++ ".",
    s!"Signature (types.json): {p.signature}",
    "",
    "Zig source (`Lift/LLVM/data/shuffler/src/shuffler.zig`):", "```zig", p.zig, "```",
    ""] ++
    (if p.records.isEmpty then [] else
      [ "## The records of the function (Zig)",
        "The function reads these records by pointer. They are `extern struct`: the fields are in order, each at the next offset",
        "that its size and alignment allow (a pointer or a `usize` is 8 bytes at an offset of a multiple of 8, a `bool` is 1 byte).",
        "Put each field that the code reads at its offset from the address of the record.", "```zig"] ++
      p.records ++ ["```", ""]) ++
    (if p.recordLayouts.isEmpty then [] else
      ["## Compiler record layouts (`Lift/LLVM/data/shuffler/types.json`)",
       "Offsets and sizes are in bytes from each record base. A pointer field contains the base address of its target record.",
       "```text", p.recordLayouts, "```", ""]) ++
  [
    s!"## L3: `{c.model.const}` (`{c.model.file}`)", "```lean", c.model.text, "```",
    "",
    "## The names in scope",
    s!"The statement is in `namespace {c.module}`, with these `open` lines (the template has them):", "```lean"] ++
    scopeOpens c ++
    [ "```",
    "A short name in a hole means the constant that these lines give; the binders of the template are fully qualified. Use",
    "the fully qualified names of the types below when a short name is not one of these.",
    "",
    p.types.render level,
    "## The shared encoding (`Lift/Shuffler/Internal/Proposed/Layout.lean`)", "```lean", p.layout, "```",
    "",
    "## The template", "```lean", tmpl, "```",
    "" ] ++
  ((if level ≥ 4 then [] else p.examples).flatMap fun (n, t) => [s!"## Example: the moved statement `{n}` (another template, the same form)", "```lean", t, "```", ""]) ++
  (if p.rejected.isEmpty then [] else
    ["## Rejected proposals (do not give them again)"] ++
    p.rejected.flatMap fun (r, e) => ["```", (holesPart r).trimAscii.toString, "```", s!"Error: {e}", ""]))

/-- The prompt: the most detailed level (0 to 4) whose text has at most `promptLimit` bytes, else level 4. A pure function
of its input. -/
def prompt (p : PromptIn) : String :=
  let texts := [0, 1, 2, 3].map (promptAt p)
  (texts.find? (·.utf8ByteSize ≤ promptLimit)).getD (promptAt p 4)

/-! ## The filters -/

/-- The filters, in order. -/
inductive Stage where
  | parse | elaborate | shape | room | refute
  deriving BEq, Repr

def Stage.name : Stage → String
  | .parse => "parse" | .elaborate => "elaborate" | .shape => "stmt_shape" | .room => "checkRoom" | .refute => "refute"

/-- The verdict of the refuter. -/
inductive Verdict where
  | pass (checked skipped : Nat)
  | real (index : Nat) (why : String)
  | unknown (why : String)
  deriving BEq, Repr

def Verdict.text : Verdict → String
  | .pass c s => s!"pass ({c} samples in the contract, {s} skipped)"
  | .real i w => s!"refuted at sample {i}: {w}"
  | .unknown w => s!"unknown: {w}"

/-- The verdict line: pass with counts, a real counterexample with its index, or unknown with counts and a reason. -/
def parseVerdict (line : String) : Option Verdict :=
  match line.splitOn " " with
  | ["REFUTE", "pass", c, s] => do pure (.pass (← c.toNat?) (← s.toNat?))
  | "REFUTE" :: "real" :: i :: why => do pure (.real (← i.toNat?) (" ".intercalate why))
  | "REFUTE" :: "unknown" :: c :: s :: why => do
    let c ← c.toNat?
    let s ← s.toNat?
    if why.isEmpty then none else pure (.unknown s!"{c} checked, {s} skipped: {" ".intercalate why}")
  | _ => none

/-- The result of the filters on one reply: the stages passed, and the error of the first stage that fails (none: all
passed). -/
structure Checked where
  passed : List Stage
  failure : Option (Stage × String)
  holes : Option Holes
  verdict : Option Verdict

/-- The info lines and the error messages of a Lean run of the text `text` as the file `dir/name`. -/
def runLean (dir : System.FilePath) (name text : String) (limitMs : Nat := 600000) : IO (List String × List String) := do
  let path := dir / name
  IO.FS.writeFile path text
  let r ← NxLift.Proc.runLimited "lake" #["env", "lean", "--json", path.toString] none limitMs
  let ms := NxLift.parseJsonMessages r.output
  let infos := ms.toList.filter (·.severity == NxLift.Severity.info) |>.flatMap fun m => m.text.splitOn "\n"
  let errs := ms.toList.filter (·.severity == NxLift.Severity.error) |>.map fun m => s!"{m.line}: {m.text}"
  let errs := match r.ending with
    | .timedOut _ => "the run timed out" :: errs
    | .exited _ => errs
  pure (infos, errs)

/-- A wrapper of each Lean run of the checks: the identity, or a limit of the Lean runs at the same time. -/
abbrev Gate := IO (List String × List String) → IO (List String × List String)

/-- The first lines of an error, on one line. -/
def oneLine (s : String) (n : Nat := 600) : String := ((" ".intercalate (s.splitOn "\n")).take n).toString

/-- The filters on a reply, in order; each stage runs only after the stages before it pass. `samples` and `seed` set the
refuter. Each Lean run goes through `gate` (the runner limits there the Lean runs at the same time). -/
def check (dir : System.FilePath) (c : Ctx) (reply : String) (samples seed : Nat) (gate : Gate := id) :
    IO Checked := do
  match parseHoles reply with
  | .error e => pure ⟨[], some (.parse, e), none, none⟩
  | .ok h =>
    if let .error e := validateInputs c h then return ⟨[], some (.parse, e), some h, none⟩
    unless supportedArgs c.target.sym.args do
      return ⟨[.parse], some (.shape, "unsupported ABI: at most six register arguments, or six registers and two 64-bit stack arguments"), some h, none⟩
    let (infos, errs) ← gate (runLean dir s!"{c.name}Shape.lean" (shapeText c h))
    if let some e := errs.head? then return ⟨[.parse], some (.elaborate, oneLine e), some h, none⟩
    let shapes := infos.filterMap fun t => (Json.parse t >>= Shape.parse).toOption
    let some sh := shapes.head? | return ⟨[.parse, .elaborate], some (.shape, "#stmt_shape gave no shape"), some h, none⟩
    unless sh.args.map (·.width) == c.target.sym.args.take 6 do
      return ⟨[.parse, .elaborate], some (.shape, "argument widths or count differ from the ABI signature"), some h, none⟩
    if let .error e := checkRoom (fnOf c.target.label) sh then
      return ⟨[.parse, .elaborate, .shape], some (.room, e), some h, none⟩
    let (rinfos, rerrs) ← gate (runLean dir s!"{c.name}Refute.lean" (refuteText c h samples seed))
    let v := match rerrs.head?, (rinfos.filterMap parseVerdict).head? with
      | some e, _ => Verdict.unknown s!"the refute file does not elaborate: {oneLine e 300}"
      | none, some v => v
      | none, none => Verdict.unknown "the refute run gave no verdict"
    match v with
    | .real .. => pure ⟨[.parse, .elaborate, .shape, .room], some (.refute, v.text), some h, some v⟩
    | _ => pure ⟨[.parse, .elaborate, .shape, .room, .refute], none, some h, some v⟩

/-! ## The ask loop -/

/-- The most asks for one target (the rule of the user): after `maxAsks` refused replies, the target is open for the final
rung. -/
def maxAsks : Nat := 5

/-- How the asks of a target end. -/
inductive Fate where
  /-- A reply passes the filters: the statement module. -/
  | accepted (module : String)
  /-- `maxAsks` replies are refused: the error of the last one. The final rung takes the target. -/
  | openFinal (error : String)
  /-- The asker gave no reply (no stored reply, a refused or failed call): a later run asks again. -/
  | stopped (why : String)

def Fate.status : Fate → String
  | .accepted _ => "accepted" | .openFinal _ => "open for the final rung" | .stopped _ => "stopped"

/-- The outcome of a target: how its asks end, the replies with their checks, and the prompts of the asks. -/
structure Outcome where
  ctx : Ctx
  fate : Fate
  tries : List (String × Checked)
  prompts : List String

def Outcome.asks (o : Outcome) : Nat := o.prompts.length

def Outcome.module (o : Outcome) : Option String := match o.fate with
  | .accepted m => some m
  | _ => none

/-- The ledger line of an outcome: the label, the status, the source (proposer, or none), the stages passed by the last
reply, the error, the verdict, the number of asks and of replies, and the cost `usd`. -/
def Outcome.ledger (o : Outcome) (usd : Json) : String :=
  let last := o.tries.getLast?
  let passed := (last.map fun (_, k) => k.passed.map (·.name)).getD []
  let error := match o.fate, last.bind (·.2.failure) with
    | .stopped why, none => Json.str why
    | _, some (s, e) => Json.str s!"{s.name}: {e}"
    | _, none => Json.null
  Json.compress <| Json.mkObj
    [("label", o.ctx.target.label), ("statement", o.ctx.module), ("status", o.fate.status),
     ("source", if o.module.isSome then "proposer" else "none"),
     ("filters", Json.arr (passed.map Json.str).toArray),
     ("error", error),
     ("verdict", match last.bind (·.2.verdict) with | some v => Json.str v.text | none => Json.null),
     ("asks", o.asks), ("replies", o.tries.length), ("usd", usd)]

/-- The asks of one target: the prompt, the reply of the asker, the filters; on a refusal, the prompt again with each
rejected reply and its error, for at most `maxAsks` asks. -/
def propose (asker : Skel.Asker) (dir : System.FilePath) (p : PromptIn) (samples seed : Nat) (gate : Gate := id) :
    IO Outcome := do
  let rec go (k : Nat) (p : PromptIn) (tries : List (String × Checked)) (prompts : List String) : IO Outcome := do
    let pr := prompt p
    let (reply?, _) ← asker pr
    let prompts := prompts ++ [pr]
    match reply? with
    | none => pure ⟨p.ctx, .stopped "no reply", tries, prompts⟩
    | some reply =>
      let k' ← check dir p.ctx reply samples seed gate
      let tries := tries ++ [(reply, k')]
      match k'.failure, k'.holes with
      | none, some h => pure ⟨p.ctx, .accepted (fill p.ctx h "proposer"), tries, prompts⟩
      | some (s, e), _ =>
        match k with
        | 0 => pure ⟨p.ctx, .openFinal s!"{s.name}: {e}", tries, prompts⟩
        | k + 1 => go k { p with rejected := p.rejected ++ [(reply, s!"{s.name}: {e}")] } tries prompts
      | none, none => pure ⟨p.ctx, .stopped "a reply with no holes passed", tries, prompts⟩
  go (maxAsks - 1) p [] []

/-- `f` on each element of `xs`, at most `n` at the same time (each on a thread of its own), with the results in the order
of `xs`. An error of a job is the error of the pool. -/
def pool {α β : Type} (n : Nat) (xs : List α) (f : α → IO β) : IO (List β) := do
  let queue ← IO.mkRef xs.zipIdx
  let out ← IO.mkRef (#[] : Array (β × Nat))
  let rec work : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
      match ← queue.modifyGet fun q => match q with | [] => (none, []) | x :: rest => (some x, rest) with
      | none => pure ()
      | some (x, i) =>
        let y ← f x
        out.modify (·.push (y, i))
        work fuel
  let tasks ← (List.range (max n 1)).mapM fun _ => IO.asTask (work xs.length) .dedicated
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e
  return ((← out.get).qsort (·.2 < ·.2)).toList.map (·.1)

/-! ## The inputs from the files -/

/-- The two moved statements of the examples. -/
def exampleFiles : List (String × String) :=
  [("IsRetainedStatement", "Lift/Shuffler/Internal/IsRetainedStatement.lean"),
   ("PopStatement", "Lift/Shuffler/Internal/PopStatement.lean")]

/-- The steps of the walk of the type context. -/
def contextDepth : Nat := 6

/-- The prompt input of each target, or the reason why a target has none (no model function, no Zig source, no signature,
no type context). The type contexts come from one environment of the imports of all the statements. -/
def promptInputs : IO (List (Target × Except String PromptIn)) := do
  let zig ← IO.FS.readFile "Lift/LLVM/data/shuffler/src/shuffler.zig"
  let types ← IO.ofExcept (Json.parse (← IO.FS.readFile "Lift/LLVM/data/shuffler/types.json"))
  let layout ← IO.FS.readFile "Lift/Shuffler/Internal/Proposed/Layout.lean"
  let examples ← exampleFiles.mapM fun (n, f) => do pure (n, ← IO.FS.readFile f)
  let srcs ← targets.mapM fun t => (do
    let some m ← findModel t.label | pure (t, .error s!"no model function {shortOf t.label} or {fnConstOf t.label}")
    let some z := zigSource zig t.label | pure (t, .error "no Zig source")
    let some s := signature types t.label | pure (t, .error "no signature in types.json")
    pure (t, .ok (m, z, s)) : IO (Target × Except String (ModelSrc × String × String)))
  let ok := srcs.filterMap fun (_, r) => r.toOption.map fun (m, _) => (m.const, importsFor m.module)
  let tcs ← IO.ofExcept (← typeCtxs ok contextDepth)
  let byModel := (ok.map (·.1)).zip tcs
  pure <| srcs.map fun (t, r) => match r with
    | .error e => (t, .error e)
    | .ok (m, z, s) => match byModel.lookup m.const with
      | none => (t, .error s!"no type context of {m.const}")
      | some tc =>
        (t, .ok { ctx := ⟨t, { m with params := tc.params, ret := tc.ret }⟩, zig := z, records := recordDefs zig z,
                  recordLayouts := (recordLayouts types t.label).getD "", signature := s, layout, examples,
                  types := tc })

end Skel.IntQ

namespace Skel.IntQ

open Lean (Json)

/-- An asker that gives the replies `rs` in order, one for each ask, then no reply: the fake asker of the stored replies. -/
def seqAsker (rs : List String) : IO Skel.Asker := do
  let r ← IO.mkRef rs
  pure fun _ => do
    match ← r.get with
    | x :: xs => r.set xs; pure (some x, 0)
    | [] => pure (none, 0)

/-- The stored replies of a target in `dir`: `<N>.reply`, then `<N>.retry` (the reply to the retry prompt), when they exist. -/
def storedReplies (dir : System.FilePath) (t : Target) : IO (List String) := do
  let n := stmtName t.label
  let files := [dir / s!"{n}.reply", dir / s!"{n}.retry"]
  files.filterMapM fun f => do if ← f.pathExists then pure (some (← IO.FS.readFile f)) else pure none

/-- The ledger line of a target that has no reply. -/
def noReplyLedger (t : Target) (why : String) : String :=
  Json.compress <| Json.mkObj
    [("label", t.label), ("statement", s!"Lift.Shuffler.Internal.Proposed.{stmtName t.label}Statement"), ("status", "stopped"),
     ("source", "none"), ("filters", Json.arr #[]), ("error", why), ("verdict", Json.null), ("asks", 0), ("replies", 0),
     ("usd", 0)]

end Skel.IntQ
