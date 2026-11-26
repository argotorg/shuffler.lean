import Skel.Types
import Skel.ProofScope
import Skel.Source

/-! Pure functions that make the Lean text of a check file (`docs/one-way-lift-skeleton-plan-20261118.md`, section 2.2)
and of a loop proof (section 2.3). -/

namespace Skel

/-- The header of a check file: the modules to import, the namespace of the file, and the names to open. -/
structure Header where
  (imports : List String) (namespace_ : String) (opens : List String)
  deriving Repr

/-- Helper scopes need the alias command. Files without such scopes keep their imports. -/
def proofScopeImports (imports : List String) (text : String) : List String :=
  if (text.splitOn "skel_proof_aliases ").length > 1 then (imports ++ ["Skel.ProofScope"]).eraseDups
  else imports

/-- Add the helper-scope support import to a reconstructed saved file when required. -/
def withProofScopeImport (text : String) : String :=
  if (proofScopeImports [] text).isEmpty || (text.splitOn "import Skel.ProofScope\n").length > 1 then text
  else "import Skel.ProofScope\n" ++ text

/-- The line between the helper declarations of a proof text and its proof (`Proof.text`). -/
def helperSep : String := "\n-- skel: the theorem\n"

/-- A proof with helper declarations (lemmas and definitions) that go before the theorem. `helpers` is empty for a proof
with no helpers. -/
structure Proof where (helpers proof : String) deriving DecidableEq, Repr

/-- The proof text: the proof alone when there are no helpers, else the helpers, `helperSep` and the proof. -/
def Proof.text (p : Proof) : String := if p.helpers.isEmpty then p.proof else p.helpers ++ helperSep ++ p.proof

/-- The proof of a proof text: the text after the first `helperSep` is the proof, the text before it the helpers. A text
with no `helperSep` has no helpers. -/
def Proof.ofText (t : String) : Proof :=
  match t.splitOn helperSep with
  | h :: rest@(_ :: _) => { helpers := h, proof := helperSep.intercalate rest }
  | _ => { helpers := "", proof := t }

/-- The lines inside `namespace ns` and `end ns`; no namespace lines when `ns` is empty. -/
private def inNs (ns : String) (body : String) : String :=
  if ns.isEmpty then body else s!"namespace {ns}\n{body}\nend {ns}"

/-- Heartbeat limits take effect at command entry. Move bounded leading resource wrappers there. -/
private def commandResourceOptions (text : String) : String × String :=
  let rec stop : List Source.SourceToken → Nat → Nat
    | option :: name :: value :: scope :: rest, prior =>
      if option.text == "set_option" && scope.text == "in" &&
          (value.text.toNat?.any fun n => n > 0 &&
            (name.text == "maxRecDepth" || (name.text == "maxHeartbeats" && n ≤ 400000))) then
        stop rest scope.stop
      else prior
    | _, prior => prior
  let end_ := stop (Source.codeTokens text) 0
  if end_ == 0 then ("", text)
  else ((text.take end_).toString ++ "\n", (text.drop end_).toString.trimAscii.toString)

/-- The declaration `name : statement := proof`. A dotted name `A.B.c` is written as `theorem c` inside
`namespace A.B` and `end A.B`, so that the name of the declaration is `A.B.c`.

A proof text with helpers (`Proof.ofText`) puts the helpers and implementation in a namespace for this row.
The definition `name.skel_statement : Prop := statement` fixes the statement before the helpers. A theorem outside
their namespace exports the implementation at that fixed type. Different rows can use the same helper names.
A helper that changes the meaning of the statement makes the exported theorem fail to check. -/
def theoremText (name statement proof : String) : String :=
  let parts := name.splitOn "."
  let short := parts.getLast?.getD name
  let ns := ".".intercalate parts.dropLast
  let p := Proof.ofText proof
  let (options, term) := commandResourceOptions p.proof
  let decl := inNs ns s!"{options}theorem {short} : {statement} := {term}"
  if p.helpers.isEmpty then decl
  else
    let scope := s!"{name}.skel_proof"
    let declared := (Source.declarationNames p.helpers ++ [name]).eraseDups
    let exclusions := s!" excluding [{", ".intercalate declared}]"
    "\n".intercalate [inNs ns s!"def {short}.skel_statement : Prop := {statement}",
      inNs scope (s!"skel_proof_aliases {scope}{exclusions}\n" ++ p.helpers ++ "\n" ++ decl),
      inNs ns s!"theorem {short} : {short}.skel_statement := @{scope}.{name}"]

/-- The check file of an obligation (section 2.2). Each import is one line. `answers` are declarations, each already
rendered with `theoremText`, and they are written in the given order before the obligation. The file ends with
`#print axioms` for the obligation and a newline. -/
def checkFile (h : Header) (model : String) (answers : List String) (ob : Obligation) (proof : String) : String :=
  let opens := if h.opens.isEmpty then [] else [s!"open {" ".intercalate h.opens}"]
  let body := [theoremText ob.id.name ob.statement proof, s!"#print axioms {ob.id.name}"]
  let imports := proofScopeImports h.imports ("\n".intercalate (model :: answers ++ body))
  let lines := imports.map (fun m => s!"import {m}")
    ++ [s!"namespace {h.namespace_}"] ++ opens ++ [model] ++ answers ++ body ++ [s!"end {h.namespace_}"]
  "\n".intercalate lines ++ "\n"

/-- The bracket depth after the character `c`. -/
def depthAfter (depth : Nat) (c : Char) : Nat :=
  if "([{⟨⦃".contains c then depth + 1
  else if ")]}⟩⦄".contains c then depth - 1
  else depth

/-- The text before the first `sep` at bracket depth 0, and the text after it. `acc` is the text before `cs`, reversed. -/
def splitAtTop (sep : Char) (acc : List Char) (depth : Nat) : List Char → Option (String × String)
  | [] => none
  | c :: cs =>
    if c == sep && depth == 0 then some (String.ofList acc.reverse, String.ofList cs)
    else splitAtTop sep (c :: acc) (depthAfter depth c) cs

/-- The binder groups of a binder text, each with its opening bracket and its inside text. `depth` is the bracket depth,
`cur` the inside text so far (reversed) and `o` the opening bracket of the open group. -/
private def binderGroups : Nat → List Char → Char → List Char → List (Char × String)
  | _, _, _, [] => []
  | depth, cur, o, c :: cs =>
    if depth == 0 then
      if "([{⦃".contains c then binderGroups 1 [] c cs else binderGroups 0 [] o cs
    else
      let depth' := depthAfter depth c
      if depth' == 0 then (o, String.ofList cur.reverse) :: binderGroups 0 [] o cs
      else binderGroups depth' (c :: cur) o cs

/-- The names that the binders of a header bind, in order: the names before the colon of each group `(…)`, `{…}`,
`⦃…⦄`. An instance binder `[…]` and a group with no colon give `_`. -/
def binderNames (binders : String) : List String :=
  (binderGroups 0 [] ' ' binders.toList).flatMap fun (o, body) =>
    if o == '[' then ["_"]
    else
      match splitAtTop ':' [] 0 body.toList with
      | some (names, _) => (names.splitOn " ").filter (· ≠ "")
      | none => ["_"]

/-- The names that the leading `∀` of a statement binds, as `binderNames` reads them from the binders in front of the
first comma at bracket depth 0. A statement with no `∀`, or with a binder that has no bracket, gives none. -/
def introNames (statement : String) : List String :=
  if statement.startsWith "∀ " then
    match splitAtTop ',' [] 0 (statement.toList.drop 2) with
    | some (binders, _) => binderNames binders
    | none => []
  else []

/-- The conjunct that the skeleton puts before the invariant of a triple: the input of the state is the input `a` of the
statement. -/
def loopFrame : String := "x.input = a"

/-- The proof text of a loop row (section 2.3) from its statement and a triple: `intro` of the names that the `∀` of the
statement binds (no line when there are none), the lines `slots` (the names of the slot, G3-21a), `intros` for the
premises, `split_hyps` to unpack them, and one `lift_loop!` call with the invariant after `loopFrame`, the measure and the
result, each term in parentheses, and the names `unfolds` for its closing step (no list when there are none). -/
def loopProof (statement : String) (t : Triple) (slots : List String := []) (unfolds : List String := []) : String :=
  let intro := match introNames statement with
    | [] => []
    | ns => [s!"  intro {" ".intercalate ns}"]
  let names := if unfolds.isEmpty then "" else s!" [{", ".intercalate unfolds}]"
  "\n".intercalate (["by"] ++ intro ++ slots.map ("  " ++ ·) ++ ["  intros", "  split_hyps",
    s!"  lift_loop! (fun x => {loopFrame} ∧ ({t.inv})) (fun x => ({t.measure})) (fun x => ({t.result})){names}"])

end Skel
