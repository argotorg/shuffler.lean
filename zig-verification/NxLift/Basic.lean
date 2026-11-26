import Lean.Data.Json

/-! Names and numbers of the driver, parsed once at the boundary.

An `Ident` is a Lean identifier that is not a keyword, a `ModName` is a dotted module name, a `Symbol` is the
name of an assembly function, an `NEString` is a text that is not empty, and a `Pos` is a number above 0.
Each has a private constructor: a value of the type is a valid one, and the code that has it does not check it
again. -/

namespace NxLift

/-- The characters that Python's `str.isspace` accepts, as far as generated text has them. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13) || (0x1c ≤ c.toNat && c.toNat ≤ 0x1f) || c.toNat == 0x85 ||
    c.toNat == 0xa0 || c.toNat == 0x1680 || (0x2000 ≤ c.toNat && c.toNat ≤ 0x200a) || c.toNat == 0x2028 ||
    c.toNat == 0x2029 || c.toNat == 0x202f || c.toNat == 0x205f || c.toNat == 0x3000

/-- A character of a word (Python's `\w`, as far as Lean text has them): a letter, a digit, `_`, a Greek letter, a
letter-like symbol, a subscript. -/
def isWord (c : Char) : Bool :=
  c.isAlphanum || c == '_' || (127 < c.toNat && (Lean.isLetterLike c || Lean.isSubScriptAlnum c ||
    (0xc0 ≤ c.toNat && c.toNat ≤ 0x24f && c.toNat != 0xd7 && c.toNat != 0xf7)))

/-- A character that starts an identifier: a word character that is not a digit. -/
def isWordStart (c : Char) : Bool := isWord c && !c.isDigit

def stripRight (s : String) : String := String.ofList (s.toList.reverse.dropWhile isSpace).reverse

def stripLeft (s : String) : String := String.ofList (s.toList.dropWhile isSpace)

/-- Python's `str.strip()`. -/
def strip (s : String) : String := stripLeft (stripRight s)

/-- Python's `repr` of a string, for the error texts that quote one. -/
def pyRepr (s : String) : String :=
  let body := s.toList.foldl (fun acc c =>
    acc ++ (if c == '\\' then "\\\\" else if c == '\'' then "\\'" else if c == '\n' then "\\n"
      else if c == '\t' then "\\t" else if c == '\r' then "\\r" else c.toString)) ""
  s!"'{body}'"

/-- The number of lines of a text as Python's `str.count("\n")`. -/
def countNewlines (s : String) : Nat := s.foldl (fun n c => if c == '\n' then n + 1 else n) 0

/-- The words that cannot be a name of a function in the generated Lean text. -/
def keywords : List String :=
  ("abbrev at attribute axiom by calc catch class decreasing_by def deriving do else end example exists " ++
   "export extends finally for forall from fun have if import in include inductive infix initialize instance let " ++
   "local macro match meta module mutual namespace nofun nomatch noncomputable notation omit open opaque partial " ++
   "prelude private protected public return section set_option show structure syntax termination_by then theorem " ++
   "this try Type Prop Sort universe unless unsafe variable where with elab mod").splitOn " "

private def plainIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => (c.isAlpha || c == '_') && rest.all fun c => c.isAlphanum || c == '_'

/-- A Lean identifier (ASCII letters, digits and `_`) that is not a keyword. -/
structure Ident where
  private mk ::
  val : String
  deriving BEq, Hashable, Repr, Ord, Inhabited

namespace Ident

def parse (s : String) : Except String Ident :=
  if plainIdent s && !keywords.contains s then .ok ⟨s⟩ else .error s!"{pyRepr s} is not a usable name"

/-- An identifier for a constant of the program. The text is known to be one: a test runs each use. -/
def lit (s : String) : Ident :=
  match parse s with
  | .ok i => i
  | .error e => panic! e

/-- The identifier `p ++ i`, for a prefix `p` of letters, digits and `_` (`p1_`). -/
def prefixed (p : String) (i : Ident) : Ident := lit (p ++ i.val)

instance : ToString Ident := ⟨Ident.val⟩

end Ident

/-- A module name: identifiers (keywords are allowed) joined by `.`. -/
structure ModName where
  private mk ::
  val : String
  deriving BEq, Hashable, Repr, Ord, Inhabited

namespace ModName

def parse (s : String) : Except String ModName :=
  if (s.splitOn ".").all plainIdent then .ok ⟨s⟩ else .error s!"{pyRepr s} is not a module name"

def lit (s : String) : ModName :=
  match parse s with
  | .ok m => m
  | .error e => panic! e

def child (m : ModName) (i : Ident) : ModName := ⟨m.val ++ "." ++ i.val⟩

/-- The module of a function: `Lifted.Code.f` is `(lit "Lifted.Code").child f`. -/
def sub (root : String) (i : Ident) : ModName := (lit root).child i

/-- The file of the module, relative to the root of its workspace. -/
def file (m : ModName) : String := m.val.replace "." "/" ++ ".lean"

instance : ToString ModName := ⟨ModName.val⟩

end ModName

/-- The name of a function in the assembly: not empty, no white space. -/
structure Symbol where
  private mk ::
  val : String
  deriving BEq, Hashable, Repr, Ord, Inhabited

namespace Symbol

def parse (s : String) : Except String Symbol :=
  if s.isEmpty || s.any isSpace then .error s!"{pyRepr s} is not a symbol" else .ok ⟨s⟩

instance : ToString Symbol := ⟨Symbol.val⟩

end Symbol

/-- A text that is not empty: the error of a failure, the reason of a step that did not run. -/
structure NEString where
  val : String
  ne : val ≠ ""

instance : Inhabited NEString := ⟨⟨"no text", by decide⟩⟩

namespace NEString

def parse (s : String) : Option NEString := if h : s = "" then none else some ⟨s, h⟩

/-- The text, or a placeholder text when it is empty. -/
def ofText (s : String) : NEString := if h : s = "" then ⟨"no text", by decide⟩ else ⟨s, h⟩

instance : ToString NEString := ⟨NEString.val⟩
instance : BEq NEString := ⟨fun a b => a.val == b.val⟩
instance : Repr NEString := ⟨fun s _ => repr s.val⟩

end NEString

/-- A number above 0: the jobs of a run, the milliseconds of a time limit. -/
structure Pos where
  val : Nat
  pos : 0 < val

namespace Pos

def parse (n : Nat) : Option Pos := if h : 0 < n then some ⟨n, h⟩ else none

def one : Pos := ⟨1, by decide⟩

instance : Repr Pos := ⟨fun p _ => repr p.val⟩
instance : BEq Pos := ⟨fun a b => a.val == b.val⟩

end Pos

end NxLift
