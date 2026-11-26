import Lean

/-! Pure functions on the text of a Lean source: the text of one declaration, the split of a declaration at its
first `:=`, and the squash of whitespace. Lean core only. -/

/-- Whether `c` can continue a Lean identifier. -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '!' || c == '?'

/-- Whether `line` starts with `word`, and the word ends there: the next character is not part of an identifier. -/
private def startsWithWord (line word : String) : Bool :=
  line.startsWith word &&
    match line.toList.drop word.length with
    | [] => true
    | c :: _ => !isIdentChar c

/-- Whether `s` has only whitespace. -/
private def isBlank (s : String) : Bool :=
  s.toList.all Char.isWhitespace

/-- `s` without the whitespace at both ends. -/
private def trimWs (s : String) : String :=
  let noLead := s.toList.dropWhile Char.isWhitespace
  String.ofList (noLead.reverse.dropWhile Char.isWhitespace).reverse

private def declKeywords : List String := ["def", "theorem", "structure", "inductive", "abbrev"]

/-- The words that start the line after a declaration: its keywords, a doc comment, `end` and `namespace`. -/
private def boundaryWords : List String := declKeywords ++ ["/-", "end", "namespace"]

/-- The text of the declaration `name`: from its line to the line before the next boundary line, without the
blank lines at its end. `none` when no line starts a declaration of that name. -/
def declText (src name : String) : Option String :=
  let lines := src.splitOn "\n"
  let fromDecl := lines.dropWhile fun l =>
    !declKeywords.any fun k => startsWithWord l s!"{k} {name}"
  match fromDecl with
  | [] => none
  | first :: rest =>
    let body := first :: rest.takeWhile fun l => !boundaryWords.any fun w => startsWithWord l w
    some ("\n".intercalate (body.reverse.dropWhile isBlank).reverse)

/-- The header and the proof of a declaration: the text before its first `:=`, and the text after it.
Both are trimmed. `none` when there is no `:=`. -/
def splitDecl (d : String) : Option (String × String) :=
  match d.splitOn ":=" with
  | header :: proof :: more => some (trimWs header, trimWs (":=".intercalate (proof :: more)))
  | _ => none

/-- One step of `squash`: the output so far, and whether the last character was whitespace. -/
private def squashStep (acc : String × Bool) (c : Char) : String × Bool :=
  let (out, inWs) := acc
  if c.isWhitespace then (if inWs then (out, true) else (out.push ' ', true))
  else (out.push c, false)

/-- Each run of whitespace becomes one space. -/
def squash (s : String) : String :=
  (s.foldl squashStep ("", false)).1


/-! Lexical boundaries shared by source import and proof-scope rendering. -/

namespace Skel.Source

/-- A lexical token with character offsets. Strings and comments remain whole, so a header cannot match inside them. -/
structure SourceToken where
  text : String
  start : Nat
  stop : Nat
  column : Nat
  error : Option String := none
  deriving Repr, Inhabited

def wordChar (c : Char) : Bool := Lean.isIdRest c

private partial def quoted (acc : List Char) : List Char → List Char × List Char × Option String
  | [] => (acc.reverse, [], some "a string literal is not closed")
  | '\\' :: c :: cs => quoted (c :: '\\' :: acc) cs
  | '"' :: cs => (('"' :: acc).reverse, cs, none)
  | c :: cs => quoted (c :: acc) cs

private partial def blockComment (depth : Nat) (acc : List Char) : List Char → List Char × List Char × Option String
  | [] => (acc.reverse, [], some "a block comment is not closed")
  | '/' :: '-' :: cs => blockComment (depth + 1) ('-' :: '/' :: acc) cs
  | '-' :: '/' :: cs =>
    if depth == 1 then (('/' :: '-' :: acc).reverse, cs, none)
    else blockComment (depth - 1) ('/' :: '-' :: acc) cs
  | c :: cs => blockComment depth (c :: acc) cs

private partial def escapedIdent (acc : List Char) : List Char → List Char × List Char × Option String
  | [] => (acc.reverse, [], some "an escaped identifier is not closed")
  | '»' :: cs => (('»' :: acc).reverse, cs, none)
  | c :: cs => escapedIdent (c :: acc) cs

/-- A Char contains one character or one escaped character. Identifier suffix apostrophes stay in word tokens. -/
private def charLiteral (cs : List Char) : List Char × List Char × Option String :=
  match cs with
  | '\\' :: escape :: rest =>
    let n := if escape == 'x' then 2 else if escape == 'u' then 4 else 0
    match rest.drop n with
    | '\'' :: more => ('\'' :: '\\' :: escape :: rest.take n ++ ['\''], more, none)
    | _ => (['\''], cs, some "a character literal is not supported")
  | value :: '\'' :: rest => (['\'', value, '\''], rest, none)
  | _ => (['\''], cs, some "a character literal is not supported")

private partial def sourceTokensAt (offset column : Nat) : List Char → List SourceToken
  | [] => []
  | c :: cs =>
    if c.isWhitespace then sourceTokensAt (offset + 1) (if c == '\n' then 0 else column + 1) cs
    else
      let (chars, rest, error) :=
        if c == '"' then quoted ['"'] cs
        else if c == ']' && cs.head? == some '\'' then ([']', '\''], cs.tail!, none)
        else if c == '\'' then charLiteral cs
        else if c == '«' then escapedIdent ['«'] cs
        else if c == 'r' && (cs.dropWhile (· == '#')).head? == some '"' then
          let (hashes, rest) := cs.span (· == '#')
          ('r' :: hashes ++ ['"'], rest.tail!, some "raw string literals are not supported in recovered proofs")
        else if c == '/' && cs.head? == some '-' then blockComment 1 ['-', '/'] cs.tail!
        else if c == '-' && cs.head? == some '-' then
          let (a, b) := cs.span (· != '\n')
          (c :: a, b, none)
        else if c.isDigit then
          let (a, b) := cs.span fun c => c.isAlphanum || c == '_'
          let chars := c :: a
          let numeral := String.ofList chars
          let digits (p : Char → Bool) (s : String) := !s.isEmpty && s.toList.all fun c => c == '_' || p c
          let valid := digits Char.isDigit numeral ||
            (numeral.startsWith "0x" && digits (fun c => c.isDigit || "abcdefABCDEF".contains c) (numeral.drop 2).toString) ||
            (numeral.startsWith "0b" && digits (fun c => c == '0' || c == '1') (numeral.drop 2).toString) ||
            (numeral.startsWith "0o" && digits (fun c => "01234567".contains c) (numeral.drop 2).toString)
          (chars, b, if valid then none else some "a numeric literal boundary is not supported")
        else if wordChar c then
          let (a, b) := cs.span wordChar
          (c :: a, b, none)
        else ([c], cs, none)
      let column' := chars.foldl (fun n c => if c == '\n' then 0 else n + 1) column
      { text := String.ofList chars, start := offset, stop := offset + chars.length, column, error } ::
        sourceTokensAt (offset + chars.length) column' rest

def sourceTokens (offset : Nat) (chars : List Char) : List SourceToken := sourceTokensAt offset 0 chars

def isComment (t : SourceToken) : Bool := t.text.startsWith "/-" || t.text.startsWith "--"

def codeTokens (text : String) : List SourceToken :=
  (sourceTokens 0 text.toList).filter fun t => !isComment t && !t.text.startsWith "\"" && !t.text.startsWith "'"

/-- The names introduced by helper declarations, relative to their enclosing proof scope.
Comments and string contents are not declarations. Namespaces remain part of each name. -/
def declarationNames (text : String) : List String := Id.run do
  let rec ident (tokens : List SourceToken) : String × List SourceToken :=
    match tokens with
    | t :: dot :: rest =>
      if dot.text == "." then
        let (tail, remaining) := ident rest
        (t.text ++ "." ++ tail, remaining)
      else (t.text, dot :: rest)
    | [t] => (t.text, [])
    | [] => ("", [])
  let rec scan (fuel : Nat) (tokens : List SourceToken) (scope : List (Option String)) (names : List String) : List String :=
    match fuel, tokens with
    | 0, _ | _, [] => names.reverse
    | fuel + 1, t :: rest =>
      if t.text == "namespace" then
        let (name, rest) := ident rest
        scan fuel rest (some name :: scope) names
      else if t.text == "section" then scan fuel rest (none :: scope) names
      else if t.text == "end" then scan fuel rest scope.tail! names
      else if ["theorem", "lemma", "def", "abbrev", "opaque", "structure", "class", "inductive"].contains t.text then
        let (name, rest) := ident rest
        scan fuel rest scope ((".".intercalate (scope.reverse.filterMap id ++ [name])) :: names)
      else scan fuel rest scope names
  let tokens := codeTokens text
  return scan tokens.length tokens [] []

/-- Relocate fully qualified references to moved helper declarations. Other code and literal text stay fixed. -/
def relocateQualifiedHelpers (text original scope : String) (helpers : List String) : String :=
  let joined (a b : String) := if a.isEmpty then b else a ++ "." ++ b
  let names := helpers.map (joined original)
  let rec path (name : String) (stop : Nat) : List SourceToken → String × Nat × List SourceToken
    | dot :: next :: rest =>
      if dot.text == "." && dot.start == stop && next.start == dot.stop &&
          (next.text.toList.head?.any wordChar || next.text.startsWith "«") then
        path (name ++ "." ++ next.text) next.stop rest
      else (name, stop, dot :: next :: rest)
    | rest => (name, stop, rest)
  let rec go : Nat → List SourceToken → Nat → String → String
    | 0, _, prior, acc | _, [], prior, acc => acc ++ (text.drop prior).toString
    | fuel + 1, token :: rest, prior, acc =>
      let (name, stop, remaining) := path token.text token.stop rest
      let rooted := name.startsWith "_root_."
      let name := if rooted then (name.drop 7).toString else name
      let inOriginal := if original.isEmpty then rooted else name.startsWith (original ++ ".")
      if inOriginal && names.any (fun h => name == h || name.startsWith (h ++ ".") || h.startsWith (name ++ ".")) then
        let relative := if original.isEmpty then name else (name.drop (original.length + 1)).toString
        let moved := (if rooted then "_root_." else "") ++ joined (joined original scope) relative
        go fuel remaining stop (acc ++ ((text.drop prior).take (token.start - prior)).toString ++ moved)
      else go fuel remaining prior acc
  let tokens := codeTokens text
  go tokens.length tokens 0 ""

end Skel.Source
