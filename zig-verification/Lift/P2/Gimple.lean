/-
A typed AST of GCC GIMPLE (SSA form, after optimisation) and a parser for the text of the dump.

The AST (`Lift.P2.Gimple.Func`) is the interface: `#gimple2` (in `Lift.P2.Gimple2`) builds the model
from it. The text parser is one producer; a GCC plugin that prints the AST with `ToJson` is
another one (the types derive `FromJson`). The parser knows only the constructs of the tree
functions: SSA assignments and copies, loads and stores through `p->field`, `*p` and
`MEM[(T *)p + n B]`, `if (a == b)`, `goto`, `return` and PHIs. Memory versions (`.MEM_n`, vops),
debug binds and source locations are dropped. Any other line is an error that names the line.
-/
import Lean

open Lean Std.Internal.Parsec Std.Internal.Parsec.String

namespace Lift.P2.Gimple

/-- The type of a value: a pointer (or reference) of 64 bits, or an integer of `w` bits. -/
inductive Ty where
  | ptr
  | bits (w : Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

def Ty.width : Ty → Nat
  | .ptr => 64
  | .bits w => w

/-- The type of a declaration, from the text of the dump. -/
def Ty.ofString (s : String) : Except String Ty :=
  let s := ((s.splitOn "const ").foldl (· ++ ·) "").splitOn " const" |>.foldl (· ++ ·) "" |>.trimAscii.toString
  if s.endsWith "*" || s.endsWith "&" then .ok .ptr
  else match s with
    | "_Rb_tree_color" | "int" | "unsigned int" => .ok (.bits 32)
    | "long int" | "long unsigned int" | "size_t" | "long long int" => .ok (.bits 64)
    | "bool" | "char" | "unsigned char" => .ok (.bits 8)
    | _ => .error s!"unknown type '{s}'"

/-- A value: an SSA name (printed `base_N`, `base_N(D)` for the default definition, without the
`(D)`), the null pointer `0B`, or an integer constant. -/
inductive Atom where
  | var (name : String)
  | null
  | int (v : Int)
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A memory place: `p->field`, `*p`, or `MEM[(T *)p + off B]`. The `rec` of a field access is the record that `p` points to,
by its name in the `types` of the plugin JSON (`gcc-plugin/SCHEMA.md`): two records can have a field of the same name at
different offsets. The dump does not print the record, so the text parser leaves `rec` empty and `Func.qualify` fills it. -/
inductive Place where
  | field (base : Atom) (rec : String) (fld : String)
  | deref (p : Atom)
  | memref (base : Atom) (off : Int)
  /-- `MEM[base + off + index * stride]`: an element of an array (`p->a[i]`, `p[i]`); the index is a 64-bit integer (an index of
  another type is converted before), the stride is the size of an element in bytes. -/
  | indexed (base : Atom) (off : Int) (index : Atom) (stride : Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The binary operations on integers of one width (the shift count and the operands of the others have the type of the result, except
that the count of a shift has its own type). The operations are modular. A shift takes its count modulo the width, as the machine does.
`udiv sdiv urem srem` fault on a zero divisor, and `sdiv srem` on the most negative number divided by -1, as the machine does. -/
inductive BinOp where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  | shl
  /-- A right shift of an unsigned type. -/
  | lshr
  /-- A right shift of a signed type. -/
  | ashr
  | udiv
  | sdiv
  | urem
  | srem
  deriving DecidableEq, Repr, ToJson, FromJson

inductive UnOp where
  /-- `~a`. -/
  | not
  /-- `-a`. -/
  | neg
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A comparison: equal, not equal, and the orders of unsigned (`u`; also the pointers) and signed (`s`) integers. -/
inductive Cmp where
  | eq
  | ne
  | ult
  | ule
  | ugt
  | uge
  | slt
  | sle
  | sgt
  | sge
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Rhs where
  | atom (a : Atom)
  | load (p : Place)
  /-- `&p->field` or `&*p`: the address of a place. -/
  | addrOf (p : Place)
  /-- `a + b`, `a * b`, `a & b`, `a << b`, ... -/
  | bin (op : BinOp) (a b : Atom)
  /-- `-a`, `~a`. -/
  | un (op : UnOp) (a : Atom)
  /-- `(T) a`: the conversion to the type of the destination. A narrower destination keeps the low bits; a wider one extends by
  the sign of the type of `a` (`signed`; a pointer is unsigned). -/
  | cast (a : Atom) (signed : Bool)
  /-- The constructs below come from the LLVM front end (`Lift/LLVM`). `a op b` as a value: 1 if it holds, else 0, in the type of the destination (`icmp`, `a < b`). -/
  | cmp (a : Atom) (op : Cmp) (b : Atom)
  /-- `if a op b then x else y` (`select`, with the `icmp` of its condition). -/
  | sel (a : Atom) (op : Cmp) (b : Atom) (x y : Atom)
  /-- Zero extension, sign extension, truncation to the width of the destination. -/
  | zext (a : Atom)
  | sext (a : Atom)
  | trunc (a : Atom)
  /-- `base + idx * scale` (`getelementptr` with a variable index; the constant offsets are `bin add`). -/
  | lea (base idx : Atom) (scale : Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Stmt where
  | assign (dst : String) (rhs : Rhs)
  | store (dst : Place) (src : Atom)
  /-- A direct call `dst = callee (args);` (or without `dst`). -/
  | call (dst : Option String) (callee : String) (args : List Atom)
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Term where
  | goto (bb : Nat)
  | cond (a : Atom) (op : Cmp) (b : Atom) (thenBB elseBB : Nat)
  | ret (v : Option Atom)
  /-- `switch` of the LLVM front end: the first case with the value of `a` is taken, else `dflt`. -/
  | switch (a : Atom) (cases : List (Int × Nat)) (dflt : Nat)
  /-- `unreachable` of the LLVM front end: no step (a fault in the model). -/
  | unreachable
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The flags of an integer operation (`nuw`, `nsw`, `exact`). -/
structure IntFlags where
  nuw : Bool := false
  nsw : Bool := false
  exact : Bool := false
  deriving DecidableEq, Repr, ToJson, FromJson

/-- `dst = PHI <v1(bb1), v2(bb2)>`: the value `v` that comes from the predecessor `bb`. -/
structure Phi where
  dst : String
  args : List (Atom × Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

structure Block where
  id : Nat
  phis : List Phi
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr, ToJson, FromJson

structure Func where
  /-- The mangled symbol. -/
  sym : String
  /-- The qualified name, as printed. -/
  name : String
  /-- `none`: `void`. -/
  retTy : Option Ty
  /-- The parameters, in order, with their types. -/
  params : List (String × Ty)
  /-- The types of the local declarations (an SSA name `base_N` has the type of `base` or `base_N`). -/
  decls : List (String × Ty)
  blocks : List Block
  /-- The flags of the integer operations that have some (by the name of the destination); the model ignores them
  (the operations wrap), the abstraction steps read them. Only the LLVM front end sets it. -/
  flags : Option (List (String × IntFlags)) := none
  deriving Repr, ToJson, FromJson

/-! ### The record of a field access -/

/-- The place with the record of a field access that the text parser left empty: `recOf` gives the record of a field name. -/
def Place.qualify (recOf : String → Except String String) : Place → Except String Place
  | .field b "" f => return .field b (← recOf f) f
  | p => return p

def Rhs.qualify (recOf : String → Except String String) : Rhs → Except String Rhs
  | .load p => return .load (← p.qualify recOf)
  | .addrOf p => return .addrOf (← p.qualify recOf)
  | r => return r

def Stmt.qualify (recOf : String → Except String String) : Stmt → Except String Stmt
  | .assign d r => return .assign d (← r.qualify recOf)
  | .store p a => return .store (← p.qualify recOf) a
  | s => return s

/-- The function with the record of every field access: the dump names the field only, so `recOf` (a table of the fields of the
records of the program) gives the record. A name that two records have is an error. -/
def Func.qualify (recOf : String → Except String String) (f : Func) : Except String Func := do
  let blocks ← f.blocks.mapM fun b => return { b with stmts := ← b.stmts.mapM (·.qualify recOf) }
  return { f with blocks }

/-- The name of a record as a Lean identifier: the characters that are not letters, digits or `_` become `_`
(`std::_Rb_tree_node_base` is `std___Rb_tree_node_base`). Two records of a program must not have the same identifier. -/
def recIdent (r : String) : Name :=
  Name.mkSimple (r.map fun c => if c.isAlphanum || c == '_' then c else '_')

/-- The records of a file, in the order of the layout of P2 (`Lift.P2.Gen.layoutOfTypes`): the names of the types of kind `record` with a
name, once for each name, sorted. The index of a record in this list is its index in the layout. The input is the kind and the name of
each type of the plugin JSON. -/
def layoutNames (types : List (String × Option String)) : List String :=
  ((types.filterMap fun (k, n) => if k == "record" then n else none).eraseDups.toArray.qsort (· < ·)).toList

/-- The constant of the offset of a field in the model namespace of a function: `Fld.<record>.<field>`, or `Fld.<field>` for the model
of the dump, whose fields have no record. -/
def fldConst (r f : String) : String := if r.isEmpty then s!"Fld.{f}" else s!"Fld.{recIdent r}.{f}"

/-- A field of a record, from the `types` of the plugin file: the record (its `name`), the field, its offset and its size in bytes. -/
abbrev FieldFact := String × String × Nat × Nat

/-- The fields of the records and unions of the file, keyed by (record, field). A record has no `name` in the JSON when it is
anonymous: its fields are not listed. The `const` copy of a record has no fields. A field with two offsets or sizes in one
record, and two records whose identifiers (`recIdent`) are the same, are errors. -/
def jsonFields (doc : Json) : Except String (List FieldFact) := do
  let types ← (← doc.getObjVal? "types").getArr?
  let mut acc : List FieldFact := []
  for t in types do
    unless (t.getObjValAs? String "kind").toOption.any (fun k => k == "record" || k == "union") do continue
    let some name := (t.getObjValAs? String "name").toOption | continue
    let some fs := (t.getObjVal? "fields").toOption | continue
    for f in ← fs.getArr? do
      let fname ← f.getObjValAs? String "name"
      match (f.getObjValAs? Nat "offset").toOption, (f.getObjValAs? Nat "size").toOption with
      | some o, some s => acc := (name, fname, o, s) :: acc
      | _, _ => pure ()
  let all := acc.reverse.eraseDups
  for (r, f, _, _) in all do
    if (all.filter fun x => x.1 == r && x.2.1 == f).length > 1 then
      throw s!"the field {f} of the record {r} has several offsets or sizes: {all.filter fun x => x.1 == r && x.2.1 == f}"
  let recs := (all.map (·.1)).eraseDups
  for r in recs do
    if (recs.filter fun r' => recIdent r' == recIdent r).length > 1 then
      throw s!"the records {recs.filter fun r' => recIdent r' == recIdent r} have the same identifier {recIdent r}"
  return all

/-- The record of a field name, when one record of the program has it: for the AST of the text parser. -/
def recOfFacts (facts : List FieldFact) (f : String) : Except String String :=
  match (facts.filter fun x => x.2.1 == f).map (·.1) |>.eraseDups with
  | [r] => .ok r
  | [] => .error s!"no record has the field {f}"
  | rs => .error s!"the field {f} is in several records ({rs}): the dump does not say which"

/-! ### Reading the dump -/

/-- Removes the source locations `[file:line:col discrim n]` of a line of the dump. -/
def stripLoc (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let isLoc (inner : List Char) : Bool :=
    let t := String.ofList inner
    let t := match t.splitOn " discrim " with | [a, _] => a | _ => t
    match t.splitOn ":" with
    | _ :: _ :: _ =>
      let ps := t.splitOn ":"
      ps.length ≥ 3 && (ps.getLast!.all Char.isDigit) && ps.getLast!.length > 0 &&
        (ps.getD (ps.length - 2) "").all Char.isDigit && (ps.getD (ps.length - 2) "").length > 0
    | _ => false
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '[' then
      let mut j := i + 1
      let mut depth := 1
      while j < cs.size && depth > 0 do
        if cs[j]! == '[' then depth := depth + 1
        else if cs[j]! == ']' then depth := depth - 1
        j := j + 1
      let inner := (cs.extract (i + 1) (j - 1)).toList
      if depth == 0 && isLoc inner then
        i := j
        if i < cs.size && cs[i]! == ' ' then i := i + 1
        continue
    out := out.push cs[i]!
    i := i + 1
  return out

/-- The lines of the section of the function `sym` in the dump `path`. The dump is read line by
line from the header `;; Function ... (sym,` to the next header, so that a large dump is not
read as a whole. -/
def readSection (path : System.FilePath) (sym : String) : IO (Array String) := do
  let h ← IO.FS.Handle.mk path .read
  let mut out : Array String := #[]
  let mut inside := false
  let mut found := false
  repeat
    let l ← h.getLine
    if l.isEmpty then break
    let l := l.dropEndWhile (· == '\n') |>.toString
    if l.startsWith ";; Function " then
      if inside then break
      if (l.splitOn s!"({sym},").length > 1 then
        inside := true; found := true
        out := out.push l
      continue
    if inside then out := out.push l
  unless found do throw (IO.userError s!"function {sym} is not in {path}")
  return out

/-! ### Parsers of one line -/

abbrev P := Parser

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '.'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '$'

def ident : P String := do
  let c ← satisfy isIdStart
  let rest ← manyChars (satisfy isIdChar)
  return c.toString ++ rest

def nat : P Nat := do
  let ds ← many1Chars digit
  return ds.toNat!

def int : P Int := do
  let neg ← (do skipChar '-'; return true) <|> pure false
  let n ← nat
  return if neg then -(n : Int) else n

/-- An SSA name, with the optional `(D)`. -/
def atom : P Atom := do
  let c ← peek?
  match c with
  | some c =>
    if c.isDigit || c == '-' then
      let n ← int
      (do skipChar 'B'; if n == 0 then return Atom.null else fail "pointer constant that is not 0B")
        <|> pure (Atom.int n)
    else
      let n ← ident
      (do skipString "(D)") <|> pure ()
      return Atom.var n
  | none => fail "atom expected"

def place : P Place :=
  (do skipChar '*'; let a ← atom; return Place.deref a)
  <|> (do
    skipString "MEM[("
    let _ ← manyChars (satisfy fun c => c != ')')
    skipChar ')'
    let b ← atom
    let off ← (do skipString " + "; let n ← int; (do skipChar 'B') <|> pure (); return n)
              <|> (do skipString " - "; let n ← int; (do skipChar 'B') <|> pure (); return -n) <|> pure 0
    skipChar ']'
    return Place.memref b off)
  <|> (do
    let b ← attempt (do let b ← atom; skipString "->"; return b)
    let f ← ident
    return Place.field b "" f)

inductive Line where
  | phi (p : Phi)
  | stmt (s : Stmt)
  | cond (a : Atom) (op : Cmp) (b : Atom)
  | goto (bb : Nat)
  | else_
  | ret (v : Option Atom)
  | ignore
  deriving Repr

def cmp : P Cmp :=
  (do skipString "=="; return Cmp.eq) <|> (do skipString "!="; return Cmp.ne)

def phiArg : P (Atom × Nat) := do
  let a ← atom
  skipChar '('
  let n ← nat
  skipChar ')'
  return (a, n)

def sepBy1 {α : Type} (p : P α) (sep : P Unit) : P (List α) := do
  let a ← p
  let rest ← many (do sep; p)
  return a :: rest.toList

/-- The name of a function: `std::local_Rb_tree_increment`. -/
def calleeName : P String :=
  many1Chars (satisfy fun c => c.isAlphanum || c == '_' || c == ':' || c == '<' || c == '>' || c == '~' || c == '.')

def callRest : P (String × List Atom) := do
  let c ← calleeName
  ws; skipChar '('; ws
  let args ← (do let a ← sepBy1 (do ws; atom) (do skipChar ','; ws); return a) <|> pure []
  ws; skipChar ')'; skipChar ';'
  return (c, args)

def stmtLine : P Line :=
  (do let (c, args) ← attempt callRest; return .stmt (.call none c args)) <|> assignLine
where
  assignLine : P Line := do
  -- `lhs = rhs;`
  let lhs ← (do let p ← place; return Sum.inr p) <|> (do let a ← atom; return Sum.inl a)
  ws; skipChar '='; ws
  match lhs with
  | .inr p =>
    let v ← atom
    skipChar ';'
    return .stmt (.store p v)
  | .inl (.var d) =>
    (do let (c, args) ← attempt callRest; return .stmt (.call (some d) c args)) <|> (do
      let r ← (do skipChar '&'; let p ← place; return Rhs.addrOf p)
        <|> (do let p ← attempt place; return Rhs.load p)
        <|> (do
          let a ← atom
          (do ws; let op ← (do skipChar '+'; return BinOp.add) <|> (do skipChar '-'; return BinOp.sub)
              ws; let b ← atom; return Rhs.bin op a b) <|> pure (Rhs.atom a))
      skipChar ';'
      return .stmt (.assign d r))
  | .inl _ => fail "assignment to a constant"

def line : P Line := do
  ws
  let c ← peek?
  match c with
  | none => return .ignore
  | some '#' =>
    skipChar '#'; ws
    let c2 ← peek?
    if c2 == some '.' then
      -- memory versions: `.MEM_n = PHI <...>`, `.MEM_n = VDEF <...>`, `.MEM_n(D)`
      return .ignore
    else
      (do skipString "DEBUG"; return .ignore)
      <|> (do skipString "VUSE"; return .ignore)
      <|> (do
        let d ← ident
        ws; skipString "= PHI <"
        let args ← sepBy1 (do ws; phiArg) (do skipChar ','; ws)
        skipChar '>'
        return .phi { dst := d, args })
      <|> fail "unsupported '#' line"
  | some _ =>
    (do skipString "if ("
        let a ← atom; ws; let o ← cmp; ws; let b ← atom
        skipChar ')'
        return .cond a o b)
    <|> (do skipString "goto <bb "; let n ← nat; skipChar '>'; return .goto n)
    <|> (do skipString "else"; return .else_)
    <|> (do skipString "return"; ws
            let v ← (do let a ← atom; return some a) <|> pure none
            skipChar ';'; return .ret v)
    <|> stmtLine

/-- Parses a line (without the source locations); the rest of the line after the statement is
ignored (`; [70.00%]`). -/
def parseLine (s : String) : Except String Line :=
  match (line).run s with
  | .ok l => .ok l
  | .error e => .error s!"{e}"

/-! ### The function -/

/-- The parameters of a signature `ret name (t1 p1, t2 p2)`. -/
def splitParams (s : String) : List String := Id.run do
  let mut out := []; let mut cur := ""; let mut d := 0
  for c in s.toList do
    if c == '(' || c == '<' then d := d + 1
    if c == ')' || c == '>' then d := d - 1
    if c == ',' && d == 0 then out := out ++ [cur]; cur := ""
    else cur := cur.push c
  if !cur.trimAscii.isEmpty then out := out ++ [cur]
  return out

/-- `type name` of one declaration: the name is the last identifier. -/
def splitDecl (s : String) : Except String (String × String) := do
  let s := s.trimAscii.toString
  let cs := s.toList.reverse
  let name := String.ofList (cs.takeWhile isIdChar).reverse
  let ty := String.ofList (cs.dropWhile isIdChar).reverse
  if name.isEmpty then throw s!"no name in '{s}'"
  return (ty.trimAscii.toString, name)

structure BlockB where
  id : Nat
  phis : Array Phi := #[]
  stmts : Array Stmt := #[]
  term : Option Term := none
  pendingIf : Option (Atom × Cmp × Atom × Option Nat) := none
  succs : Array Nat := #[]

/-- Parses the section of one function (see `readSection`). `qname` is the qualified name of the
function (from the header line, or `""` to take it from the signature). -/
def parseFunc (sym : String) (qname0 : String) (lines0 : Array String) : Except String Func := do
  -- the header line `;; Function qname (sym, ...)` gives the qualified name
  let (qname, lines) :=
    match lines0[0]? with
    | some h =>
      if h.startsWith ";; Function " then
        (((h.drop 12).toString.splitOn s!" ({sym},").head!, lines0.extract 1 lines0.size)
      else (qname0, lines0)
    | none => (qname0, lines0)
  let mut blocks : Array Block := #[]
  let mut cur : Option BlockB := none
  let mut decls : Array (String × Ty) := #[]
  let mut sig : Option String := none
  let mut inSucc := false
  let mut inBody := false
  let flush (cur : Option BlockB) (blocks : Array Block) : Except String (Array Block) := do
    match cur with
    | none => return blocks
    | some b =>
      let t ← match b.term with
        | some t => pure t
        | none =>
          if b.succs.size == 1 then pure (Term.goto b.succs[0]!)
          else throw s!"block {b.id} has no terminator and {b.succs.size} successors"
      return blocks.push { id := b.id, phis := b.phis.toList, stmts := b.stmts.toList, term := t }
  for raw in lines do
    let l := stripLoc raw
    let t := l.trimAscii.toString
    if t.startsWith ";;" then
      let body := (t.drop 2).trimAscii.toString
      if body.startsWith "basic block " then
        blocks ← flush cur blocks
        let n := (body.drop 12).takeWhile Char.isDigit |>.toString.toNat!
        cur := some { id := n }
        inSucc := false
        inBody := true
      else if body.startsWith "succ:" then
        inSucc := true
        let rest := (body.drop 5).trimAscii.toString
        let tgt := rest.takeWhile Char.isDigit |>.toString
        if !tgt.isEmpty then cur := cur.map fun b => { b with succs := b.succs.push tgt.toNat! }
      else if body.startsWith "pred:" then inSucc := false
      else if inSucc && !body.isEmpty && body.front.isDigit then
        let tgt := body.takeWhile Char.isDigit |>.toString
        cur := cur.map fun b => { b with succs := b.succs.push tgt.toNat! }
      continue
    if t.isEmpty || t == "{" || t == "}" then continue
    if !inBody then
      -- signature and declarations
      if t.endsWith ";" && sig.isSome then
        let (ty, name) ← splitDecl (t.dropEnd 1).toString
        let ty ← Ty.ofString ty
        decls := decls.push (name, ty)
      else if t.endsWith ")" && sig.isNone && (qname.isEmpty || (t.splitOn (qname ++ " (")).length > 1) then
        sig := some t
      continue
    let some b := cur | throw s!"statement outside a block: {t}"
    match parseLine t with
    | .error e => throw s!"cannot parse '{t}': {e}"
    | .ok .ignore => pure ()
    | .ok (.phi p) => cur := some { b with phis := b.phis.push p }
    | .ok (.stmt s) => cur := some { b with stmts := b.stmts.push s }
    | .ok (.cond x o y) => cur := some { b with pendingIf := some (x, o, y, none) }
    | .ok .else_ => pure ()
    | .ok (.goto n) =>
      match b.pendingIf with
      | none => cur := some { b with term := some (.goto n) }
      | some (x, o, y, none) => cur := some { b with pendingIf := some (x, o, y, some n) }
      | some (x, o, y, some tt) =>
        cur := some { b with term := some (.cond x o y tt n), pendingIf := none }
    | .ok (.ret v) => cur := some { b with term := some (.ret v) }
  blocks ← flush cur blocks
  let some sigText := sig | throw "no signature line in the section"
  -- `ret name (params)`
  let some oi := (sigText.splitOn " (").head? | throw "bad signature"
  let name :=
    if qname.isEmpty then (oi.splitOn " ").getLast! else qname
  let retS := (oi.dropEnd name.length).trimAscii.toString
  let retTy ← if retS == "void" then pure none else some <$> Ty.ofString retS
  let pstart := (sigText.splitOn (name ++ " (")).tail.foldl (· ++ ·) ""
  let pstr := (pstart.dropEnd 1).toString
  let mut params : Array (String × Ty) := #[]
  for p in splitParams pstr do
    let (ty, nm) ← splitDecl p
    params := params.push (nm, ← Ty.ofString ty)
  return { sym, name, retTy, params := params.toList, decls := decls.toList, blocks := blocks.toList }

end Lift.P2.Gimple
