/-
SMT-LIB terms and scripts as a Lean AST, and their text.

The queries of the triage (`Lift.Smt.Encode`) are built as values of these types and printed once, at the end.
The solver is an untrusted process: it reads the text, and nothing in Lean depends on its answer except the
replay of a model (`Lift.Smt.Replay`).

The sorts: `Bool`, `Int`, bit vectors and arrays. A term has bit-vector literals (`lit w v`), the application of a
function symbol (`app`), the indexed operators `extract` and `zero_extend`, and `ite`. The smart constructors fold
the constants (`and`, `or`, `not`, `ite`, `eq`) so that the text of a query is not made of `true` and `false`.
-/

namespace Lift.Smt

inductive Srt where
  | bool
  | int
  | bv (w : Nat)
  | array (i o : Srt)
  deriving BEq, Repr, Inhabited

partial def Srt.text : Srt → String
  | .bool => "Bool"
  | .int => "Int"
  | .bv w => s!"(_ BitVec {w})"
  | .array i o => s!"(Array {i.text} {o.text})"

inductive Tm where
  | var (name : String)
  | tt
  | ff
  /-- A bit-vector literal of width `w` and value `v` (reduced modulo `2 ^ w`). -/
  | lit (w : Nat) (v : Nat)
  | num (v : Int)
  | app (op : String) (args : List Tm)
  | ext (hi lo : Nat) (a : Tm)
  | zext (k : Nat) (a : Tm)
  | ifte (c a b : Tm)
  deriving BEq, Repr, Inhabited

namespace Tm

def lit' (w v : Nat) : Tm := .lit w (v % 2 ^ w)

def isTrue : Tm → Bool | .tt => true | _ => false
def isFalse : Tm → Bool | .ff => true | _ => false

def not : Tm → Tm
  | .tt => .ff
  | .ff => .tt
  | .app "not" [a] => a
  | a => .app "not" [a]

def and (a b : Tm) : Tm :=
  if a.isFalse || b.isFalse then .ff
  else if a.isTrue then b
  else if b.isTrue then a
  else .app "and" [a, b]

def or (a b : Tm) : Tm :=
  if a.isTrue || b.isTrue then .tt
  else if a.isFalse then b
  else if b.isFalse then a
  else .app "or" [a, b]

def all (ts : List Tm) : Tm := ts.foldl and .tt
def any (ts : List Tm) : Tm := ts.foldl or .ff

def imp (a b : Tm) : Tm := or (not a) b

def eq (a b : Tm) : Tm := if a == b then .tt else .app "=" [a, b]

def ite (c a b : Tm) : Tm :=
  if c.isTrue then a else if c.isFalse then b else if a == b then a else .ifte c a b

def bin (op : String) (a b : Tm) : Tm := .app op [a, b]

def add (a b : Tm) : Tm :=
  match a, b with
  | .lit _ 0, x => x
  | x, .lit _ 0 => x
  | .lit w x, .lit _ y => .lit' w (x + y)
  | _, _ => .app "bvadd" [a, b]

def sub (a b : Tm) : Tm :=
  match a, b with
  | x, .lit _ 0 => x
  | .lit w x, .lit _ y => .lit' w (x + 2 ^ w - y % 2 ^ w)
  | _, _ => .app "bvsub" [a, b]

def ult (a b : Tm) : Tm := .app "bvult" [a, b]
def ule (a b : Tm) : Tm := .app "bvule" [a, b]
def select (a i : Tm) : Tm := .app "select" [a, i]
def store (a i v : Tm) : Tm := .app "store" [a, i, v]

/-- The concatenation, the first term in the high bits. -/
def concat (a b : Tm) : Tm := .app "concat" [a, b]

/-- The bytes `b :: bs` (the first is the lowest) as one value (little endian). -/
def ofBytes (b : Tm) : List Tm → Tm
  | [] => b
  | c :: cs => concat (ofBytes c cs) b

/-- The number of nodes (a measure of the size of the term). -/
partial def size : Tm → Nat
  | .app _ as => 1 + (as.map size).foldl (· + ·) 0
  | .ext _ _ a | .zext _ a => 1 + size a
  | .ifte c a b => 1 + size c + size a + size b
  | _ => 1

partial def text : Tm → String
  | .var n => n
  | .tt => "true"
  | .ff => "false"
  | .lit w v => s!"(_ bv{v} {w})"
  | .num v => if v < 0 then s!"(- {-v})" else s!"{v}"
  | .app op [] => op
  | .app op as => "(" ++ op ++ " " ++ " ".intercalate (as.map text) ++ ")"
  | .ext hi lo a => s!"((_ extract {hi} {lo}) {text a})"
  | .zext k a => s!"((_ zero_extend {k}) {text a})"
  | .ifte c a b => s!"(ite {text c} {text a} {text b})"

end Tm

inductive Cmd where
  | logic (name : String)
  | option (key value : String)
  | comment (text : String)
  /-- `declare-fun name (args) ret`: a constant when `args` is empty. -/
  | declare (name : String) (args : List Srt) (ret : Srt)
  /-- `define-fun name () sort term`. -/
  | define (name : String) (sort : Srt) (t : Tm)
  | assert (t : Tm)
  | checkSat
  | getValue (ts : List Tm)
  | getUnsatCore
  deriving Repr

def Cmd.text : Cmd → String
  | .logic n => s!"(set-logic {n})"
  | .option k v => s!"(set-option :{k} {v})"
  | .comment t => "; " ++ (t.replace "\n" " ")
  | .declare n as r => s!"(declare-fun {n} ({" ".intercalate (as.map Srt.text)}) {r.text})"
  | .define n s t => s!"(define-fun {n} () {s.text} {t.text})"
  | .assert t => s!"(assert {t.text})"
  | .checkSat => "(check-sat)"
  | .getValue ts => s!"(get-value ({" ".intercalate (ts.map Tm.text)}))"
  | .getUnsatCore => "(get-unsat-core)"

def script (cs : List Cmd) : String := "\n".intercalate (cs.map Cmd.text) ++ "\n"

end Lift.Smt
