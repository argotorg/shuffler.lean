/-
Terms, literals and facts of the generic miner, and the heaps they are evaluated on.

A heap is a `Snap`: the distinguished objects, the objects with their type, and the value of each field
(a pointer or a scalar, as a 64-bit word). A *fact* is a statement about all objects `x` of one type `cls`: a
disjunction of literals; a literal compares two terms. A term is `x`, a distinguished object, a constant, or a
field of a term. The field of a term that is null, or is no object of the field's owner type, is 0 (as the
`View.get` of the tree miner gives the default record), so every term is defined at every address.

The Horn form `p₁, …, pₙ → c` is the disjunction `¬p₁ ∨ … ∨ ¬pₙ ∨ c`; `Fact.show` prints the last literal as the
conclusion.
-/
import Lift.Inv.Gen.Univ
import Std.Data.HashMap

namespace Lift.Inv.Gen
open Lift.Heap

abbrev Addr := BitVec 64

inductive Term where
  | x
  /-- The distinguished object `i` of the `Univ`. -/
  | root (i : Nat)
  | k (n : Nat)
  /-- The field `f` (an index) of the term, which has the type `ty`. -/
  | fld (t : Term) (ty : Nat) (f : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- `a = b` (`pos`) or `a ≠ b`. -/
structure Lit where
  a : Term
  b : Term
  pos : Bool
  deriving DecidableEq, Repr, Inhabited, Hashable

def Lit.neg (l : Lit) : Lit := { l with pos := !l.pos }

/-- For all objects `x` of the type `cls`: some literal holds. -/
structure Fact where
  cls : Nat
  lits : List Lit
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- `prem → concl` as a fact. -/
def Fact.horn (cls : Nat) (prem : List Lit) (concl : Lit) : Fact := ⟨cls, prem.map Lit.neg ++ [concl]⟩

/-! ### Heaps -/

structure Snap where
  roots : Array Addr := #[]
  /-- The objects with their type, the distinguished ones first. -/
  objs : Array (Addr × Nat) := #[]
  /-- The type and the field values of each object, in the order of the fields. -/
  vals : Std.HashMap Addr (Nat × Array Addr) := {}
  deriving Inhabited

namespace Snap

/-- The heap with no object. -/
def empty : Snap := {}

def typeOf? (s : Snap) (a : Addr) : Option Nat := (s.vals[a]?).map (·.1)

def has (s : Snap) (a : Addr) : Bool := s.vals.contains a

/-- The field `f` of the object `a` if it has the type `ty`; else 0. -/
def field (s : Snap) (ty f : Nat) (a : Addr) : Addr :=
  match s.vals[a]? with
  | some (t, vs) => if t == ty then vs[f]?.getD 0 else 0
  | none => 0

/-- The objects of one type. -/
def ofType (s : Snap) (t : Nat) : List Addr := (s.objs.toList.filter (·.2 == t)).map (·.1)

def addrs (s : Snap) : List Addr := s.objs.toList.map (·.1)

end Snap

/-- The value of a term at the object `x`. -/
def Term.eval (s : Snap) (x : Addr) : Term → Addr
  | .x => x
  | .root i => s.roots[i]?.getD 0
  | .k n => BitVec.ofNat 64 n
  | .fld t ty f => s.field ty f (t.eval s x)

/-- The value of a term when some fields are unknown (`get a ty f`: the field `f` of the object `a`, if known). -/
def Term.evalP (typeOf : Addr → Option Nat) (roots : Array Addr) (get : Addr → Nat → Option Addr) (x : Addr) :
    Term → Option Addr
  | .x => some x
  | .root i => some (roots[i]?.getD 0)
  | .k n => some (BitVec.ofNat 64 n)
  | .fld t ty f => do
    let a ← t.evalP typeOf roots get x
    if a == 0 then some 0
    else match typeOf a with
      | some t' => if t' == ty then get a f else some 0
      | none => some 0

def Lit.holds (s : Snap) (x : Addr) (l : Lit) : Bool := (l.a.eval s x == l.b.eval s x) == l.pos

def Fact.holdsAt (s : Snap) (c : Fact) (x : Addr) : Bool := c.lits.any (·.holds s x)

/-- The fact holds in the heap: at every object of its type. -/
def Fact.holds (s : Snap) (c : Fact) : Bool := s.objs.all fun (x, t) => t != c.cls || c.holdsAt s x

/-- The objects of the type where the fact fails. -/
def Fact.failures (s : Snap) (c : Fact) : List Addr :=
  (s.objs.toList.filter fun (x, t) => t == c.cls && !c.holdsAt s x).map (·.1)

/-! ### Text -/

/-- The name of a field without the member prefix `_M_` of libstdc++. -/
def shortName (n : String) : String := if n.startsWith "_M_" then (n.drop 3).toString else n

def Term.show (U : Univ) : Term → String
  | .x => "x"
  | .root i => U.fixedName i
  | .k n => toString n
  | .fld t ty f => t.show U ++ "." ++ shortName (U.fld ty f).name

def Lit.show (U : Univ) (l : Lit) : String :=
  l.a.show U ++ (if l.pos then " = " else " ≠ ") ++ l.b.show U

/-- `x ≠ h → x.parent ≠ 0`: the last literal is the conclusion, the negation of the others are the premises. -/
def Fact.show (U : Univ) (c : Fact) : String :=
  match c.lits.reverse with
  | [] => "false"
  | concl :: rest =>
    match rest.reverse with
    | [] => concl.show U
    | ps => ", ".intercalate (ps.map fun l => l.neg.show U) ++ " → " ++ concl.show U

/-- The terms that occur in a fact. -/
def Term.subterms : Term → List Term
  | .fld t ty f => .fld t ty f :: t.subterms
  | t => [t]

end Lift.Inv.Gen
