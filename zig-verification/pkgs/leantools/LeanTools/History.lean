/-!
# Version history of a working file

A persistent stack: each edit pushes a version, and `undo n` goes back `n` versions. A version
keeps the check result, so that the last version without errors can be found.
-/

namespace LeanTools

structure Version where
  text : String
  errors : Nat
  sorries : Nat
deriving Repr, BEq

structure History where
  current : Version
  /-- Earlier versions, the newest first. -/
  past : List Version
  /-- The most earlier versions that are kept. -/
  cap : Nat

def History.start (v : Version) (cap : Nat := 200) : History := { current := v, past := [], cap }

def History.push (h : History) (v : Version) : History :=
  { h with current := v, past := (h.current :: h.past).take h.cap }

def History.undo (h : History) (n : Nat) : Except String History :=
  if n == 0 then .error "undo needs at least 1 step"
  else match h.past.drop (n - 1) with
    | v :: rest => .ok { h with current := v, past := rest }
    | [] => .error s!"only {h.past.length} earlier versions are kept"

/-- The number of steps back to the newest version with no errors, and that version. -/
def History.lastCompiling? (h : History) : Option (Nat × Version) :=
  ((h.current :: h.past).zipIdx).find? (·.1.errors == 0) |>.map fun (v, i) => (i, v)

end LeanTools
