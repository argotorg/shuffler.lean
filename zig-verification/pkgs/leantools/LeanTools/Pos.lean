/-!
# Positions

The tools count lines from 1 and columns in characters from 1; LSP counts lines from 0 and
columns in UTF-16 code units from 0.
-/

namespace LeanTools

def utf16Units (c : Char) : Nat := if c.val < 0x10000 then 1 else 2

/-- The UTF-16 offset of the character at index `col` (from 0) of `line`. -/
def utf16Of (line : String) (col : Nat) : Nat :=
  ((line.toList.take col).map utf16Units).sum

/-- The index of the character that starts at UTF-16 offset `u` of `line`; an offset inside a
surrogate pair gives the index of its character. -/
def colOfUtf16 (line : String) (u : Nat) : Nat :=
  go line.toList 0 0
where
  go : List Char → Nat → Nat → Nat
    | [], _, i => i
    | c :: cs, acc, i => if acc + utf16Units c > u then i else go cs (acc + utf16Units c) (i + 1)

/-- Line `n` (from 0) of `text`, or "" past the end. -/
def lineAt (text : String) (n : Nat) : String :=
  ((text.splitOn "\n")[n]?).getD ""

end LeanTools
