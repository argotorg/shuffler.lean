import LeanTools.Pos
import Test.Harness

open LeanTools Test

namespace Test.Pos

def unit : T Unit := do
  checkEq "ascii" (utf16Of "abc" 2) 2
  checkEq "BMP symbol is one unit" (utf16Of "⊢ x" 2) 2
  checkEq "astral symbol is two units" (utf16Of "𝔽x" 1) 2
  checkEq "past the end" (utf16Of "ab" 5) 2
  checkEq "back ascii" (colOfUtf16 "abc" 2) 2
  checkEq "back astral" (colOfUtf16 "𝔽x" 2) 1
  checkEq "back inside a pair" (colOfUtf16 "𝔽x" 1) 0
  checkEq "back past the end" (colOfUtf16 "ab" 9) 2
  checkEq "lineAt" (lineAt "a\nb\nc" 1) "b"
  checkEq "lineAt past the end" (lineAt "a" 3) ""

def alphabet : Array Char := #['a', '⊢', '𝔽', 'ℕ', ' ']

/-- `colOfUtf16` inverts `utf16Of` on character boundaries. -/
def prop (input : String × Nat) : Bool :=
  let (line, k) := input
  let col := min k line.length
  colOfUtf16 line (utf16Of line col) == col

def gen (g : StdGen) : (String × Nat) × StdGen :=
  let (s, g) := randString alphabet 20 g
  let (k, g) := below 25 g
  ((s, k), g)

def suite : T Unit := do
  unit
  forAll "round trip" 2000 6 gen prop

end Test.Pos
