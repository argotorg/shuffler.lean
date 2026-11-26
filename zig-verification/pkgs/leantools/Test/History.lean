import LeanTools.History
import Test.Harness

open LeanTools Test

namespace Test.History

def v (text : String) (errors sorries : Nat := 0) : Version := { text, errors, sorries }

def texts (h : History) : List String := h.current.text :: h.past.map (·.text)

def unit : T Unit := do
  let h := History.start (v "a") (cap := 3)
  checkEq "start" (texts h) ["a"]
  let h := h.push (v "b") |>.push (v "c")
  checkEq "push keeps the newest first" (texts h) ["c", "b", "a"]
  checkEq "undo 1" ((h.undo 1).toOption.map texts) (some ["b", "a"])
  checkEq "undo 2" ((h.undo 2).toOption.map texts) (some ["a"])
  check "undo past the start" (h.undo 3).toOption.isNone
  check "undo 0" (h.undo 0).toOption.isNone
  let h4 := h.push (v "d") |>.push (v "e")
  checkEq "cap drops the oldest" (texts h4) ["e", "d", "c", "b"]
  checkEq "lastCompiling skips versions with errors"
    ((History.start (v "a") |>.push (v "b" (errors := 1)) |>.push (v "c" (errors := 2))).lastCompiling?.map (·.1))
    (some 2)
  checkEq "lastCompiling of a compiling current" ((History.start (v "a")).lastCompiling?.map (·.1)) (some 0)
  checkEq "lastCompiling without one" ((History.start (v "a" (errors := 1))).lastCompiling?.map (·.1)) none

/-- Undo of `n` after `k ≥ n` pushes gives the version from `n` pushes before. -/
def prop (input : Nat × Nat) : Bool :=
  let (k, n) := input
  let h := (List.range k).foldl (fun h i => h.push (v (toString (i + 1)))) (History.start (v "0") (cap := 1000))
  match h.undo n with
  | .ok h' => n ≥ 1 && n ≤ k && h'.current.text == toString (k - n)
  | .error _ => n == 0 || n > k

def gen (g : StdGen) : (Nat × Nat) × StdGen :=
  let (k, g) := below 50 g
  let (n, g) := below 55 g
  ((k, n), g)

def suite : T Unit := do
  unit
  forAll "undo returns the version n pushes before" 2000 5 gen prop

end Test.History
