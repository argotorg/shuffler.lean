/-! A minimal test harness: named checks that collect failures, and a seeded generator for
property tests, so that a failure is reproducible. -/

namespace Test

structure Failure where
  name : String
  detail : String

abbrev T := StateT (Array Failure) IO

def check (name : String) (cond : Bool) (detail : String := "") : T Unit :=
  unless cond do modify (·.push { name, detail })

def checkEq {α : Type} [BEq α] [Repr α] (name : String) (got want : α) : T Unit :=
  check name (got == want) s!"got {repr got}, want {repr want}"

/-- Runs `prop` on `n` inputs from `gen`, with the generator seeded by `seed`. -/
def forAll {α : Type} [Repr α] (name : String) (n seed : Nat) (gen : StdGen → α × StdGen)
    (prop : α → Bool) : T Unit := do
  let mut g := mkStdGen seed
  for i in [0:n] do
    let (x, g') := gen g
    g := g'
    unless prop x do
      modify (·.push { name, detail := s!"case {i} (seed {seed}): {repr x}" })
      return

def run (suites : List (String × T Unit)) : IO UInt32 := do
  let mut failed := 0
  for (suite, t) in suites do
    let ((), fs) ← t.run #[]
    for f in fs do
      IO.println s!"FAIL {suite}/{f.name}: {f.detail}"
    failed := failed + fs.size
  IO.println s!"{failed} failures"
  return if failed == 0 then 0 else 1

/-- A random natural number below `n` (`n > 0`). -/
def below (n : Nat) (g : StdGen) : Nat × StdGen :=
  let (x, g) := randNat g 0 (n - 1)
  (x, g)

/-- A random string over `alphabet` with length below `n`. -/
def randString (alphabet : Array Char) (n : Nat) (g : StdGen) : String × StdGen := Id.run do
  let (len, g) := below n g
  let mut g := g
  let mut s := ""
  for _ in [0:len] do
    let (i, g') := below alphabet.size g
    g := g'
    s := s.push alphabet[i]!
  return (s, g)

end Test
