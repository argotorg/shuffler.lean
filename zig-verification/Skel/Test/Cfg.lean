import Skel.Cfg

/-! The tests of `Skel/Cfg.lean` (suite `cfg`): `lake exe skel-test --only cfg`. The slice and the `Cfg` are those of
`Lift.Spike.Code.program`. Each check is a value that must hold. A check that does not hold prints one `FAIL` line; the
suite gives the number of failed checks. -/

namespace CfgTests

open Kraken.X64

/-- Is the value an error? -/
def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- The names of the blocks of a `Cfg`, in order, when the value is a `Cfg`. -/
def blockNames : Except String Lift.P2.Gen.Cfg → Option (List String)
  | .ok g => some (g.blocks.toList.map (·.name))
  | .error _ => none

/-- The loop heads of a `Cfg`, when the value is a `Cfg`. -/
def heads : Except String Lift.P2.Gen.Cfg → Option (List Nat)
  | .ok g => some g.heads
  | .error _ => none

/-- Does the value give a `Cfg` with at least one block? -/
def hasBlocks : Except String Lift.P2.Gen.Cfg → Bool
  | .ok g => !g.blocks.isEmpty
  | .error _ => false

/-- The number of directives of a slice, when the value is a slice. -/
def sliceSize : Except String Program → Option Nat
  | .ok p => some p.length
  | .error _ => none

/-- Does the slice end with `retq`? -/
def endsWithRet : Except String Program → Bool
  | .ok p => match p.getLast? with
    | some (.instr (.regular _ _ .ret)) => true
    | _ => false
  | .error _ => false

/-- Does the slice start with its label? -/
def startsWithLabel (name : String) : Except String Program → Bool
  | .ok p => p.head? == some (.label name)
  | .error _ => false

/-- Does the slice contain a label of an end of a function? -/
def hasEndLabel : Except String Program → Bool
  | .ok p => p.labels.any (·.startsWith ".Lfunc_end")
  | .error _ => true

/-- The checks of the slice and the `Cfg`, each with its name. -/
def checks : List (String × Bool) :=
  let sum := Skel.Cfg.sliceFunction Lift.Spike.Code.program "toySum"
  -- The first block is the entry of the slice, and `blockNameOf` names the entry `entry` (Lift/V2/Lifter.lean).
  [ ("toySum: block names", blockNames (Skel.Cfg.ofFunction "toySum") == some ["entry", "LBB1_1", "LBB1_3"]),
    ("toySum: loop heads", heads (Skel.Cfg.ofFunction "toySum") == some [1]),
    ("unknown name is an error", isError (Skel.Cfg.ofFunction "noSuchFunction")),
    ("empty name is an error", isError (Skel.Cfg.ofFunction "")),
    ("first function (toyJob) gives blocks", hasBlocks (Skel.Cfg.ofFunction "toyJob")),
    ("last function (toyInc) gives blocks", hasBlocks (Skel.Cfg.ofFunction "toyInc")),
    ("toySum slice has 11 directives", sliceSize sum == some 11),
    ("toySum slice starts with its label", startsWithLabel "toySum" sum),
    ("toySum slice ends with retq", endsWithRet sum),
    ("toySum slice has no end label", !hasEndLabel sum),
    ("unknown name gives no slice", isError (Skel.Cfg.sliceFunction Lift.Spike.Code.program "noSuchFunction")) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `cfg`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "cfg" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  cfg: {name}"
  return failed

end CfgTests
