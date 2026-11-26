import Skel.Test.DeriveReader

/-! The suite `reader` (task READER): `lake exe skel-test --only reader`. `Skel/Test/DeriveReader.lean` (imported, checked when
this module builds) has the checks of the reader rules D1 to D3 on synthetic blocks and small terms. The suite checks again
that each block of the synthetic functions has a derived part. -/

namespace GenReaderTests

/-- The synthetic functions with a block that does not derive. -/
def notDerived : List String :=
  DeriveReaderCode.fns.filter fun fn =>
    match DeriveReaderCode.derived.lookup fn with
    | some ps => ps.isEmpty || ps.any (fun p => p.2 matches .error _)
    | none => true

/-- Gives the number of failed checks. The suite runs when `only` is none or `reader`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "reader" then return 0
  for fn in notDerived do IO.println s!"FAIL  reader: {fn} has a block that does not derive"
  return notDerived.length

end GenReaderTests
