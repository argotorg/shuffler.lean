module

public import Lift.Trusted.Object

@[expose] public section

/-! `Encode`: the fields of a value of a public type, in memory order. A generator prints the
instances of the public types from `types.json`; the instances here are for `u64`, pointers and
arrays of `u64`. -/

namespace Lift.Trusted

/-- The fields of a value in memory order, and the inverse. -/
class Encode (α : Type) where
  encode : α → List Field
  decode : List Field → Option α

/-- The value of a field of 64 bits. -/
def word? : Field → Option (BitVec 64)
  | ⟨.W64, v⟩ => some v
  | _ => none

/-- A `u64` or a pointer: one field of 64 bits. -/
instance : Encode (BitVec 64) where
  encode v := [⟨.W64, v⟩]
  decode
    | [f] => word? f
    | _ => none

/-- An array of `u64`: one field of 64 bits for each element, with no padding. -/
instance : Encode (List (BitVec 64)) where
  encode xs := xs.map fun v => ⟨.W64, v⟩
  decode fs := fs.mapM word?

end Lift.Trusted
