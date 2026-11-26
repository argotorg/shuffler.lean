module

public import Lift.Trusted.Encode

@[expose] public section

/-! Generic `Encode` instances for the shuffler pilot: one, two and four bytes, `bool`, a list of
bytes, and fixed-size arrays. Each instance gives the fields of a value in memory order. -/

namespace Lift.Pilot.Encode

open Lift.Trusted

/-- One byte: one field of 8 bits. -/
instance : Encode (BitVec 8) where
  encode v := [⟨.W8, v⟩]
  decode
    | [⟨.W8, v⟩] => some v
    | _ => none

/-- Two bytes: one field of 16 bits. -/
instance : Encode (BitVec 16) where
  encode v := [⟨.W16, v⟩]
  decode
    | [⟨.W16, v⟩] => some v
    | _ => none

/-- Four bytes: one field of 32 bits. -/
instance : Encode (BitVec 32) where
  encode v := [⟨.W32, v⟩]
  decode
    | [⟨.W32, v⟩] => some v
    | _ => none

/-- `bool`: one byte, `false` is 0 and `true` is 1 (the Zig `bool` layout). -/
instance : Encode Bool where
  encode b := [⟨.W8, if b then 1 else 0⟩]
  decode
    | [⟨.W8, v⟩] => if v = 0 then some false else if v = 1 then some true else none
    | _ => none

/-- A list of bytes: one field of 8 bits for each element, in order, with no padding. -/
instance : Encode (List (BitVec 8)) where
  encode xs := xs.map fun v => ⟨.W8, v⟩
  decode fs := fs.mapM fun
    | ⟨.W8, v⟩ => some v
    | _ => none

/-- The fields of `n` elements of `k` fields each, in order: the decodes of the chunks of `k`
fields, and no field left over. -/
def decodeElems {α : Type} [Encode α] (k : Nat) : Nat → List Field → Option (List α)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, fs => do
    let x ← Encode.decode (fs.take k)
    let xs ← decodeElems k n (fs.drop k)
    return x :: xs

/-- A fixed-size array of `n` elements: the encodings of the elements in index order, with no
padding. The decode takes the field count of one element from `default`, so it is exact only when
every value of `α` has that field count. -/
instance {α : Type} {n : Nat} [Encode α] [Inhabited α] : Encode (Vector α n) where
  encode v := v.toList.flatMap Encode.encode
  decode fs := do
    let xs ← decodeElems (Encode.encode (default : α)).length n fs
    if h : xs.length = n then some ⟨xs.toArray, by simpa using h⟩ else none

end Lift.Pilot.Encode
