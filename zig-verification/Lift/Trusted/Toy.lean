module

public import Lift.Trusted.Encode

@[expose] public section

/-! The public record of `Lift/LLVM/data/toy/toy.zig`, in the form that a generator prints from
`types.json`:

    const Job = extern struct { src: [*]const u64, len: u64, limit: u64, total: u64 };
-/

namespace Lift.Trusted.Toy

open Lift.Trusted

/-- The record `Job`: 32 bytes, the fields at the offsets 0, 8, 16 and 24. -/
structure Job where
  src : BitVec 64
  len : BitVec 64
  limit : BitVec 64
  total : BitVec 64
deriving DecidableEq

/-- The fields of `Job` in the order of the declaration, each with the instance of its type. -/
instance : Encode Job where
  encode j := Encode.encode j.src ++ Encode.encode j.len ++ Encode.encode j.limit ++
    Encode.encode j.total
  decode
    | [a, b, c, d] => do
      return ⟨(← Encode.decode [a]), (← Encode.decode [b]), (← Encode.decode [c]),
        (← Encode.decode [d])⟩
    | _ => none

end Lift.Trusted.Toy
