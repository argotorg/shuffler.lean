module

public import Lift.P2.Total.Memory

@[expose] public section

/-! The objects of a trusted statement: values of fixed widths at an address, and what it means
that a memory and a policy have them. The addresses are `BitVec 64`; an object must not wrap past
`2^64`, so the byte ranges are compared as natural numbers. -/

namespace Lift.Trusted

open Lift.P2.Total

/-- A value of one width. -/
structure Field where
  w : Width
  v : w.type
deriving DecidableEq

/-- An object: an address, its fields in sequence, and whether a call can change it. -/
structure Object where
  addr : BitVec 64
  fields : List Field
  writable : Bool

/-- The fields, each with its byte offset; the first offset is `off`. -/
def offsets : Nat → List Field → List (Nat × Field)
  | _, [] => []
  | off, f :: fs => (off, f) :: offsets (off + f.w.bytes) fs

/-- The number of bytes of the object. -/
def Object.size (o : Object) : Nat := (o.fields.map fun f => f.w.bytes).sum

/-- The byte `b` is in `[a, a + n)`. -/
def InBytes (a : BitVec 64) (n : Nat) (b : BitVec 64) : Prop :=
  a.toNat ≤ b.toNat ∧ b.toNat < a.toNat + n

/-- The bytes `[a, a + n)` and `[b, b + k)` have no byte in common. -/
def Apart (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- A writable object has no byte in common with another object of the list. -/
def Separate (objs : List Object) : Prop :=
  objs.Pairwise fun o o' => (o.writable ∨ o'.writable) → Apart o.addr o.size o'.addr o'.size

/-- The memory `m` has the object `o` under `policy`: `o` does not wrap past `2^64`, the read of
each field is permitted and gives its value, and the write of each field of a writable `o` is
permitted. -/
def Mem.has (policy : CpuPolicy) (m : DataMem) (o : Object) : Prop :=
  o.addr.toNat + o.size ≤ 2 ^ 64 ∧
    ∀ x ∈ offsets 0 o.fields,
      readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v ∧
        (o.writable = true → policy.permits (.write (o.addr + BitVec.ofNat 64 x.1) x.2.w) = true)

end Lift.Trusted
