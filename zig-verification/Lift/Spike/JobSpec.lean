module

@[expose] public section

/-! The L3 specification of `toyJob` (`Lift/LLVM/data/toy/toy.zig`): pure values only. The sum is
`List.sum` on `BitVec 64`, the sum of `Lift.Spike.Sum.run`. -/

namespace Lift.Spike.JobSpec

/-- The status of `toyJob`. -/
inductive Status where
  | done
  | tooLong
deriving DecidableEq, Repr

/-- The input: the source array (its length is the `len` field), the limit, the old total. -/
structure In where
  src : List (BitVec 64)
  limit : BitVec 64
  total : BitVec 64
deriving DecidableEq, Repr

/-- The result: the status and the new total. -/
structure Out where
  status : Status
  total : BitVec 64
deriving DecidableEq, Repr

/-- `too_long` and the old total if the array is longer than the limit, else `done` and the
wrapping sum; no result if the length does not fit in 64 bits. -/
def run (x : In) : Option Out :=
  if x.src.length < 2 ^ 64 then
    some (if x.limit.toNat < x.src.length then ⟨.tooLong, x.total⟩ else ⟨.done, x.src.sum⟩)
  else none

/-- The contract: the length of the array fits in the 64-bit `len` field. -/
def C (x : In) : Prop := x.src.length < 2 ^ 64

theorem total : ∀ x, C x → ∃ y, run x = some y := fun x hx =>
  ⟨if x.limit.toNat < x.src.length then ⟨.tooLong, x.total⟩ else ⟨.done, x.src.sum⟩,
    by unfold C at hx; simp only [run, hx, ↓reduceIte]⟩

end Lift.Spike.JobSpec
