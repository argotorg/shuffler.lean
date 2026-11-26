module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Spike.SumSpec
public import Lift.Spike.Code

@[expose] public section

/-! The trusted statement of `toySum` (`Lift/LLVM/data/toy/toy.zig`, `callconv(.c)`). Not proved.

    export fn toySum(p: [*]const u64, n: u64) callconv(.c) u64 {
        var s: u64 = 0;
        for (p[0..n]) |v| s +%= v;
        return s;
    }
-/

namespace Lift.Spike.SumStatement

open Lift.P2.Total Lift.Trusted Lift.Spike.SumSpec

/-- `toySum` in `Code.code`: the entry `0x100022`, no stack room (a leaf with no push), and the
64-bit result in `rax`. -/
def toySum : Fn := ⟨Code.code, 0x100022, 0, .W64⟩

/-- The entry is the label `toySum`. -/
theorem toySum_entry : Code.code.labels.label "toySum" = toySum.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array object: the words of `xs` at `p`, read-only. -/
def objects (xs : List (BitVec 64)) (p : BitVec 64) : List Object := [⟨p, Encode.encode xs, false⟩]

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause
of `Fn.Return` keeps each byte, because the array is read-only and the room is empty. -/
def post (xs : List (BitVec 64)) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs = some y ∧ Encode.encode y = [r]

/-- For each input `xs` in the contract and each address `p` of the array, the call
`toySum(p, n)` with `n` the length of `xs` returns the result of L3. -/
def SumStatement : Prop :=
  ∀ xs, C xs → ∀ p : BitVec 64,
    toySum.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 xs.length⟩] (objects xs p) (post xs)

end Lift.Spike.SumStatement
