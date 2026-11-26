module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Toys.FindSpec
public import Lift.Toys.Code

@[expose] public section

/-! The trusted statement of `toyFind` (`Lift/Toys/data/toy.zig`, `callconv(.c)`). Not proved.

    export fn toyFind(p: [*]const u64, n: u64, key: u64) callconv(.c) u64 {
        var i: u64 = 0;
        while (i < n) : (i += 1) { if (p[i] == key) return i; }
        return n;
    }
-/

namespace Lift.Toys.FindStatement

open Lift.P2.Total Lift.Trusted Lift.Toys.FindSpec

/-- `toyFind` in `Code.code`: the entry `0x100032`, no stack room (a leaf with no push), and the
64-bit result in `rax`. -/
def toyFind : Fn := ⟨Code.code, 0x100032, 0, .W64⟩

/-- The entry is the label `toyFind`. -/
theorem toyFind_entry : Code.code.labels.label "toyFind" = toyFind.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array object: the words of `x.xs` at `p`, read-only. -/
def objects (x : In) (p : BitVec 64) : List Object := [⟨p, Encode.encode x.xs, false⟩]

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause
of `Fn.Return` keeps each byte, because the array is read-only and the room is empty. -/
def post (x : In) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y = [r]

/-- For each input `x` in the contract and each address `p` of the array, the call
`toyFind(p, n, key)` with `n` the length of `x.xs` returns the result of L3. -/
def FindStatement : Prop :=
  ∀ x, C x → ∀ p : BitVec 64,
    toyFind.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 x.xs.length⟩, ⟨.W64, x.key⟩] (objects x p)
      (post x)

end Lift.Toys.FindStatement
