module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Toys.FillSpec
public import Lift.Toys.Code

@[expose] public section

/-! The trusted statement of `toyFill` (`Lift/Toys/data/toy.zig`, `callconv(.c)`). Not proved.

    export fn toyFill(p: [*]u64, n: u64) callconv(.c) void {
        var i: u64 = 0;
        while (i < n) : (i += 1) p[i] = i;
    }
-/

namespace Lift.Toys.FillStatement

open Lift.P2.Total Lift.Trusted Lift.Toys.FillSpec

/-- `toyFill` in `Code.code`: the entry `0x1000a8`, no stack room (a leaf with no push). The function
has no result: `ret` is `.W64` and `post` ignores the result field. -/
def toyFill : Fn := ⟨Code.code, 0x1000a8, 0, .W64⟩

/-- The entry is the label `toyFill`. -/
theorem toyFill_entry : Code.code.labels.label "toyFill" = toyFill.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array of the call: the old contents `x` at `p`, writable. -/
def objects (x : In) (p : BitVec 64) : List Object := [⟨p, Encode.encode x, true⟩]

/-- At the return, L3 gives `y` and the array at `p` has the contents `y`. The result field is not
used. -/
def post (x : In) (p : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Mem.has policy m ⟨p, Encode.encode y, true⟩

/-- For each input `x` in the contract and each array address `p`, each call `toyFill(p, len)`
returns, and the array has the contents of L3. -/
def FillStatement : Prop :=
  ∀ x, C x → ∀ p : BitVec 64,
    toyFill.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 x.length⟩] (objects x p) (post x p)

end Lift.Toys.FillStatement
