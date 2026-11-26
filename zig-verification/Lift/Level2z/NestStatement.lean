module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Level2z.NestSpec
public import Lift.Level2z.Code

@[expose] public section

/-! The trusted statement of `l2zNest` (`Lift/LLVM/data/level2z/level2z.zig`, `callconv(.c)`). Not
proved.

    export fn l2zNest(out: [*]u64, r: u64, c: u64) callconv(.c) void {
        for (0..r) |i| {
            for (0..c) |j| out[i *% c +% j] = i +% j;
        }
    }
-/

namespace Lift.Level2z.NestStatement

open Lift.P2.Total Lift.Trusted Lift.Level2z.NestSpec

/-- `l2zNest` in `Code.code`: the entry `0x1001bb`, no stack room (a leaf with no push). The function
has no result: `ret` is `.W64` and `post` ignores the result field. -/
def nest : Fn := ⟨Lift.Level2z.Code.code, 0x1001bb, 0, .W64⟩

/-- The entry is the label `l2zNest`. -/
theorem nest_entry : Lift.Level2z.Code.code.labels.label "l2zNest" = nest.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array object: the old contents of `x` at `out`, writable. The count `r * c` can be below its
length: the words above are in the object and stay. -/
def objects (x : In) (out : BitVec 64) : List Object := [⟨out, Encode.encode x.out, true⟩]

/-- At the return, the array at `out` has the contents of L3. The result field is not used. -/
def post (x : In) (out : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Mem.has policy m ⟨out, Encode.encode y, true⟩

/-- For each input `x` in the contract and each array address `out`, the call `l2zNest(out, r, c)`
returns, and the array has the contents of L3. -/
def NestStatement : Prop :=
  ∀ x, C x → ∀ out : BitVec 64,
    nest.Call [⟨.W64, out⟩, ⟨.W64, x.r⟩, ⟨.W64, x.c⟩] (objects x out) (post x out)

end Lift.Level2z.NestStatement
