module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Level2z.TwoLoopsSpec
public import Lift.Level2z.Code

@[expose] public section

/-! The trusted statement of `l2zTwoLoops` (`Lift/LLVM/data/level2z/level2z.zig`, `callconv(.c)`). Not
proved.

    export fn l2zTwoLoops(f: [*]u8, n: u64) callconv(.c) u64 {
        const s = f[0..n];
        var c: u64 = 0;
        for (s) |v| c +%= b(v != 0);
        for (s) |*v| v.* = 0;
        return c;
    }
-/

namespace Lift.Level2z.TwoLoopsStatement

open Lift.P2.Total Lift.Trusted Lift.Level2z.TwoLoopsSpec

/-- `l2zTwoLoops` in `Code.code`: the entry `0x1001e8`, no stack room (a leaf with no push), and the
64-bit result in `rax`. -/
def twoLoops : Fn := ⟨Lift.Level2z.Code.code, 0x1001e8, 0, .W64⟩

/-- The entry is the label `l2zTwoLoops`. -/
theorem twoLoops_entry : Lift.Level2z.Code.code.labels.label "l2zTwoLoops" = twoLoops.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array object: the old contents `x` at `f`, writable. -/
def objects (x : In) (f : BitVec 64) : List Object := [⟨f, Encode.encode x, true⟩]

/-- At the return, the result field is the count of L3 and the array at `f` has the contents of L3. -/
def post (x : In) (f : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y.1 = [r] ∧ Mem.has policy m ⟨f, Encode.encode y.2, true⟩

/-- For each input `x` in the contract and each array address `f`, the call `l2zTwoLoops(f, n)` with `n`
the length of `x` returns the count and the contents of L3. -/
def TwoLoopsStatement : Prop :=
  ∀ x, C x → ∀ f : BitVec 64,
    twoLoops.Call [⟨.W64, f⟩, ⟨.W64, BitVec.ofNat 64 x.length⟩] (objects x f) (post x f)

end Lift.Level2z.TwoLoopsStatement
