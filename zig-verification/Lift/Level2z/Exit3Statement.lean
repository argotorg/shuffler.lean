module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Level2z.Exit3Spec
public import Lift.Level2z.Code

@[expose] public section

/-! The trusted statement of `l2zExit3` (`Lift/LLVM/data/level2z/level2z.zig`, `callconv(.c)`). Not
proved.

    export fn l2zExit3(p: [*]const u64, n: u64, key: u64, lim: u64) callconv(.c) u64 {
        for (p[0..n], 0..) |v, i| {
            if (v == key) return i;
            if (v > lim) return none;
        }
        return none;
    }
-/

namespace Lift.Level2z.Exit3Statement

open Lift.P2.Total Lift.Trusted Lift.Level2z.Exit3Spec

/-- `l2zExit3` in `Code.code`: the entry `0x100199`, the stack room 8 (`pushq $-1; popq %rax` before the
loop writes the word at `rsp - 8`; there is no other push and no call), and the 64-bit result in
`rax`. -/
def exit3 : Fn := ⟨Lift.Level2z.Code.code, 0x100199, 8, .W64⟩

/-- The entry is the label `l2zExit3`. -/
theorem exit3_entry : Lift.Level2z.Code.code.labels.label "l2zExit3" = exit3.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The array object: the words of `x.xs` at `p`, read-only. -/
def objects (x : In) (p : BitVec 64) : List Object := [⟨p, Encode.encode x.xs, false⟩]

/-- At the return, the result is the result of L3. The `lim` exit and the end of the array both give
`none64`, as in the Zig source. The memory is not in `post`: the frame clause of
`Fn.Return` keeps each byte outside the room, because the array is read-only. -/
def post (x : In) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y = [r]

/-- For each input `x` in the contract and each address `p` of the array, the call
`l2zExit3(p, n, key, lim)` with `n` the length of `x.xs` returns the result of L3. -/
def Exit3Statement : Prop :=
  ∀ x, C x → ∀ p : BitVec 64,
    exit3.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 x.xs.length⟩, ⟨.W64, x.key⟩, ⟨.W64, x.lim⟩]
      (objects x p) (post x)

end Lift.Level2z.Exit3Statement
