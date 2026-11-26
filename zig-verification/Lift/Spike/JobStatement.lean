module

public import Lift.Trusted.Call
public import Lift.Trusted.Toy
public import Lift.Spike.JobSpec
public import Lift.Spike.Code

@[expose] public section

/-! The trusted statement of `toyJob` (`Lift/LLVM/data/toy/toy.zig`, `callconv(.c)`):

    const Job = extern struct { src: [*]const u64, len: u64, limit: u64, total: u64 };
    const Status = enum(u32) { done = 0, too_long = 1 };
    export fn toyJob(j: *Job) Status {
        if (j.len > j.limit) return .too_long;
        j.total = @call(.never_inline, toySum, .{ j.src, j.len });
        return .done;
    }
-/

namespace Lift.Spike.JobStatement

open Lift.P2.Total Lift.Trusted Lift.Trusted.Toy Lift.Spike.JobSpec

/-- `enum(u32) { done = 0, too_long = 1 }`: one field of 32 bits. -/
instance : Encode Status where
  encode
    | .done => [⟨.W32, 0⟩]
    | .tooLong => [⟨.W32, 1⟩]
  decode
    | [⟨.W32, v⟩] => if v = 0 then some .done else if v = 1 then some .tooLong else none
    | _ => none

/-- `toyJob` in `Code.code`: the entry `0x100000`, 16 bytes of stack room (`pushq %rbx` and the
return address of the call of `toySum`), and the 32-bit result in `eax`. -/
def toyJob : Fn := ⟨Code.code, 0x100000, 16, .W32⟩

/-- The entry is the label `toyJob`. -/
theorem toyJob_entry : Code.code.labels.label "toyJob" = toyJob.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The record `*j` for the input `x`: `src` is the address of the array, `len` its length. -/
def record (x : In) (src total : BitVec 64) : Job :=
  { src := src, len := BitVec.ofNat 64 x.src.length, limit := x.limit, total := total }

/-- The objects of the call: the record `*j` (writable) and the array `src[0..len]` (read-only). -/
def objects (x : In) (j src : BitVec 64) : List Object :=
  [⟨j, Encode.encode (record x src x.total), true⟩, ⟨src, Encode.encode x.src, false⟩]

/-- At the return, L3 gives `y`: the result is the status of `y`, and `*j` has the total of `y`
and its other fields unchanged. -/
def post (x : In) (j src : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y.status = [r] ∧
    Mem.has policy m ⟨j, Encode.encode (record x src y.total), true⟩

/-- For each input `x` in the contract and each record address `j` and array address `src`, each
call `toyJob(j)` returns the result of L3. -/
def JobStatement : Prop :=
  ∀ x, C x → ∀ j src : BitVec 64, toyJob.Call [⟨.W64, j⟩] (objects x j src) (post x j src)

end Lift.Spike.JobStatement
