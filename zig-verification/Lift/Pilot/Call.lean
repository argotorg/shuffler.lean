module

public import Lift.Trusted.Call

@[expose] public section

/-! The call form of the shuffler: `Fn.Call` with the permission of the accesses of each width at
each byte of the objects and of the stack room. `Mem.has` permits the exact (address, width) of each
field of an object. The compiled code reads the same bytes with other widths (a slot as 8 bytes and
its `kind` as 1 byte), and no field list permits all of them. The definitions are in the namespace
`Lift.Trusted` so that `f.EntryB` and `f.CallB` are the dot notation of `Fn`. They are not in
`Lift/Trusted`, but each statement with `Fn.CallB` depends on them for its meaning: they are
statement terms (decision D24). -/

namespace Lift.Trusted

open Lift.P2.Total Lift.Sem

/-- The policy permits the read of each width, at each byte offset `k` of `[a, a + n)` where the
access stays in the range, and, when `wr` is `true`, the write too. The sum `a + k` is the sum of
`BitVec 64`, as in `Mem.has`. No width has 0 bytes, so the range of `n = 0` bytes needs no access. -/
def PermitsRange (policy : CpuPolicy) (a : BitVec 64) (n : Nat) (wr : Bool) : Prop :=
  ∀ (k : Nat) (w : Width), k + w.bytes ≤ n →
    policy.permits (.read (a + BitVec.ofNat 64 k) w) = true ∧
      (wr = true → policy.permits (.write (a + BitVec.ofNat 64 k) w) = true)

/-- A call of `f` as `Fn.Entry`, and the policy permits the accesses of each width in each object
(for write too when the object is writable) and in the stack room `[rsp - f.room, rsp)`, which
`Fn.stack` has. The return word at `rsp` has no permission here: a `ret` reads it as 8 bytes, which
`Fn.Entry.ret` permits. -/
def Fn.EntryB (f : Fn) (policy : CpuPolicy) (args : List Field) (objs : List Object)
    (ra : BitVec 64) (s : MachineState) : Prop :=
  f.Entry policy args objs ra s ∧
    (∀ o ∈ objs, PermitsRange policy o.addr o.size o.writable) ∧
    PermitsRange policy (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 f.room) f.room true

/-- `Fn.Call` with `Fn.EntryB` in place of `Fn.Entry`: each execution of each call of `f` from a
state of `Fn.EntryB` is finite, has no fault, and ends in a return state. -/
def Fn.CallB (f : Fn) (args : List Field) (objs : List Object)
    (post : CpuPolicy → Field → DataMem → Prop) : Prop :=
  ∀ policy ra s, f.EntryB policy args objs ra s →
    Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s

/-- `Fn.CallB` with two read-only 64-bit stack arguments at `rsp + 8` and `rsp + 16`.
The object and stack-room permissions come from `EntryB`; the two argument words have
the exact read permissions of `Mem.has`. -/
def Fn.Call8B (f : Fn) (args : List Field) (g h : BitVec 64) (objs : List Object)
    (post : CpuPolicy → Field → DataMem → Prop) : Prop :=
  ∀ policy ra s, f.EntryB policy args objs ra s →
    Mem.has policy s.data.dmem
      ⟨s.data.regs.rsp.toBitVec + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩ →
    Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s

/-- `Fn.Call` gives `Fn.CallB`: `Fn.EntryB` has more hypotheses. -/
theorem Fn.CallB.of_call {f : Fn} {args : List Field} {objs : List Object}
    {post : CpuPolicy → Field → DataMem → Prop} (h : f.Call args objs post) :
    f.CallB args objs post :=
  fun policy ra s e => h policy ra s e.1

/-- A range inside a permitted range is permitted, with the same `wr` or a weaker one. The range
`[a + j, a + j + n')` is inside `[a, a + n)` when `j + n' ≤ n`. -/
theorem PermitsRange.mono {policy : CpuPolicy} {a : BitVec 64} {n j n' : Nat} {wr wr' : Bool}
    (h : PermitsRange policy a n wr) (hj : j + n' ≤ n) (hw : wr' = true → wr = true) :
    PermitsRange policy (a + BitVec.ofNat 64 j) n' wr' := by
  intro k w hk
  have e : a + BitVec.ofNat 64 j + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (j + k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [e]
  exact ⟨(h (j + k) w (by omega)).1, fun h' => (h (j + k) w (by omega)).2 (hw h')⟩

/-- The read of width `w` at offset `k` is permitted when `k + w.bytes ≤ n`. -/
theorem PermitsRange.read {policy : CpuPolicy} {a : BitVec 64} {n : Nat} {wr : Bool}
    (h : PermitsRange policy a n wr) {k : Nat} {w : Width} (hk : k + w.bytes ≤ n) :
    policy.permits (.read (a + BitVec.ofNat 64 k) w) = true :=
  (h k w hk).1

/-- The write of width `w` at offset `k` is permitted when `k + w.bytes ≤ n` and `wr` is `true`. -/
theorem PermitsRange.write {policy : CpuPolicy} {a : BitVec 64} {n : Nat} {wr : Bool}
    (h : PermitsRange policy a n wr) {k : Nat} {w : Width} (hk : k + w.bytes ≤ n)
    (hw : wr = true) : policy.permits (.write (a + BitVec.ofNat 64 k) w) = true :=
  (h k w hk).2 hw

end Lift.Trusted
