module

public import Lift.Sem.SysV
public import Lift.P2.Total.Footprint

@[expose] public section

/-! The stack room of a call: the words below `rsp` that the function and its callees can push.
A push is a `writeRam` of a word; it succeeds when the policy permits the write and the word is
mapped (`Lift/P2/Total/Memory.lean`). The room also permits the read of each word, for the pops
and for the return word of each callee. The words are at `rsp - k` with `8 ∣ k`. The addresses are
modulo `2^64`, as in Kraken. -/

namespace Lift.Sem.SysV

open Lift.P2.Total

/-- For each `k` in `[8, n]` with `8 ∣ k`, the policy permits the write and the read of the word at
`rsp - k` of `s`, and the word is mapped. -/
def StackRoom (policy : CpuPolicy) (s : MachineState) (n : Nat) : Prop :=
  ∀ k, 8 ≤ k → k ≤ n → 8 ∣ k →
    policy.permits (.write (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64) = true ∧
    policy.permits (.read (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64) = true ∧
    Mem.loadInt s.data.dmem (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 ≠ none

/-- The byte `x` is one of the `n` bytes below `sp`, modulo `2^64`. -/
def Below (sp : BitVec 64) (n : Nat) (x : BitVec 64) : Prop :=
  (x - (sp - BitVec.ofNat 64 n)).toNat < n

/-- Each byte of `m` that is not one of the `n` bytes below `rsp` of `s` is the byte of `s`. -/
def Outside (s : MachineState) (n : Nat) (m : DataMem) : Prop :=
  ∀ x, ¬ Below s.data.regs.rsp.toBitVec n x → m.get? x = s.data.dmem.get? x

/-! ## Writes and reads of one word -/

/-- A permitted write of a mapped word is the store of the word. -/
theorem writeRam_of_mapped {policy : CpuPolicy} {m : DataMem} {a v : BitVec 64}
    (hp : policy.permits (.write a .W64) = true) (hm : Mem.loadInt m a 8 ≠ none) :
    writeRam policy m a .W64 v = .ok (Mem.storeInt m a 8 v.toInt) := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hm
  simp [Lift.P2.Total.writeRam, hp, Width.bytes, hw]

/-- A permitted read of a stored word gives its value. -/
theorem readRam_storeInt {policy : CpuPolicy} {m : DataMem} {a v : BitVec 64}
    (hp : policy.permits (.read a .W64) = true) :
    readRam policy (Mem.storeInt m a 8 v.toInt) a .W64 = .ok v := by
  simp [Lift.P2.Total.readRam, hp, Width.bytes, Width.bits, Mem.loadInt_storeInt_64,
    BitVec.ofInt_ofBytes_toBytes_64]

/-- After a store, the word at the same address is mapped. -/
theorem mapped_storeInt (m : DataMem) (a : BitVec 64) (v : Int) :
    Mem.loadInt (Mem.storeInt m a 8 v) a 8 ≠ none := by
  simp [Mem.loadInt_storeInt_64]

/-- Two words at `sp - k` and `sp - j` with `j + 8 ≤ k` do not meet. -/
theorem slot_disjoint (sp : BitVec 64) {j k : Nat} (hjk : j + 8 ≤ k) (hk : k + 8 ≤ 2 ^ 64) :
    ByteDisjoint (sp - BitVec.ofNat 64 k) 8 (sp - BitVec.ofNat 64 j) 8 := by
  intro i hi i' hi'
  bv_omega

/-- A word at `sp - k` with `8 ≤ k` does not meet the word at `sp` (the return word). -/
theorem ret_disjoint (sp : BitVec 64) {k : Nat} (hk8 : 8 ≤ k) (hk : k + 8 ≤ 2 ^ 64) :
    ByteDisjoint (sp - BitVec.ofNat 64 k) 8 sp 8 := by
  intro i hi i' hi'
  bv_omega

/-- A read gives the same value from each memory with the same word. -/
theorem readRam_of_loadInt {policy : CpuPolicy} {m m' : DataMem} {a u : BitVec 64}
    (e : Mem.loadInt m' a 8 = Mem.loadInt m a 8) (h : readRam policy m a .W64 = .ok u) :
    readRam policy m' a .W64 = .ok u := by
  cases hp : policy.permits (.read a .W64) <;> cases hl : Mem.loadInt m a 8 <;>
    simp_all [Lift.P2.Total.readRam, Width.bytes]

/-- A store does not change a read of a word that it does not meet. -/
theorem readRam_storeInt_of_disjoint {policy : CpuPolicy} {m : DataMem} {a b u : BitVec 64}
    {v : Int} (h : ByteDisjoint a 8 b 8) (hr : readRam policy m b .W64 = .ok u) :
    readRam policy (Mem.storeInt m a 8 v) b .W64 = .ok u :=
  readRam_of_loadInt (loadInt_storeInt_separate _ _ _ _ _ _ h) hr

/-- A store does not change a load of a word that it does not meet. -/
theorem loadInt_storeInt_of_disjoint {m : DataMem} {a b : BitVec 64} {v : Int}
    (h : ByteDisjoint a 8 b 8) :
    Mem.loadInt (Mem.storeInt m a 8 v) b 8 = Mem.loadInt m b 8 :=
  loadInt_storeInt_separate m a b 8 8 v h

/-- A store keeps each mapped word that it does not meet mapped. -/
theorem mapped_storeInt_of_disjoint {m : DataMem} {a b : BitVec 64} {v : Int}
    (h : ByteDisjoint a 8 b 8) (hm : Mem.loadInt m b 8 ≠ none) :
    Mem.loadInt (Mem.storeInt m a 8 v) b 8 ≠ none := by
  rw [loadInt_storeInt_of_disjoint h]
  exact hm

/-! ## The room -/

/-- A push to the word at `rsp - k` in the room succeeds, on each memory where the word is mapped. -/
theorem StackRoom.writeRam {policy : CpuPolicy} {s : MachineState} {n k : Nat}
    (h : StackRoom policy s n) (hk8 : 8 ≤ k) (hkn : k ≤ n) (hd : 8 ∣ k) {m : DataMem}
    (hm : Mem.loadInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 ≠ none) (v : BitVec 64) :
    writeRam policy m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64 v =
      .ok (Mem.storeInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 v.toInt) :=
  writeRam_of_mapped (h k hk8 hkn hd).1 hm

/-- The read of a pushed word at `rsp - k` in the room gives its value. -/
theorem StackRoom.readRam {policy : CpuPolicy} {s : MachineState} {n k : Nat}
    (h : StackRoom policy s n) (hk8 : 8 ≤ k) (hkn : k ≤ n) (hd : 8 ∣ k) (m : DataMem)
    (v : BitVec 64) :
    Lift.P2.Total.readRam policy (Mem.storeInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 v.toInt)
      (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64 = .ok v :=
  readRam_storeInt (h k hk8 hkn hd).2.1

/-- A smaller room. -/
theorem StackRoom.mono {policy : CpuPolicy} {s : MachineState} {n n' : Nat}
    (h : StackRoom policy s n) (hn : n' ≤ n) : StackRoom policy s n' :=
  fun k hk8 hkn hd => h k hk8 (Nat.le_trans hkn hn) hd

/-! ## The bytes outside the room -/

theorem Outside.rfl (s : MachineState) (n : Nat) : Outside s n s.data.dmem :=
  fun _ _ => _root_.rfl

/-- A push to the word at `rsp - k` in the room keeps each byte outside the room. -/
theorem Outside.storeInt {s : MachineState} {n k : Nat} {m : DataMem} (h : Outside s n m)
    (hk8 : 8 ≤ k) (hkn : k ≤ n) (v : Int) :
    Outside s n (Mem.storeInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 v) := by
  intro x hx
  rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun i hi e => hx (by subst e; unfold Below; bv_omega)]
  exact h x hx

/-- Outside the room, the return word at `rsp` is that of `s`. -/
theorem Outside.loadInt_ret {s : MachineState} {n : Nat} {m : DataMem} (h : Outside s n m)
    (hn : n + 8 ≤ 2 ^ 64) :
    Mem.loadInt m s.data.regs.rsp.toBitVec 8 = Mem.loadInt s.data.dmem s.data.regs.rsp.toBitVec 8 :=
  Mem.loadInt_congr fun i hi => h _ (by unfold Below; bv_omega)

/-- Outside the room, a read of the return word at `rsp` gives the value of `s`. -/
theorem Outside.readRam_ret {policy : CpuPolicy} {s : MachineState} {n : Nat} {m : DataMem}
    {u : BitVec 64} (h : Outside s n m) (hn : n + 8 ≤ 2 ^ 64)
    (hr : Lift.P2.Total.readRam policy s.data.dmem s.data.regs.rsp.toBitVec .W64 = .ok u) :
    Lift.P2.Total.readRam policy m s.data.regs.rsp.toBitVec .W64 = .ok u :=
  readRam_of_loadInt (h.loadInt_ret hn) hr

end Lift.Sem.SysV
