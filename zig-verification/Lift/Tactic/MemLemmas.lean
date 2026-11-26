module

public import Lift.Sem.StackRoom
public import VerifiedNix.MemSimp

@[expose] public section

/-! The lemmas of `room_mem` (`Lift/Tactic/Mem.lean`). Each lemma has the form that the tactic
applies: the data (`k`) comes first, a side condition on `k` is one `decide` fact, and an address
is a hypothesis `a = ...`, so that the tactic proves it by the linear form of the addresses. -/

namespace Lift.Tactic.Room

open Lift.P2.Total Lift.Sem

/-- Two addresses with the same atoms and a constant difference `0` are equal. -/
theorem addr_eq {w : Nat} (ρ : List (BitVec w)) (x y : MemSimp.Addr)
    (hc : x.sameAtoms ρ y = true) (h : ((x.const - y.const) % (2 ^ w : Nat) == 0) = true) :
    x.denote ρ = y.denote ρ := by
  have h0 : BitVec.ofInt w (x.const - y.const) = 0 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofInt, beq_iff_eq.mp h]; rfl)
  have hs := MemSimp.Addr.sub_denote hc
  rw [h0] at hs
  grind

/-! ## The room -/

/-- The permit of a write at the slot `rsp - k`. -/
theorem permits_write {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : SysV.StackRoom policy s n) (k : Nat) (hk : decide (8 ≤ k ∧ k ≤ n ∧ 8 ∣ k) = true)
    {a : BitVec 64} (ha : a = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) :
    policy.permits (.write a .W64) = true := by
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true hk
  subst ha
  exact (h k h1 h2 h3).1

/-- The permit of a read at the slot `rsp - k`. -/
theorem permits_read {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : SysV.StackRoom policy s n) (k : Nat) (hk : decide (8 ≤ k ∧ k ≤ n ∧ 8 ∣ k) = true)
    {a : BitVec 64} (ha : a = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) :
    policy.permits (.read a .W64) = true := by
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true hk
  subst ha
  exact (h k h1 h2 h3).2.1

/-- The word at the slot `rsp - k` of the start memory is mapped. -/
theorem mapped_slot {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : SysV.StackRoom policy s n) (k : Nat) (hk : decide (8 ≤ k ∧ k ≤ n ∧ 8 ∣ k) = true)
    {a : BitVec 64} (ha : a = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) :
    Mem.loadInt s.data.dmem a 8 ≠ none := by
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true hk
  subst ha
  exact (h k h1 h2 h3).2.2

/-! ## Reads, writes and mapped words -/

/-- A permitted read of a word that the memory holds as the bytes of `v`. -/
theorem readRam_of_stored {policy : CpuPolicy} {m : DataMem} {a v : BitVec 64}
    (hp : policy.permits (.read a .W64) = true)
    (hl : Mem.loadInt m a 8 = some (Int.ofBytes (Int.toBytes 8 v.toInt))) :
    readRam policy m a .W64 = .ok v := by
  simp [Lift.P2.Total.readRam, hp, hl, Width.bytes, Width.bits,
    BitVec.ofInt_ofBytes_toBytes_64]

/-- A read gives the value of a read of the same word (up to the spelling of the address) in a
memory `m`, when `m'` and `m` hold the same bytes there. -/
theorem readRam_of_hyp {policy : CpuPolicy} {m m' : DataMem} {a a₀ v : BitVec 64}
    (h : readRam policy m a₀ .W64 = .ok v) (ha : a = a₀)
    (e : Mem.loadInt m' a 8 = Mem.loadInt m a 8) : readRam policy m' a .W64 = .ok v := by
  subst ha
  exact SysV.readRam_of_loadInt e h

/-- A permitted write of a mapped word is the store of the word. -/
theorem writeRam_of_store {policy : CpuPolicy} {m M' : DataMem} {a v : BitVec 64}
    (hp : policy.permits (.write a .W64) = true) (hm : Mem.loadInt m a 8 ≠ none)
    (e : Mem.storeInt m a 8 v.toInt = M') : writeRam policy m a .W64 v = .ok M' := by
  subst e
  exact SysV.writeRam_of_mapped hp hm

/-- The same word (up to the spelling of the address) is mapped. -/
theorem mapped_of_hyp {m : DataMem} {a a₀ : BitVec 64} (h : Mem.loadInt m a₀ 8 ≠ none)
    (ha : a = a₀) : Mem.loadInt m a 8 ≠ none := by
  subst ha
  exact h

/-- Two stores are equal when the memories, the addresses and the values are. -/
theorem storeInt_congr {m m' : DataMem} {a a' : BitVec 64} {n : Nat} {v v' : Int}
    (hm : m = m') (ha : a = a') (hv : v = v') :
    Mem.storeInt m a n v = Mem.storeInt m' a' n v' := by
  subst hm ha hv
  rfl

/-! ## The bytes outside the room -/

/-- A store at the slot `rsp - k` keeps the bytes outside the room. -/
theorem outside_store {s : MachineState} {n : Nat} {m : DataMem} (k : Nat)
    (hk : decide (8 ≤ k ∧ k ≤ n) = true) (h : SysV.Outside s n m) {a : BitVec 64}
    (ha : a = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) (v : Int) :
    SysV.Outside s n (Mem.storeInt m a 8 v) := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true hk
  subst ha
  exact h.storeInt h1 h2 v

/-- The return word at `rsp`: outside the room it is the word of the start memory. -/
theorem loadInt_of_outside {s : MachineState} {n : Nat} {m : DataMem}
    (h : SysV.Outside s n m) (hn : decide (n + 8 ≤ 2 ^ 64) = true) {a : BitVec 64}
    (ha : a = s.data.regs.rsp.toBitVec) :
    Mem.loadInt m a 8 = Mem.loadInt s.data.dmem a 8 := by
  subst ha
  exact h.loadInt_ret (of_decide_eq_true hn)

end Lift.Tactic.Room
