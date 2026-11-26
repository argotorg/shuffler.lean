module

public import Lift.Sem.StackRoom
public import Kraken.SeparationMem
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

namespace Lift.Sem.SysV

open Lift.P2.Total

/-! ## The input memory of a frame that reads the heap (PIL-HEAP)

The model of the frame form reads the heap in the input memory of `rep`. The machine reads the heap in the memory after the
pushes, which is the memory of the entry `s` outside the `n` bytes of the room (`Outside`). `Hidden s n m`: `m` is the memory of
`s` with the room unmapped. A read that succeeds in `m` meets no byte of the room, so the machine reads the same value
(`Hidden.readRam`). `hide s n` is such a memory. -/

/-- `m` is the memory of `s` with the `n` bytes below `rsp` unmapped. -/
def Hidden (s : MachineState) (n : Nat) (m : DataMem) : Prop :=
  Outside s n m ∧ ∀ x, Below s.data.regs.rsp.toBitVec n x → m.get? x = none

/-- The memory of `s` with the `n` bytes below `rsp` removed. -/
def hide (s : MachineState) (n : Nat) : DataMem :=
  s.data.dmem.filter fun x _ => !decide ((x - (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 n)).toNat < n)

theorem hide_hidden (s : MachineState) (n : Nat) : Hidden s n (hide s n) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> unfold Below at hx <;> unfold hide <;>
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter', hx, decide_true, decide_false,
      Bool.not_true, Bool.not_false] <;>
    cases s.data.dmem[x]? <;> rfl

/-- A read that succeeds in the memory of `s` with the room unmapped is the read in each memory that has the bytes of `s`
outside the room. The policy and the address are equations, so that a proof gives them in the terms of the model. -/
theorem Hidden.readRam {policy policy' : CpuPolicy} {s : MachineState} {n : Nat} {a m : DataMem}
    {addr addr' : BitVec 64} {w : Width} {v : w.type}
    (hh : Hidden s n a) (hp : policy' = policy) (hr : Lift.P2.Total.readRam policy' a addr' w = .ok v)
    (he : addr' = addr) (ho : Outside s n m) : Lift.P2.Total.readRam policy m addr w = .ok v := by
  subst hp he
  have hl : Mem.loadInt a addr' w.bytes ≠ none := by
    intro e
    unfold Lift.P2.Total.readRam at hr
    split at hr
    · rw [e] at hr; cases hr
    · cases hr
  obtain ⟨bs, hbs⟩ : ∃ bs, a.loadBytes addr' w.bytes = some bs := by
    unfold Mem.loadInt at hl
    cases h : a.loadBytes addr' w.bytes with
    | none => rw [h] at hl; exact absurd rfl hl
    | some bs => exact ⟨bs, rfl⟩
  obtain ⟨hlen, hget⟩ := Mem.loadBytes_eq_some_iff.mp hbs
  have e : Mem.loadInt m addr' w.bytes = Mem.loadInt a addr' w.bytes := Mem.loadInt_congr fun i hi => by
    have hs := hget i (hlen ▸ hi)
    have hnb : ¬ Below s.data.regs.rsp.toBitVec n (addr' + BitVec.ofNat 64 i) := by
      intro hb
      rw [hh.2 _ hb] at hs
      cases hs
    rw [ho _ hnb, hh.1 _ hnb]
  unfold Lift.P2.Total.readRam at hr ⊢
  rw [e]
  by_cases hp : policy'.permits (.read addr' w) = true
  · simp only [hp, ite_true] at hr ⊢
    cases hl2 : Mem.loadInt a addr' w.bytes <;> simp only [hl2] at hr ⊢
    · cases hr
    · exact hr
  · simp only [hp] at hr
    cases hr

/-- The two cases of the outer `if` of an equation (the branch of a model step whose condition can have an `if` inside). -/
theorem ite_cases {α : Sort _} {c : Prop} [Decidable c] {a b n : α} (h : (if c then a else b) = n) :
    (c ∧ a = n) ∨ (¬ c ∧ b = n) := by
  by_cases hc : c
  · exact .inl ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · exact .inr ⟨hc, by rw [if_neg hc] at h; exact h⟩

/-- A read that meets the room fails in the memory with the room unmapped (the negative case of `Hidden.readRam`). -/
theorem Hidden.readRam_below {policy : CpuPolicy} {s : MachineState} {n : Nat} {a : DataMem} {addr : BitVec 64}
    {w : Width} {v : w.type} (hh : Hidden s n a) (hb : Below s.data.regs.rsp.toBitVec n addr) :
    Lift.P2.Total.readRam policy a addr w ≠ .ok v := by
  intro hr
  unfold Lift.P2.Total.readRam at hr
  have hz : Mem.loadInt a addr w.bytes = none := by
    have h0 : a.get? (addr + BitVec.ofNat 64 0) = none := by rw [BitVec.add_zero]; exact hh.2 _ hb
    have hw : 0 < w.bytes := by cases w <;> decide
    unfold Mem.loadInt
    cases h : a.loadBytes addr w.bytes with
    | none => rfl
    | some bs =>
      obtain ⟨hlen, hget⟩ := Mem.loadBytes_eq_some_iff.mp h
      have := hget 0 (by omega)
      rw [h0] at this
      cases this
  split at hr
  · rw [hz] at hr; cases hr
  · cases hr

end Lift.Sem.SysV
