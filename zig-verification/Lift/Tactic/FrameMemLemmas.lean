module

public import Lift.Sem.SepRoom
public import Lift.Sem.Hidden
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

/-! The lemmas of `frame_mem` (`Lift/Tactic/FrameMem.lean`), for a memory in separation form
(`m =⋆ slot ⋆ … ⋆ Eq rest`, `Lift/Sem/SepRoom.lean`). As in `Lift/Tactic/MemLemmas.lean`, an address
is a hypothesis `a = a₀`, so that the tactic proves it by the linear form of the addresses, and a
side condition on `k` is one `decide` fact. The permits are not in the slots: they come from a
`SysV.StackRoom` fact, as for `room_mem`. -/

/-! ## The words of a room that are mapped

`Mapped sp j n m`: the words at `sp - k` for `j ≤ k ≤ n` and `8 ∣ k` are mapped in `m`. The room of a
callee needs its words mapped in the memory at the call; the `post` of the callee says that they stay
mapped. A store only adds bytes, so a store never unmaps a word (`Mapped.storeInt`, with no condition
on the address). -/

namespace Lift.Sem.SysV

open Lift.P2.Total

/-- The words at `sp - k` for `j ≤ k ≤ n` and `8 ∣ k` are mapped in `m`. -/
def Mapped (sp : BitVec 64) (j n : Nat) (m : DataMem) : Prop :=
  ∀ k, j ≤ k → k ≤ n → 8 ∣ k → Mem.loadInt m (sp - BitVec.ofNat 64 k) 8 ≠ none

theorem Mapped.mono {sp : BitVec 64} {j j' n n' : Nat} {m : DataMem} (h : Mapped sp j n m)
    (hk : decide (j ≤ j' ∧ n' ≤ n) = true) : Mapped sp j' n' m := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true hk
  exact fun k a b c => h k (by omega) (by omega) c

/-- No word: `n < j`. -/
theorem Mapped.of_lt {sp : BitVec 64} {j n : Nat} {m : DataMem} (hk : decide (n < j) = true) :
    Mapped sp j n m := by
  have := of_decide_eq_true hk
  exact fun k a b _ => absurd (Nat.le_trans a b) (by omega)

/-- One word of `Mapped`. -/
theorem Mapped.loadInt {sp : BitVec 64} {k : Nat} {m : DataMem} {a : BitVec 64}
    (ha : a = sp - BitVec.ofNat 64 k) (hd : decide (8 ∣ k) = true) (h : Mapped sp k k m) :
    Mem.loadInt m a 8 ≠ none := by
  subst ha
  exact h k (Nat.le_refl k) (Nat.le_refl k) (of_decide_eq_true hd)

/-- The words of a room are mapped in the start memory. -/
theorem StackRoom.mapped {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : StackRoom policy s n) : Mapped s.data.regs.rsp.toBitVec 8 n s.data.dmem :=
  fun k a b c => (h k a b c).2.2

theorem allSome_ne_none {α : Type} :
    ∀ {l : List (Option α)}, (∀ x ∈ l, x.isSome) → l.allSome ≠ none
  | [], _ => by simp [List.allSome]
  | x :: l, h => by
    obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    have := allSome_ne_none (l := l) (fun z hz => h z (by simp [hz]))
    simp only [List.allSome, List.mapM_cons, id] at this ⊢
    intro hn
    apply this
    cases hl : l.mapM id with
    | none => rfl
    | some _ => simp [hl] at hn

/-- A store keeps each mapped word mapped. -/
theorem loadInt_storeInt_ne_none {m : DataMem} {a b : BitVec 64} {w k : Nat} {v : Int}
    (h : Mem.loadInt m b k ≠ none) : Mem.loadInt (Mem.storeInt m a w v) b k ≠ none := by
  obtain ⟨xs, hx⟩ := Option.ne_none_iff_exists'.mp h
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hx
  obtain ⟨bs, hb, -⟩ := hx
  have hl := List.allSome_eq_map_some hb
  simp only [Mem.loadInt, Mem.loadBytes, ne_eq, Option.map_eq_none_iff]
  apply allSome_ne_none
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hm : (Std.ExtHashMap.get? m (b + BitVec.ofNat 64 i)) ∈ List.map some bs := by
    rw [← hl]; exact List.mem_map_of_mem hi
  obtain ⟨y, -, hy⟩ := List.mem_map.mp hm
  rw [Mem.get?_storeInt]
  have hmem : b + BitVec.ofNat 64 i ∈ m :=
    Std.ExtHashMap.isSome_getElem?_iff_mem.mp (by
      rw [← Std.ExtHashMap.get?_eq_getElem?, ← hy]; rfl)
  simp [hmem]

theorem Mapped.storeInt {sp : BitVec 64} {j n : Nat} {m : DataMem} (h : Mapped sp j n m)
    (a : BitVec 64) (w : Nat) (v : Int) : Mapped sp j n (Mem.storeInt m a w v) :=
  fun k a' b c => loadInt_storeInt_ne_none (h k a' b c)

/-- The room of a callee that starts `j` bytes below `rsp` of `s`: its permits are those of the room
of `s`, and its words are mapped in the memory of the call (`hm`). -/
theorem StackRoom.callee {policy : CpuPolicy} {s t : MachineState} {n n' j : Nat}
    (room : StackRoom policy s n)
    (hsp : t.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 j)
    (hk : decide (j + n' ≤ n ∧ 8 ∣ j) = true)
    (hm : Mapped s.data.regs.rsp.toBitVec (j + 8) (j + n') t.data.dmem) : StackRoom policy t n' := by
  obtain ⟨hj, hd⟩ := of_decide_eq_true hk
  intro k hk8 hkn hdk
  have e : t.data.regs.rsp.toBitVec - BitVec.ofNat 64 k =
      s.data.regs.rsp.toBitVec - BitVec.ofNat 64 (j + k) := by
    rw [hsp, BitVec.sub_sub, BitVec.ofNat_add, BitVec.add_comm]
  obtain ⟨h1, h2, -⟩ := room (j + k) (by omega) (by omega) (Nat.dvd_add hd hdk)
  rw [e]
  exact ⟨h1, h2, hm _ (by omega) (by omega) (Nat.dvd_add hd hdk)⟩

/-- The words of the room of `R` after the return of a callee. `h` and `mp` are the `post` of the
callee that was called in `s'` (`rsp` of `s'` is `R - j`, its room is the `n'` bytes below). A word
inside the room of the callee is mapped by `mp`. Another word does not meet the room (`j` and `n'`
are multiples of 8), so it is as mapped as in the memory of the call (`hm`), which includes the return
word at `rsp` of `s'`. -/
theorem Mapped.after {s' : MachineState} {n' j lo hi : Nat} {m : DataMem} {R : BitVec 64}
    (h : Outside s' n' m) (hs : s'.data.regs.rsp.toBitVec = R - BitVec.ofNat 64 j)
    (mp : Mapped s'.data.regs.rsp.toBitVec 8 n' m)
    (hk : decide (8 ∣ j ∧ 8 ∣ n' ∧ j + n' + 8 ≤ 2 ^ 64 ∧ hi < 2 ^ 64) = true)
    (hm : Mapped R lo hi s'.data.dmem) : Mapped R lo hi m := by
  obtain ⟨hj, hn, hb, hh⟩ := of_decide_eq_true hk
  intro k hlo hhi hd
  by_cases hin : j + 8 ≤ k ∧ k ≤ j + n'
  · have e : s'.data.regs.rsp.toBitVec - BitVec.ofNat 64 (k - j) = R - BitVec.ofNat 64 k := by
      rw [hs, BitVec.sub_sub]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [← e]
    exact mp (k - j) (by omega) (by omega) (by omega)
  · have e : Mem.loadInt m (R - BitVec.ofNat 64 k) 8 =
        Mem.loadInt s'.data.dmem (R - BitVec.ofNat 64 k) 8 :=
      Mem.loadInt_congr fun i hi => h _ (by
        unfold Below
        rw [hs]
        have : k ≤ j ∨ j + n' + 8 ≤ k := by omega
        rcases this with hk | hk <;> bv_omega)
    rw [e]
    exact hm k hlo hhi hd

end Lift.Sem.SysV

namespace Lift.Tactic.Frame

open Lift.P2.Total Lift.Sem Std.ExtHashMap

/-- A read of the slot that holds `v`. -/
theorem readRam_slot {policy : CpuPolicy} {m : DataMem} {a a₀ v : BitVec 64} {F : DataMem → Prop}
    (hm : m =⋆ SysV.Word a₀ v ⋆ F) (ha : a = a₀) (hp : policy.permits (.read a .W64) = true) :
    readRam policy m a .W64 = .ok v := by
  subst ha
  exact SysV.readRam_sep hm hp

/-- A write of a slot of 8 bytes is the store of the word. -/
theorem writeRam_slot {policy : CpuPolicy} {m M' : DataMem} {a a₀ v : BitVec 64} {bs : List UInt8}
    {F : DataMem → Prop} (hm : m =⋆ Mem.Bytes a₀ bs ⋆ F) (ha : a = a₀) (hl : bs.length = 8)
    (hp : policy.permits (.write a .W64) = true) (e : Mem.storeInt m a 8 v.toInt = M') :
    writeRam policy m a .W64 v = .ok M' := by
  subst ha e
  exact (SysV.writeRam_sep hm hp hl v).1

/-- After the store of a word on a slot of 8 bytes, the slot holds the word. -/
theorem storeInt_slot {m : DataMem} {a a₀ : BitVec 64} {bs : List UInt8} {F : DataMem → Prop}
    (hm : m =⋆ Mem.Bytes a₀ bs ⋆ F) (ha : a = a₀) (hl : bs.length = 8) (v : BitVec 64) :
    Mem.storeInt m a 8 v.toInt =⋆ SysV.Word a₀ v ⋆ F := by
  subst ha
  exact Mem.storeInt_sep a 8 bs F m ⟨hm, hl⟩ v.toInt

/-- The return word at `rsp`: outside the room it is the word of the start memory. -/
theorem readRam_ret {policy : CpuPolicy} {s : MachineState} {n : Nat} {m : DataMem}
    {a u : BitVec 64} (_room : SysV.StackRoom policy s n) (ha : a = s.data.regs.rsp.toBitVec)
    (hn : decide (n + 8 ≤ 2 ^ 64) = true) (h : SysV.Outside s n m)
    (hr : readRam policy s.data.dmem s.data.regs.rsp.toBitVec .W64 = .ok u) :
    readRam policy m a .W64 = .ok u := by
  subst ha
  exact h.readRam_ret (of_decide_eq_true hn) hr

/-- A read of the value `u` from a read of `v` and the equation of the two values: the stack argument of a call (ARGS8),
whose read `frame_call` proves and whose value the closer of the register equations proves. -/
theorem readRam_arg {policy : CpuPolicy} {m : DataMem} {a v : BitVec 64} {u : UInt64}
    (h : readRam policy m a .W64 = .ok v) (e : UInt64.ofBitVec v = u) : readRam policy m a .W64 = .ok u.toBitVec := by
  subst e
  exact h

/-- A slot at `sp - k` with `8 ≤ k ≤ n` that holds a word is in the room. -/
theorem inRoom_word {sp : BitVec 64} {n : Nat} {v : BitVec 64} (k : Nat)
    (hk : decide (8 ≤ k ∧ k ≤ n) = true) {a : BitVec 64} (ha : a = sp - BitVec.ofNat 64 k) :
    SysV.InRoom sp n (SysV.Word a v) := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true hk
  subst ha
  exact SysV.InRoom.word ⟨h1, h2⟩

/-- A slot at `sp - k` with `8 ≤ k ≤ n` and bytes of length 8 is in the room. -/
theorem inRoom_bytes {sp : BitVec 64} {n : Nat} {bs : List UInt8} (k : Nat)
    (hk : decide (8 ≤ k ∧ k ≤ n) = true) {a : BitVec 64} (ha : a = sp - BitVec.ofNat 64 k)
    (hl : bs.length = 8) : SysV.InRoom sp n (Mem.Bytes a bs) := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true hk
  subst ha
  exact SysV.InRoom.bytes hl h1 h2

/-! ## After a callee

`s'` is the state at the entry of a callee with `n` bytes of room below its `rsp`, which is `R - j`.
`h : Outside s' n m` is the `post` of the callee: the memory `m` of its return. -/

/-- A word at `R - k` that the room of the callee does not meet has the same read in `m` as in the
memory of the entry of the callee: the word is above the `rsp` of the callee (`k ≤ j`) or below its
room (`j + n + 8 ≤ k`). -/
theorem readRam_far {policy : CpuPolicy} {s' : MachineState} {n j k : Nat} {m : DataMem}
    {R a v : BitVec 64} (h : SysV.Outside s' n m)
    (hs : s'.data.regs.rsp.toBitVec = R - BitVec.ofNat 64 j) (ha : a = R - BitVec.ofNat 64 k)
    (hk : decide ((k ≤ j ∨ j + n + 8 ≤ k) ∧ j + n + 8 ≤ 2 ^ 64 ∧ k < 2 ^ 64) = true)
    (hr : readRam policy s'.data.dmem a .W64 = .ok v) : readRam policy m a .W64 = .ok v := by
  subst ha
  obtain ⟨hk, hj, hk2⟩ := of_decide_eq_true hk
  refine SysV.readRam_of_loadInt (Mem.loadInt_congr fun i hi => h _ ?_) hr
  unfold SysV.Below
  rw [hs]
  rcases hk with hk | hk <;> bv_omega

/-- `Outside` of the caller after the return of a callee whose room is inside the room of the
caller. -/
theorem outside_compose {s s' : MachineState} {n n' j : Nat} {m : DataMem} {R : BitVec 64}
    (h' : SysV.Outside s' n' m) (hs : s'.data.regs.rsp.toBitVec = R - BitVec.ofNat 64 j)
    (hR : s.data.regs.rsp.toBitVec = R) (h : SysV.Outside s n s'.data.dmem)
    (hk : decide (j + n' ≤ n ∧ n < 2 ^ 64) = true) : SysV.Outside s n m := by
  obtain ⟨hk, hn⟩ := of_decide_eq_true hk
  intro x hx
  refine (h' x fun hb => hx ?_).trans (h x hx)
  unfold SysV.Below at hb ⊢
  rw [hs] at hb
  rw [hR]
  bv_omega

end Lift.Tactic.Frame
