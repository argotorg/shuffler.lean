module

public import Lift.Sem.StackRoom
public import Kraken.SeparationMem
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

/-! The stack room in separation form: `m =⋆ slot₁ ⋆ … ⋆ slotₖ ⋆ Eq rest`. A slot is the 8 bytes
of one word (`Mem.Bytes a bs`); `Word a v` is the slot that holds `v`. The frame `rest` is an exact
memory: the bytes of `m` that are not in a slot. Outside the room, `rest` is the memory of the
entry state (`Outside`). A push is a store into a slot (`writeRam_sep`); a pop or a read of a saved
register is a load from a slot (`readRam_sep`). `Outside.of_sep` gives the bytes outside the room
back from the separation form, when each slot is in the room (`InRoom`). -/

namespace Lift.Sem.SysV

open Lift.P2.Total Std.ExtHashMap

/-- The slot at `a` that holds the word `v`. -/
def Word (a v : BitVec 64) : DataMem → Prop := Mem.Bytes a (Int.toBytes 8 v.toInt)

/-- The bytes of `m` that are not among the `n` bytes at `a`. -/
def cut (m : DataMem) (a : BitVec 64) (n : Nat) : DataMem :=
  m.filter fun x _ => !decide ((x - a).toNat < n)

theorem getElem?_cut (m : DataMem) (a x : BitVec 64) (n : Nat) :
    (cut m a n)[x]? = if (x - a).toNat < n then none else m[x]? := by
  simp only [cut, getElem?_filter']
  by_cases h : (x - a).toNat < n <;> cases m[x]? <;>
    simp only [h, Option.filter_none, Option.filter_some, decide_true, decide_false,
      Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true]

private theorem add_toNat_sub (a x : BitVec 64) : a + BitVec.ofNat 64 (x - a).toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-! ## The carve of one slot -/

/-- A memory with the bytes `bs` at `a` is the slot of `bs` and the rest of the memory. -/
theorem eq_bytes_sep_cut {m : DataMem} {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a n = some bs) (hn : n ≤ 2 ^ 64) :
    Eq m = Mem.Bytes a bs ⋆ Eq (cut m a n) := by
  obtain ⟨hl, hb⟩ := Mem.loadBytes_eq_some_iff.mp h
  have hu : (bs.At a).union (cut m a n) = m := by
    apply ext_getElem?
    intro x
    rw [union_eq, getElem?_union, getElem?_cut, get?_At _ _ _ (hl ▸ hn)]
    by_cases hx : (x - a).toNat < n
    · have e := hb _ (hl ▸ hx)
      rw [add_toNat_sub, get?_eq_getElem?] at e
      rw [if_pos hx, Option.none_or, List.getElem?_eq_getElem (hl ▸ hx), e]
    · rw [if_neg hx, List.getElem?_eq_none (by omega), Option.or_none]
  have hi : (bs.At a).inter (cut m a n) = ∅ := by
    rw [eq_empty_iff_forall_not_mem]
    intro x hx
    rw [inter_eq, mem_inter_iff, mem_At_iff, mem_iff_isSome_getElem?, getElem?_cut] at hx
    obtain ⟨⟨i, hi, rfl⟩, h2⟩ := hx
    have : ((a + BitVec.ofNat 64 i) - a).toNat < n := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    rw [if_pos this] at h2
    simp at h2
  funext m'
  rw [sep_def]
  refine propext ⟨fun e => ⟨_, _, hu.trans e, hi, rfl, rfl⟩, ?_⟩
  rintro ⟨_, _, hu', -, rfl, rfl⟩
  exact hu.symm.trans hu'

/-- The cut of a range keeps each load of a range that it does not meet. -/
theorem loadBytes_cut {m : DataMem} {a b : BitVec 64} {n k : Nat} (h : ByteDisjoint a n b k) :
    (cut m a n).loadBytes b k = m.loadBytes b k := by
  refine Mem.loadBytes_congr fun j hj => ?_
  rw [get?_eq_getElem?, get?_eq_getElem?, getElem?_cut, ite_eq_right]
  intro hlt
  refine h _ hlt j hj ?_
  rw [add_toNat_sub]

/-- The cut of a word in the room keeps each byte outside the room. -/
theorem Outside.cut {s : MachineState} {n k : Nat} {m : DataMem} (h : Outside s n m)
    (hk8 : 8 ≤ k) (hkn : k ≤ n) :
    Outside s n (SysV.cut m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8) := by
  intro x hx
  rw [get?_eq_getElem?, getElem?_cut, ite_eq_right, ← get?_eq_getElem?]
  · exact h x hx
  · intro hlt
    exact hx (by unfold Below; bv_omega)

/-! ## The room as slots -/

/-- The permitted write of the word at `rsp - k` in the room. -/
theorem StackRoom.write {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : StackRoom policy s n) (k : Nat) (hk : 8 ≤ k ∧ k ≤ n ∧ 8 ∣ k := by decide) :
    policy.permits (.write (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64) = true :=
  (h k hk.1 hk.2.1 hk.2.2).1

/-- The permitted read of the word at `rsp - k` in the room. -/
theorem StackRoom.read {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : StackRoom policy s n) (k : Nat) (hk : 8 ≤ k ∧ k ≤ n ∧ 8 ∣ k := by decide) :
    policy.permits (.read (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) .W64) = true :=
  (h k hk.1 hk.2.1 hk.2.2).2.1

private theorem loadBytes_of_loadInt {m : DataMem} {a : BitVec 64} (h : Mem.loadInt m a 8 ≠ none) :
    ∃ bs, m.loadBytes a 8 = some bs := by
  cases hb : m.loadBytes a 8 with
  | none => exact absurd (by simp [Mem.loadInt, hb]) h
  | some bs => exact ⟨bs, rfl⟩

/-- A mapped word is a slot, and the memory without it. -/
theorem carve {m : DataMem} {a : BitVec 64} (h : Mem.loadInt m a 8 ≠ none) :
    ∃ bs, bs.length = 8 ∧ Eq m = Mem.Bytes a bs ⋆ Eq (cut m a 8) := by
  obtain ⟨bs, hb⟩ := loadBytes_of_loadInt h
  exact ⟨bs, Mem.length_of_loadBytes_eq_some hb, eq_bytes_sep_cut hb (by decide)⟩

/-- The cut of a word keeps each mapped word that it does not meet mapped. -/
theorem mapped_cut {m : DataMem} {a b : BitVec 64} (h : ByteDisjoint a 8 b 8)
    (hm : Mem.loadInt m b 8 ≠ none) : Mem.loadInt (cut m a 8) b 8 ≠ none := by
  simpa only [Mem.loadInt, loadBytes_cut h] using hm

/-- The room of 32 bytes as four slots and an exact frame, which is the memory of `s` outside
the room. -/
theorem StackRoom.sep32 {policy : CpuPolicy} {s : MachineState} (h : StackRoom policy s 32) :
    ∃ b₁ b₂ b₃ b₄ rest, b₁.length = 8 ∧ b₂.length = 8 ∧ b₃.length = 8 ∧ b₄.length = 8 ∧
      Outside s 32 rest ∧
      s.data.dmem =⋆ Mem.Bytes (s.data.regs.rsp.toBitVec - 8) b₁ ⋆
        (Mem.Bytes (s.data.regs.rsp.toBitVec - 16) b₂ ⋆
          (Mem.Bytes (s.data.regs.rsp.toBitVec - 24) b₃ ⋆
            (Mem.Bytes (s.data.regs.rsp.toBitVec - 32) b₄ ⋆ Eq rest))) := by
  have d {j k : Nat} (hjk : j + 8 ≤ k ∧ k + 8 ≤ 2 ^ 64 := by decide) :=
    (slot_disjoint s.data.regs.rsp.toBitVec hjk.1 hjk.2).symm
  have w (k : Nat) (hk : 8 ≤ k ∧ k ≤ 32 ∧ 8 ∣ k := by decide) := (h k hk.1 hk.2.1 hk.2.2).2.2
  obtain ⟨b₁, l₁, e₁⟩ := carve (a := s.data.regs.rsp.toBitVec - 8) (w 8)
  obtain ⟨b₂, l₂, e₂⟩ := carve (a := s.data.regs.rsp.toBitVec - 16)
    (mapped_cut (a := s.data.regs.rsp.toBitVec - 8) (d (j := 8) (k := 16)) (w 16))
  obtain ⟨b₃, l₃, e₃⟩ := carve (a := s.data.regs.rsp.toBitVec - 24)
    (mapped_cut (a := s.data.regs.rsp.toBitVec - 16) (d (j := 16) (k := 24))
      (mapped_cut (a := s.data.regs.rsp.toBitVec - 8) (d (j := 8) (k := 24)) (w 24)))
  obtain ⟨b₄, l₄, e₄⟩ := carve (a := s.data.regs.rsp.toBitVec - 32)
    (mapped_cut (a := s.data.regs.rsp.toBitVec - 24) (d (j := 24) (k := 32))
      (mapped_cut (a := s.data.regs.rsp.toBitVec - 16) (d (j := 16) (k := 32))
        (mapped_cut (a := s.data.regs.rsp.toBitVec - 8) (d (j := 8) (k := 32)) (w 32))))
  rw [e₂, e₃, e₄] at e₁
  have hm := cast (congrFun e₁ s.data.dmem) rfl
  refine ⟨b₁, b₂, b₃, b₄, _, l₁, l₂, l₃, l₄, ?_, hm⟩
  exact ((((Outside.rfl s 32).cut (k := 8) (by decide) (by decide)).cut (k := 16) (by decide)
    (by decide)).cut (k := 24) (by decide) (by decide)).cut (k := 32) (by decide) (by decide)

/-! ## Accesses in separation form -/

/-- A permitted write of a slot is a store; the slot then holds the word. -/
theorem writeRam_sep {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {bs : List UInt8}
    {F : DataMem → Prop} (hm : m =⋆ Mem.Bytes a bs ⋆ F)
    (hp : policy.permits (.write a .W64) = true) (hl : bs.length = 8) (v : BitVec 64) :
    writeRam policy m a .W64 v = .ok (Mem.storeInt m a 8 v.toInt) ∧
      Mem.storeInt m a 8 v.toInt =⋆ Word a v ⋆ F := by
  refine ⟨writeRam_of_mapped hp ?_, Mem.storeInt_sep a 8 bs F m ⟨hm, hl⟩ v.toInt⟩
  rw [Mem.loadInt_sep bs a 8 F m hm hl (by decide)]
  simp

/-- A permitted read of a slot gives its word. -/
theorem readRam_sep {policy : CpuPolicy} {m : DataMem} {a v : BitVec 64} {F : DataMem → Prop}
    (hm : m =⋆ Word a v ⋆ F) (hp : policy.permits (.read a .W64) = true) :
    readRam policy m a .W64 = .ok v := by
  simp [Lift.P2.Total.readRam, hp, Width.bytes, Width.bits,
    Mem.loadInt_sep _ a 8 F m hm (Int.toBytes_length 8 _) (by decide),
    BitVec.ofInt_ofBytes_toBytes_64]

/-- A read gives the same value from two memories with the same slot. -/
theorem readRam_frame {policy : CpuPolicy} {m m' : DataMem} {a u : BitVec 64} {bs : List UInt8}
    {F F' : DataMem → Prop} (hm : m =⋆ Mem.Bytes a bs ⋆ F) (hm' : m' =⋆ Mem.Bytes a bs ⋆ F')
    (hl : bs.length = 8) (h : readRam policy m a .W64 = .ok u) : readRam policy m' a .W64 = .ok u :=
  readRam_of_loadInt ((Mem.loadInt_sep bs a 8 F' m' hm' hl (by decide)).trans
    (Mem.loadInt_sep bs a 8 F m hm hl (by decide)).symm) h

/-- A word that a read gives is mapped. -/
theorem mapped_of_readRam {policy : CpuPolicy} {m : DataMem} {a u : BitVec 64}
    (h : readRam policy m a .W64 = .ok u) : Mem.loadInt m a 8 ≠ none := by
  intro hn
  simp [Lift.P2.Total.readRam, Width.bytes, hn] at h
  split at h <;> cases h

/-! ## The bytes outside the room -/

/-- Each byte of each memory of `P` is one of the `n` bytes below `sp`. -/
def InRoom (sp : BitVec 64) (n : Nat) (P : DataMem → Prop) : Prop :=
  ∀ h, P h → ∀ x, x ∈ h → Below sp n x

theorem InRoom.sep {sp : BitVec 64} {n : Nat} {P Q : DataMem → Prop} (hP : InRoom sp n P)
    (hQ : InRoom sp n Q) : InRoom sp n (P ⋆ Q) := by
  rintro _ ⟨a, b, rfl, -, ha, hb⟩ x hx
  rw [union_eq, mem_union_iff] at hx
  exact hx.elim (hP a ha x) (hQ b hb x)

/-- A slot at `sp - k` with `8 ≤ k ≤ n` is in the room. -/
theorem InRoom.bytes {sp : BitVec 64} {n k : Nat} {bs : List UInt8} (hl : bs.length = 8)
    (hk8 : 8 ≤ k) (hkn : k ≤ n) : InRoom sp n (Mem.Bytes (sp - BitVec.ofNat 64 k) bs) := by
  rintro _ rfl x hx
  obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hx
  unfold Below
  bv_omega

theorem InRoom.word {sp : BitVec 64} {n k : Nat} {v : BitVec 64}
    (hk8 : 8 ≤ k ∧ k ≤ n := by decide) :
    InRoom sp n (Word (sp - BitVec.ofNat 64 k) v) :=
  InRoom.bytes (Int.toBytes_length 8 _) hk8.1 hk8.2

/-- The slots in the room and an exact frame `rest` that is the memory of `s` outside the room:
the memory is that of `s` outside the room. -/
theorem Outside.of_sep {s : MachineState} {n : Nat} {m rest : DataMem} {P : DataMem → Prop}
    (hm : m =⋆ P ⋆ Eq rest) (hP : InRoom s.data.regs.rsp.toBitVec n P) (h : Outside s n rest) :
    Outside s n m := by
  obtain ⟨a, b, rfl, -, ha, rfl⟩ := hm
  intro x hx
  have hna : x ∉ a := fun hin => hx (hP a ha x hin)
  rw [get?_eq_getElem?, union_eq, getElem?_union, getElem?_eq_none hna, Option.or_none,
    ← get?_eq_getElem?]
  exact h x hx

/-- The return word at `rsp`, above the room, from the separation form. -/
theorem readRam_ret_of_sep {policy : CpuPolicy} {s : MachineState} {n : Nat} {m rest : DataMem}
    {P : DataMem → Prop} {u : BitVec 64} (hm : m =⋆ P ⋆ Eq rest)
    (hP : InRoom s.data.regs.rsp.toBitVec n P) (h : Outside s n rest) (hn : n + 8 ≤ 2 ^ 64)
    (hr : Lift.P2.Total.readRam policy s.data.dmem s.data.regs.rsp.toBitVec .W64 = .ok u) :
    Lift.P2.Total.readRam policy m s.data.regs.rsp.toBitVec .W64 = .ok u :=
  (Outside.of_sep hm hP h).readRam_ret hn hr

end Lift.Sem.SysV
