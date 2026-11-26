module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Sem.HeapLemmas
public import Lift.Sem.StackRoom
public import Lift.Sem.Hidden
public import Lift.Sem.HeapBytesFrame
public import Lift.Pilot.Call
public import Lift.Sem.Cut
public import Lift.Sem.PrivateStack
public import Lift.Sem.StackArgs
public import Lift.Sem.CallArmBytes

@[expose] public section

/-! The relation between the trusted forms of `Lift/Trusted` (objects of fields, `Mem.has`,
`Fn.Entry`, `Fn.Return`) and the forms of the chain (`Obj`, `Heap.Holds`, `SysV.Entry`,
`SysV.StackRoom`, `Heap.Owned`, `SysV.Below`). The lemmas are not about one function. The trusted
side compares byte ranges as natural numbers; the chain compares them modulo `2^64`. They agree
when the range does not wrap. The call form `Fn.CallB` of `Lift/Pilot/Call.lean` also gives the
byte-range permission `Heap.Permits` of the heap (`Fn.EntryB.holds_permits`); the import of
`Lift.Sem.HeapBytesFrame` gives the lemmas of `Heap.loadB` and `Heap.storeB` to the texts that
import this module. -/

namespace Lift.Sem.Bridge

open Lift.P2.Total Lift.Trusted

/-- The cell of a field. -/
def toCell (f : Field) : Cell := ⟨f.w, f.v⟩

/-- The heap object of a trusted object: the same address, writability and values. -/
def toObj (o : Object) : Obj := ⟨o.addr, o.writable, o.fields.map toCell⟩

/-! ## Objects -/

theorem offsets_map (n : Nat) (fs : List Field) :
    Sem.offsets n (fs.map toCell) =
      (Trusted.offsets n fs).map fun x => (x.1, toCell x.2) := by
  induction fs generalizing n with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, Sem.offsets, Trusted.offsets, ih]
    rfl

/-- The object of an array of words, `Encode.encode` of a list of `u64`, is the array of the words. -/
theorem toObj_encode_words64 (p : BitVec 64) (xs : List (BitVec 64)) (wr : Bool) :
    toObj ⟨p, Encode.encode xs, wr⟩ = Obj.words p wr .W64 xs := by
  simp [toObj, Obj.words, Encode.encode, toCell]

theorem size_toObj (o : Object) : (toObj o).size = o.size := by
  simp only [Obj.size, Object.size, toObj, List.map_map]
  rfl

theorem mem_offsets_toObj {o : Object} {x : Nat × Cell} :
    x ∈ Sem.offsets 0 (toObj o).cells ↔ ∃ y ∈ Trusted.offsets 0 o.fields, x = (y.1, toCell y.2) := by
  simp only [toObj, offsets_map, List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩

theorem covers_toObj (o : Object) (b : BitVec 64) : (toObj o).Covers b ↔ InBytes o.addr o.size b := by
  unfold Obj.Covers InBytes
  rw [size_toObj]
  rfl

theorem apart_toObj (o o' : Object) : (toObj o).Apart (toObj o') ↔ Apart o.addr o.size o'.addr o'.size := by
  unfold Obj.Apart Apart
  rw [size_toObj, size_toObj]
  rfl

/-- `Mem.has` of one object is the `read`, `write` and `noWrap` parts of `Heap.Holds`. -/
theorem has_iff (policy : CpuPolicy) (m : DataMem) (o : Object) :
    Mem.has policy m o ↔ (toObj o).addr.toNat + (toObj o).size ≤ 2 ^ 64 ∧
      (∀ x ∈ Sem.offsets 0 (toObj o).cells,
        readRam policy m ((toObj o).addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) ∧
      ((toObj o).writable → ∀ x ∈ Sem.offsets 0 (toObj o).cells,
        policy.permits (.write ((toObj o).addr + BitVec.ofNat 64 x.1) x.2.w)) := by
  rw [size_toObj]
  constructor
  · rintro ⟨hn, hx⟩
    refine ⟨hn, fun x hx' => ?_, fun hw x hx' => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_offsets_toObj.mp hx'
      exact (hx y hy).1
    · obtain ⟨y, hy, rfl⟩ := mem_offsets_toObj.mp hx'
      exact (hx y hy).2 hw
  · rintro ⟨hn, hr, hw⟩
    exact ⟨hn, fun y hy => ⟨hr _ (mem_offsets_toObj.mpr ⟨y, hy, rfl⟩),
      fun h => hw h _ (mem_offsets_toObj.mpr ⟨y, hy, rfl⟩)⟩⟩

/-- The heap of a list of trusted objects is held exactly when the memory has each object and the
objects are separate. -/
theorem holds_iff (policy : CpuPolicy) (objs : List Object) (m : DataMem) :
    Heap.Holds policy (objs.map toObj) m ↔
      (∀ o ∈ objs, Mem.has policy m o) ∧ Separate objs := by
  constructor
  · intro hh
    refine ⟨fun o ho => (has_iff policy m o).mpr ⟨hh.noWrap _ (List.mem_map_of_mem ho),
      hh.read _ (List.mem_map_of_mem ho), hh.write _ (List.mem_map_of_mem ho)⟩, ?_⟩
    have := List.pairwise_map.mp hh.apart
    refine this.imp fun h hw => (apart_toObj _ _).mp (h hw)
  · rintro ⟨hm, hs⟩
    refine ⟨fun o' ho' => ?_, fun o' ho' => ?_, fun o' ho' => ?_, ?_⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      exact ((has_iff policy m o).mp (hm o ho)).2.1
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      exact ((has_iff policy m o).mp (hm o ho)).2.2
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      exact ((has_iff policy m o).mp (hm o ho)).1
    · exact List.pairwise_map.mpr (hs.imp fun h hw => (apart_toObj _ _).mpr (h hw))

theorem owned_iff (objs : List Object) (b : BitVec 64) :
    Heap.Owned (objs.map toObj) b ↔
      ∃ o ∈ objs, o.writable = true ∧ InBytes o.addr o.size b := by
  constructor
  · rintro ⟨o', ho', hw, hc⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
    exact ⟨o, ho, hw, (covers_toObj o b).mp hc⟩
  · rintro ⟨o, ho, hw, hc⟩
    exact ⟨(toObj o), List.mem_map_of_mem ho, hw, (covers_toObj o b).mpr hc⟩

/-! ## Byte ranges modulo `2^64` -/

/-- A range that does not wrap: the modular distance from its start is the natural one. -/
theorem sub_toNat_lt_iff {lo b : BitVec 64} {n : Nat} (h : lo.toNat + n ≤ 2 ^ 64) :
    (b - lo).toNat < n ↔ InBytes lo n b := by
  unfold InBytes
  rw [BitVec.toNat_sub]
  have := b.isLt
  have := lo.isLt
  by_cases hb : lo.toNat ≤ b.toNat
  · rw [show 2 ^ 64 - lo.toNat + b.toNat = (b.toNat - lo.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem toNat_sub_ofNat {sp : BitVec 64} {n : Nat} (hn : n ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 n).toNat = sp.toNat - n := by
  have := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    show 2 ^ 64 - n + sp.toNat = (sp.toNat - n) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- `SysV.Below` is modular; it is the natural range `[sp - n, sp)` when `n ≤ sp`. -/
theorem below_iff {sp b : BitVec 64} {n : Nat} (hn : n ≤ sp.toNat) :
    SysV.Below sp n b ↔ InBytes (sp - BitVec.ofNat 64 n) n b := by
  unfold SysV.Below
  apply sub_toNat_lt_iff
  rw [toNat_sub_ofNat hn]
  have := sp.isLt
  omega

/-- No byte of a range `[lo, lo + n)` that does not wrap is a byte of an object apart from it. -/
theorem not_covers_of_apart {o : Object} {lo b : BitVec 64} {n : Nat}
    (ha : Apart o.addr o.size lo n) (hw : lo.toNat + n ≤ 2 ^ 64) (hb : (b - lo).toNat < n) :
    ¬ (toObj o).Covers b := by
  rw [covers_toObj]
  have := (sub_toNat_lt_iff hw).mp hb
  unfold InBytes at *
  unfold Apart at ha
  omega

/-! ## The stack room and the return word -/

theorem mem_offsets_words64 (xs : List (BitVec 64)) (n k : Nat) (hk : k < xs.length) :
    (n + 8 * k, (⟨.W64, xs[k]⟩ : Field)) ∈ Trusted.offsets n (xs.map fun v => ⟨.W64, v⟩) := by
  induction xs generalizing n k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => simp [Trusted.offsets]
    | succ k =>
      have := ih (n + 8) k (by simpa using hk)
      simp only [List.map_cons, Trusted.offsets, List.mem_cons, List.getElem_cons_succ]
      right
      rw [show n + 8 * (k + 1) = n + 8 + 8 * k by omega]
      exact this

/-- The words `[sp - n, sp)` of a trusted stack object give the stack room of the chain. -/
theorem stackRoom_of_has {policy : CpuPolicy} {s : MachineState} {n : Nat} {ws : List (BitVec 64)}
    (hn : n ≤ s.data.regs.rsp.toNat) (hl : ws.length * 8 = n)
    (h : Mem.has policy s.data.dmem
      ⟨s.data.regs.rsp.toBitVec - BitVec.ofNat 64 n, ws.map fun w => ⟨.W64, w⟩, true⟩) :
    SysV.StackRoom policy s n := by
  intro k hk8 hkn hd
  obtain ⟨q, rfl⟩ := hd
  have hn' : n ≤ s.data.regs.rsp.toBitVec.toNat := hn
  have hi : (n - 8 * q) / 8 < ws.length := by omega
  have hx := h.2 _ (mem_offsets_words64 ws 0 _ hi)
  have ha : s.data.regs.rsp.toBitVec - BitVec.ofNat 64 n +
      BitVec.ofNat 64 (0 + 8 * ((n - 8 * q) / 8)) = s.data.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * q) := by
    apply BitVec.eq_of_toNat_eq
    have := s.data.regs.rsp.toBitVec.isLt
    have e : 0 + 8 * ((n - 8 * q) / 8) = n - 8 * q := by omega
    rw [e, BitVec.toNat_add, toNat_sub_ofNat (by omega), toNat_sub_ofNat (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - 8 * q < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
    change s.data.regs.rsp.toNat - n + (n - 8 * q) = s.data.regs.rsp.toNat - 8 * q
    omega
  rw [ha] at hx
  obtain ⟨hr, hw⟩ := hx
  obtain ⟨hp, v, hv⟩ := readRam_ok hr
  exact ⟨hw rfl, hp, by rw [show (8 : Nat) = Width.W64.bytes from rfl, hv]; nofun⟩

/-- The return word of a trusted entry: the read is permitted, the chain's return address is `ra`,
and the word does not wrap. -/
theorem ret_of_has {policy : CpuPolicy} {s : MachineState} {ra : BitVec 64}
    (h : Mem.has policy s.data.dmem (retWord s ra)) :
    policy.permits (.read s.data.regs.rsp.toBitVec .W64) = true ∧
      SysV.retAddr s = some (Int64.ofBitVec ra) ∧ s.data.regs.rsp.toNat + 8 ≤ 2 ^ 64 := by
  have hr := (h.2 (0, ⟨.W64, ra⟩) (by simp [retWord, Trusted.offsets])).1
  simp only [retWord, BitVec.add_zero] at hr
  unfold readRam at hr
  split at hr
  · rename_i hp
    split at hr
    · rename_i v hv
      cases hr
      refine ⟨hp, ?_, h.1⟩
      unfold SysV.retAddr
      rw [show (8 : Nat) = Width.W64.bytes from rfl, hv]
      rfl
    · cases hr
  · cases hr

/-- The first argument of 64 bits is `rdi`. -/
theorem rdi_of_argsIn {s : MachineState} {j : BitVec 64} (h : ArgsIn [⟨.W64, j⟩] s) :
    s.data.regs.rdi.toBitVec = j := by
  have := h.2 (⟨.W64, j⟩, s.data.regs.rdi) (by simp [argRegs])
  simpa [Field.InReg, Width.bits] using this

/-- A trusted entry is a chain entry of the code range `[lo, hi)` of the program. -/
theorem Fn.Entry.sysV {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object}
    {ra : BitVec 64} {s : MachineState} {lo hi : Int64} (h : f.Entry policy args objs ra s)
    (hlo : f.code.startAddr = lo) (hhi : f.code.addrOf f.code.program.length = hi) :
    SysV.Entry policy lo hi f.entry s := by
  obtain ⟨hp, -, -⟩ := ret_of_has h.ret
  obtain ⟨-, hra, -⟩ := ret_of_has h.ret
  exact ⟨h.pc, hlo ▸ hhi ▸ h.exec, hp, _, hra⟩

/-! ## The return -/

/-- The chain's frame (not owned, not in the room below `sp`) gives the trusted frame. -/
theorem frame_of_owned {objs : List Object} {sp : BitVec 64} {n : Nat} {m m' : DataMem}
    (hn : n ≤ sp.toNat)
    (h : ∀ b, ¬ Heap.Owned (objs.map toObj) b → ¬ SysV.Below sp n b → m'.get? b = m.get? b) :
    ∀ b, (∀ o ∈ objs, o.writable = true → ¬ InBytes o.addr o.size b) →
      ¬ InBytes (sp - BitVec.ofNat 64 n) n b → m'.get? b = m.get? b := by
  intro b hb hr
  refine h b (fun ho => ?_) (fun hbl => hr ((below_iff hn).mp hbl))
  obtain ⟨o, ho, hw, hc⟩ := (owned_iff objs b).mp ho
  exact hb o ho hw hc

/-- The PC of a chain exit is the trusted return address. -/
theorem pc_of_exit {s t : MachineState} {ra : BitVec 64} (hr : SysV.retAddr s = some (Int64.ofBitVec ra))
    (he : SysV.Exit s t) : t.pc = Int64.ofBitVec ra :=
  Option.some.inj (he.pc.symm.trans hr)

/-! ## The byte-range permission of `Fn.CallB` (decisions D38 and D40) -/

/-- The byte-range permission of the heap of a list of trusted objects is `PermitsRange` of each
object. -/
theorem permits_iff (policy : CpuPolicy) (objs : List Object) :
    Heap.Permits policy (objs.map toObj) ↔
      ∀ o ∈ objs, PermitsRange policy o.addr o.size o.writable := by
  constructor
  · intro h o ho k w hk
    have := h (toObj o) (List.mem_map_of_mem ho) k w (by rw [size_toObj]; exact hk)
    exact this
  · intro h o' ho' k w hk
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
    rw [size_toObj] at hk
    exact h o ho k w hk

/-- The bridge of `Fn.CallB`: the memory of a `Fn.EntryB` state holds the heap of the objects, and
the policy has the byte-range permission of that heap. -/
theorem Fn.EntryB.holds_permits {f : Fn} {policy : CpuPolicy} {args : List Field}
    {objs : List Object} {ra : BitVec 64} {s : MachineState} (h : f.EntryB policy args objs ra s) :
    Heap.Holds policy (objs.map toObj) s.data.dmem ∧ Heap.Permits policy (objs.map toObj) :=
  ⟨(holds_iff policy objs _).mpr ⟨h.1.has, h.1.separate⟩, (permits_iff policy objs).mpr h.2.1⟩

end Lift.Sem.Bridge
