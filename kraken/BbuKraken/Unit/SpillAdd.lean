module

public import BbuKraken.Unit.SpillDefs
import all BbuKraken.Unit.SpillDefs
public import BbuKraken.Unit.IsSpilled
import all BbuKraken.Unit.IsSpilled

@[expose] public section

/-!
# `SpillSet::add`

`c/bbu/<Names.spillSetAdd>.S`: no frame, no call. It tests the kind byte and the opcode byte of
the slot (as `isSpilled`), reads the byte `m_spilled[payload]` and, if it is 0, stores 1 to it.
`al` is the `Status`: 0 (`DONE`) or 2 (`ASSERTION_FAILED`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

namespace SpillAdd

/-! ## The flags and `Flat.spillAdd` -/

-- `movzbl` then `testb %al, %al` and `al`: the byte.
theorem byte_zext (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = b := by
  ext i hi; simp [show i < 64 by omega, BitVec.getLsbD_eq_getElem, hi]

theorem al_zext (b : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = b := by
  ext i hi; simp

theorem isVariable_of {x : StackSlot} (hk : (!(x.kind == Value)) = false)
    (ho : (x.valueOpcode == Const) = false) : Flat.isVariable x = true := by
  simp_all [Flat.isVariable, isLiteralValue]

-- The jumps of `jne` (not a value) or of `je` (a literal) to `.LB.SpillSet.add.1`.
theorem add_not_var {f : BitVec 32 → BitVec 8} {x : StackSlot}
    (h : (!(x.kind == Value)) = true ∨ (x.valueOpcode == Const) = true) :
    Flat.spillAdd f x = (.assertionFailed, f) := by
  unfold Flat.spillAdd Flat.isVariable isLiteralValue
  rcases h with h | h <;> simp_all

-- `jne .LB.SpillSet.add.0`: the byte is not 0.
theorem add_spilled {f : BitVec 32 → BitVec 8} {x : StackSlot} (hk : (!(x.kind == Value)) = false)
    (ho : (x.valueOpcode == Const) = false)
    (hb : (!(f x.payload &&& f x.payload == BitVec.zero 8)) = true) :
    Flat.spillAdd f x = (.assertionFailed, f) := by
  rw [BitVec.and_self] at hb
  have hv := isVariable_of hk ho
  simp only [Flat.spillAdd, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp_all

-- The fall-through: the byte is 0, and the store writes 1.
theorem add_done {f : BitVec 32 → BitVec 8} {x : StackSlot} (hk : (!(x.kind == Value)) = false)
    (ho : (x.valueOpcode == Const) = false)
    (hb : (!(f x.payload &&& f x.payload == BitVec.zero 8)) = false) :
    Flat.spillAdd f x = (.done, Flat.setByte f x.payload 1) ∧ f x.payload = 0#8 := by
  rw [BitVec.and_self] at hb
  have hv := isVariable_of hk ho
  have h0 : f x.payload = 0#8 := by simpa using hb
  simp only [Flat.spillAdd, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h0]
  simp

/-! ## The states -/

variable {p S : Addr} {f : BitVec 32 → BitVec 8} {n : Nat} {F : MProp 64} {s t : MachineData}
  {ra : Int64}

abbrev Pm (p S : Addr) (f : BitVec 32 → BitVec 8) (n : Nat) (F : MProp 64) : MProp 64 :=
  Wd p S ∗ Spl S f (List.range n) ∗ F

theorem rd_S (h : Kg (Pm p S f n F) s ra [] t) :
    BitVec.ofInt 64 (Mem.loadInt t.dmem p 8).get! = S := by
  obtain ⟨R, e⟩ : ∃ R, Stk (rsp s) [] ra.toBitVec ∗ Pm p S f n F = Wd p S ∗ R :=
    ⟨_, by unfold Pm; ecancel⟩
  exact Wd.rd (e ▸ h.mem)

theorem isSome_S (h : Kg (Pm p S f n F) s ra [] t) : (Mem.loadInt t.dmem p 8).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, Stk (rsp s) [] ra.toBitVec ∗ Pm p S f n F = Wd p S ∗ R :=
    ⟨_, by unfold Pm; ecancel⟩
  exact Wd.isSome (e ▸ h.mem)

theorem spl (h : Kg (Pm p S f n F) s ra [] t) :
    ∃ R, (Spl S f (List.range n) ∗ R).get t.dmem := by
  obtain ⟨R, e⟩ : ∃ R, Stk (rsp s) [] ra.toBitVec ∗ Pm p S f n F
      = Spl S f (List.range n) ∗ R := ⟨_, by unfold Pm; ecancel⟩
  exact ⟨R, e ▸ h.mem⟩

theorem payload_lt (hpre : AddPre p S f n F s)
    (hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false)
    (ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false) :
    (StackSlot.ofWord (rsi s)).payload.toNat ∈ List.range n :=
  List.mem_range.mpr (hpre.lt (isVariable_of hk ho))

theorem isSome_byte (h : Kg (Pm p S f n F) s ra [] t) (hpre : AddPre p S f n F s)
    (hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false)
    (ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false) :
    (Mem.loadInt t.dmem (S + BitVec.ofNat 64 (StackSlot.ofWord (rsi s)).payload.toNat) 1).isSome
      = true :=
  let ⟨_, hs⟩ := spl h; Spl.isSome hs (payload_lt hpre hk ho)

theorem rdb_byte (h : Kg (Pm p S f n F) s ra [] t) (hpre : AddPre p S f n F s)
    (hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false)
    (ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false) :
    BitVec.ofInt 8 (Mem.loadInt t.dmem
      (S + BitVec.ofNat 64 (StackSlot.ofWord (rsi s)).payload.toNat) 1).get!
      = f (StackSlot.ofWord (rsi s)).payload := by
  obtain ⟨_, hs⟩ := spl h
  have := Spl.rdb hs (payload_lt hpre hk ho)
  rwa [show ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x by simp] at this

-- `movb $1, (%rsi)`.
theorem kg_store (h : Kg (Pm p S f n F) s ra [] t) (hn : n ≤ 2 ^ 32) {q : BitVec 32}
    (hi : q.toNat ∈ List.range n) {t' : MachineData}
    (hm : t'.dmem = t.dmem.storeInt (S + BitVec.ofNat 64 q.toNat) 1 1)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) :
    Kg (Pm p S (Flat.setByte f q 1) n F) s ra [] t' := by
  obtain ⟨R, e⟩ : ∃ R, ∀ g, Stk (rsp s) [] ra.toBitVec ∗ Pm p S g n F
      = Spl S g (List.range n) ∗ R := ⟨_, fun g => by unfold Pm; ecancel⟩
  have hs := Spl.store List.nodup_range (fun j hj => by have := List.mem_range.mp hj; omega)
    (e f ▸ h.mem) hi 1
  rw [show BitVec.ofNat 32 q.toNat = q by simp, show BitVec.ofInt 8 1 = 1 by rfl] at hs
  refine ⟨?_, hsp.trans h.sp, hbx.trans h.bx, hbp.trans h.bp, h12.trans h.r12, h13.trans h.r13,
    h14.trans h.r14, h15.trans h.r15⟩
  rw [hm, e]
  exact hs

-- The postcondition at `ret`.
theorem post {f' : BitVec 32 → BitVec 8} (h : Kg (Pm p S f' n F) s ra [] t)
    {st : Flat.Status}
    (hf : Flat.spillAdd f (StackSlot.ofWord (rsi s)) = (st, f')) (hal : al t = code st) :
    ∀ t', t'.dmem = t.dmem → rax t' = rax t → AddPost p S f n F s t' := by
  intro t' hm hax
  refine ⟨by rw [hf]; exact (congrArg (BitVec.setWidth 8) hax).trans hal, ra.toBitVec, ?_⟩
  rw [hf, hm]
  have e : Stk (rsp s) [] ra.toBitVec ∗ Pm p S f' n F
      = Wd p S ∗ Spl S f' (List.range n) ∗ Stk (rsp s) [] ra.toBitVec ∗ F := by
    unfold Pm; ecancel
  exact e ▸ h.mem

end SpillAdd

open SpillAdd in
theorem spillSetAdd_unit [Host] [FunDecls] :
    ∀ p S f n F, Body spillSetAddAsm (AddPre p S f n F) (AddPost p S f n F) := by
  intro p S f n F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨v, hm⟩ := hpre.mem
  have hk0 : Kg (Pm p S f n F) s ra [] (s.pushRa ra) :=
    Kg.init (v := v) (by
      have e : Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [] v ∗ F
          = Stk (rsp s) [] v ∗ Pm p S f n F := by unfold Pm; ecancel
      exact e ▸ hm)
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.spillSetAdd then t = s.pushRa ra
        else if l = ".LB.SpillSet.add.0" then Kg (Pm p S f n F) s ra [] t
          ∧ Flat.spillAdd f (StackSlot.ofWord (rsi s)) = (.assertionFailed, f)
        else if l = ".LB.SpillSet.add.1" then Kg (Pm p S f n F) s ra [] t
          ∧ al t = 2#8 ∧ Flat.spillAdd f (StackSlot.ofWord (rsi s)) = (.assertionFailed, f)
        else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.spillSetAdd, ↓reduceIte]
  case «.LB.SpillSet.add.0» t ht =>
    simp only [Names.spillSetAdd, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hf⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    · simp only [Names.spillSetAdd, String.reduceEq, ↓reduceIte]
      exact ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, trivial, hf⟩
    · decide
  case «.LB.SpillSet.add.1» t ht =>
    simp only [Names.spillSetAdd, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hal, hf⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => simp [hk.retAddr]
    | ret => exact Kg.ret hk (post hk hf hal)
  case «_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot» t ht =>
    simp only [Names.spillSetAdd, ↓reduceIte] at ht
    subst ht
    have hrdi : (s.pushRa ra).regs.rdi.toBitVec = p := by
      simpa [MachineData.pushRa] using hpre.rdi
    have hrsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
    have hS := rd_S hk0
    have hS' := isSome_S hk0
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [IsSpilled.kind_flag, IsSpilled.op_flag, hrdi, hrsi, hS,
      IsSpilled.payload_word, byte_zext] at *
    vc_by_shape
    | closed => decide
    | goto ".LB.SpillSet.add.1" =>
      -- `jne` (not a value) or `je` (a literal): `al = 2`.
      have hf : Flat.spillAdd f (StackSlot.ofWord (rsi s)) = (.assertionFailed, f) :=
        add_not_var (by first | exact Or.inl ‹_› | exact Or.inr ‹_›)
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.spillSetAdd, String.reduceEq, ↓reduceIte]
        exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, hf⟩
      · simp
    | goto ".LB.SpillSet.add.0" =>
      -- `jne .LB.SpillSet.add.0`: the byte is not 0.
      have hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false := ‹_›
      have ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false := ‹_›
      have hb := rdb_byte hk0 hpre hk ho
      have hf := add_spilled (f := f) hk ho (by rw [← hb]; assumption)
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.spillSetAdd, String.reduceEq, ↓reduceIte]
        exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, hf⟩
      · simp
    | load =>
      first
      | exact hS'
      | exact isSome_byte hk0 hpre ‹_› ‹_›
    | retAddr =>
      have hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false := ‹_›
      have ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false := ‹_›
      refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr
        (P := Pm p S (Flat.setByte f (StackSlot.ofWord (rsi s)).payload 1) n F) (s := s)
        (fr := []) ?_⟩
      exact kg_store hk0 hpre.n_le (payload_lt hpre hk ho) rfl rfl rfl rfl rfl rfl rfl rfl
    | ret =>
      -- The fall-through: `m_spilled[payload] = 1` and `al = 0`.
      have hk : (!((StackSlot.ofWord (rsi s)).kind == Value)) = false := ‹_›
      have ho : ((StackSlot.ofWord (rsi s)).valueOpcode == Const) = false := ‹_›
      have hb := rdb_byte hk0 hpre hk ho
      have hd := add_done (f := f) hk ho (by rw [← hb]; assumption)
      simp only [rsi, Reg64s.get64_rsi] at hb hd
      refine Kg.ret (P := Pm p S (Flat.setByte f (StackSlot.ofWord (rsi s)).payload 1) n F)
        (s := s) (fr := [])
        (kg_store hk0 hpre.n_le (payload_lt hpre hk ho) rfl rfl rfl rfl rfl rfl rfl rfl)
        ?_
      refine post (kg_store hk0 hpre.n_le (payload_lt hpre hk ho) rfl rfl rfl rfl rfl rfl rfl rfl)
        hd.1 ?_
      simp only [al, rax, Reg64s.get64_rax, al_zext, hb, hd.2]
      rfl

end Bbu.Unit
