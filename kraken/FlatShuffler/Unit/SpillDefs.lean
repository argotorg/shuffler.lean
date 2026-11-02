module

public import FlatShuffler.Unit.Defs
import all FlatShuffler.Unit.Defs
public import FlatShuffler.FlatSpill
import all FlatShuffler.FlatSpill
public import FlatShuffler.Sep.ExitContract
import all FlatShuffler.Sep.ExitContract

@[expose] public section

/-! The memory and call contracts of `SpillSet::add`. -/

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit

open FlatShuffler.Sep

abbrev r9 (s : MachineData) : Word := s.regs.get64 .r9

/-! ## A body state

`Sep.Kp` with the memory `P` in place of `View S g ∗ F`. -/

structure Kg (P : MProp 64) (s : MachineData) (ra : Int64) (fr : List Word) (t : MachineData) :
    Prop where
  mem : (Stk (rsp s) fr ra.toBitVec ∗ P).get t.dmem
  sp : t.regs.rsp = (s.pushRa ra).regs.rsp
  bx : t.regs.rbx = s.regs.rbx
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {P : MProp 64} {s t : MachineData} {ra : Int64} {fr : List Word}

theorem Kg.init {v : Word} (h : (Stk (rsp s) fr v ∗ P).get s.dmem) :
    Kg P s ra fr (s.pushRa ra) := by
  have e : ∀ w, Stk (rsp s) fr w ∗ P
      = Wd (rsp s - 8#64) w ∗ (Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ P) := by
    intro w; unfold Stk; ecancel
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [e]
  exact Wd.store (e v ▸ h) ra.toBitVec

theorem Kg.next {t' : MachineData} (h : Kg P s ra fr t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Kg P s ra fr t' :=
  ⟨hm ▸ h.mem, hsp.trans h.sp, hbx.trans h.bx, hbp.trans h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem Kg.sp64 (h : Kg P s ra fr t) : t.regs.get64 .rsp = rsp s - 8#64 := by
  rw [Reg64s.get64_rsp, h.sp]; rfl

theorem Kg.retAddr (h : Kg P s ra fr t) : t.retAddr = some ra := by
  obtain ⟨R, e⟩ : ∃ R, Stk (rsp s) fr ra.toBitVec ∗ P = Wd (rsp s - 8#64) ra.toBitVec ∗ R :=
    ⟨_, by unfold Stk; ecancel⟩
  rw [MachineData.retAddr, h.sp64, Wd.retAddr (e ▸ h.mem), Int64.ofBitVec_toBitVec]

theorem Kg.stack (h : Kg P s ra fr t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by simp [h.sp])

-- Undo the alignment word for a leaf function that uses `subq $8, %rsp`.
def unpad (t : MachineData) : MachineData :=
  { t with regs := t.regs.set64 .rsp (t.regs.get64 .rsp + 8#64) }

theorem Kg.padded_stack (h : Kg P s ra fr (unpad t)) :
    t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  have hs : t.regs.get64 .rsp + 8#64 = rsp s - 8#64 := h.sp64
  simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
  have he : rsp s - 8#64 - t.regs.get64 .rsp = 8#64 := by bv_omega
  rw [he]
  decide

-- `ret` from a body in state `t`: the postcondition holds for each state with the memory and
-- `rax` of `t`.
theorem Kg.ret [Host] {post : MachineData → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} (h : Kg P s ra fr t)
    (hQ : ∀ t', t'.dmem = t.dmem → rax t' = rax t → post s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t' => a = ra ∧ post s t' ∧ Sep.mod.Agree s t') t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } := by
  have hsp : t.regs.get64 .rsp + 8#64 = rsp s := by rw [h.sp64]; exact BitVec.sub_add_cancel _ _
  refine Or.inr ⟨⟨by simp [h.retAddr], hQ _ rfl (by simp [rax]), fun q hq => ?_, mod_mem _ _⟩,
    fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · next he => subst he; exact hsp
    · have hb := h.bx; have hp := h.bp; have h2 := h.r12; have h3 := h.r13; have h4 := h.r14
      have h5 := h.r15
      cases q <;> simp_all [Sep.mod, Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_r12,
        Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15]
  · apply MachineData.stackBelow_of_add_eight
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [hsp]; exact BitVec.sub_add_cancel _ _

end

/-! ## The bytes of the spill set -/

-- Two ids below `2 ^ 32` are two indices.
theorem ofNat32_ne {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (h : j ≠ i) :
    BitVec.ofNat 32 j ≠ BitVec.ofNat 32 i := by
  intro e; apply h
  have := congrArg BitVec.toNat e
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

theorem Spl.congr {a : Addr} {f g : BitVec 32 → BitVec 8} {is : List Nat}
    (h : ∀ j ∈ is, f (BitVec.ofNat 32 j) = g (BitVec.ofNat 32 j)) : Spl a f is = Spl a g is := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    simp only [Spl]
    rw [h j (List.mem_cons_self ..), ih fun k hk => h k (List.mem_cons_of_mem _ hk)]

-- The atom of the id `i`, and the bytes of the other ids.
theorem Spl.erase (a : Addr) (f : BitVec 32 → BitVec 8) {is : List Nat} {i : Nat} (hi : i ∈ is) :
    Spl a f is = B8 (a + BitVec.ofNat 64 i) (f (BitVec.ofNat 32 i)) ∗ Spl a f (is.erase i) := by
  induction is with
  | nil => cases hi
  | cons j js ih =>
    by_cases e : j = i
    · subst e; simp [Spl]
    · have hi' : i ∈ js := (List.mem_cons.mp hi).resolve_left (Ne.symm e)
      rw [List.erase_cons_tail (by simpa using e)]
      simp only [Spl]; rw [ih hi', sep_lc]

section
variable {a : Addr} {f : BitVec 32 → BitVec 8} {is : List Nat} {F : MProp 64} {m : Mem 64} {i : Nat}

theorem Spl.isSome (h : (Spl a f is ∗ F).get m) (hi : i ∈ is) :
    (m.loadInt (a + BitVec.ofNat 64 i) 1).isSome = true := by
  rw [Spl.erase a f hi, MProp.sep_assoc] at h; exact B8.isSome h

theorem Spl.rdb (h : (Spl a f is ∗ F).get m) (hi : i ∈ is) :
    rdb m (a + BitVec.ofNat 64 i) = f (BitVec.ofNat 32 i) := by
  rw [Spl.erase a f hi, MProp.sep_assoc] at h; exact B8.rdb h

-- `movb` to the byte of the id `i`. The ids are distinct and below `2 ^ 32`.
theorem Spl.store (hnd : is.Nodup) (hlt : ∀ j ∈ is, j < 2 ^ 32) (h : (Spl a f is ∗ F).get m)
    (hi : i ∈ is) (x : Int) :
    (Spl a (Flat.setByte f (BitVec.ofNat 32 i) (BitVec.ofInt 8 x)) is ∗ F).get
      (m.storeInt (a + BitVec.ofNat 64 i) 1 x) := by
  have e : Spl a (Flat.setByte f (BitVec.ofNat 32 i) (BitVec.ofInt 8 x)) (is.erase i)
      = Spl a f (is.erase i) := by
    refine Spl.congr fun j hj => ?_
    have hji : j ≠ i := fun e => hnd.not_mem_erase (e ▸ hj)
    have hj' := List.mem_of_mem_erase hj
    simp [Flat.setByte, ofNat32_ne (hlt i hi) (hlt j hj') hji]
  rw [Spl.erase a f hi, MProp.sep_assoc] at h
  rw [Spl.erase a _ hi, e, MProp.sep_assoc]
  simpa [Flat.setByte] using B8.store h x

end

/-! ## Bytes -/

-- The bytes `bs` from `a`.
def Bs (a : Addr) : List (BitVec 8) → MProp 64
  | [] => MProp.emp
  | b :: bs => B8 a b ∗ Bs (a + 1#64) bs

/-! ## `SpillSet::add` -/

-- `rdi` is the object `p` that holds `S`; the bytes of the ids below `n` are at `S`; the id of
-- a variable slot `rsi` is below `n`; the stack holds the return slot.
structure AddPre (p S : Addr) (f : BitVec 32 → BitVec 8) (n : Nat) (F : MProp 64)
    (s : MachineData) : Prop where
  rdi : rdi s = p
  n_le : n ≤ 2 ^ 32
  lt : Flat.isVariable (StackSlot.ofWord (rsi s)) = true →
    (StackSlot.ofWord (rsi s)).payload.toNat < n
  mem : ∃ x y v, (Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [x, y] v ∗ F).get s.dmem

-- `al` is the `EmissionOutcome` of `Flat.spillAdd`, and the bytes are its bytes.
def AddPost (p S : Addr) (f : BitVec 32 → BitVec 8) (n : Nat) (F : MProp 64)
    (s t : MachineData) : Prop :=
  some (al t) = code (Flat.spillAdd f (StackSlot.ofWord (rsi s))).1
    ∧ ∃ x y v, (Wd p S ∗ Spl S (Flat.spillAdd f (StackSlot.ofWord (rsi s))).2 (List.range n)
      ∗ Stk (rsp s) [x, y] v ∗ F).get t.dmem

def AddExit (p S : Addr) (f : BitVec 32 → BitVec 8) (n : Nat) (F : MProp 64)
    (s t : MachineData) : Prop :=
  Flat.spillAdd f (StackSlot.ofWord (rsi s)) = (.assertionExit, f)
    ∧ ∃ x y v, (Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [x, y] v ∗ F).get t.dmem

-- The call rule of `SpillSet::add`: the caller gives the object, the bytes and the frame.
abbrev AddSpec [Host] [FunDecls] : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ p S f n F, AddPre p S f n F s
        ∧ (∀ s', AddPost p S f n F s s' → Sep.mod.Agree s s' → K () s')
        ∧ (∀ s', AddExit p S f n F s s' → s'.regs.get64 .rdi = 1#64 → E (label "exit") s') ⦄
      (Directive.instr (.regular asz osz
        (.call (.rel (.sub (.label Names.spillSetAdd) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem AddPre.isSome {p S : Addr} {f : BitVec 32 → BitVec 8} {n : Nat} {F : MProp 64}
    {s : MachineData} (h : AddPre p S f n F s) :
    (s.dmem.loadInt (s.regs.get64 .rsp - 8#64) 8).isSome = true := by
  obtain ⟨x, y, v, hm⟩ := h.mem
  obtain ⟨R, e⟩ : ∃ R, Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [x, y] v ∗ F
      = Wd (rsp s - 8#64) v ∗ R := ⟨_, by unfold Stk; ecancel⟩
  exact Wd.isSome (e ▸ hm)

theorem addSpec_of_body [Host] [FunDecls] {g₀ : Fragment}
    (hg : FunDecls.at (label Names.spillSetAdd) = some g₀)
    (hr : ProofKit.ReturnAddressDistinct Names.spillSetAdd "exit")
    (hb : ∀ p S f n F, BodyWithExit g₀.prog (AddPre p S f n F)
      (AddPost p S f n F) (AddExit p S f n F)) : AddSpec := by
  intro asz osz K E
  refine ⟨fun s ⟨p, S, f, n, F, hp, hk, hx⟩ => ?_⟩
  exact (ProofKit.callSpecWithExit_of_triple hg hr (hb p S f n F) asz osz K E).1 s
    ⟨hp.isSome, hp, hk, fun t ⟨harg, hpost⟩ => hx t hpost harg⟩

end FlatShuffler.Unit
