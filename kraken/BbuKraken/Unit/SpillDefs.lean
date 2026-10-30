import BbuKraken.Unit.Defs
import BbuKraken.FlatSpill

/-!
# The contracts of the spill set unit

The unit is `SpillSet::add` (`c/bbu/<Names.spillSetAdd>.S`) and `spill_set`
(`c/bbu/spill_set.S`). These functions do not use `Emission`, so their contracts do not use
`Sep.View`: the memory part is the bytes of the spill set (`Sep.Spl`), the arrays of the
arguments, the stack below `rsp` (`Sep.Stk`) and a frame `F`. The body triples are `Sep.Body`.

- `AddPre` and `AddPost`: `rdi` is the `SpillSet` object `p`, which holds the pointer `S` to the
  bytes. The bytes of the ids below `n` are in the contract, and the id of a variable slot is
  below `n`. The result is `Flat.spillAdd`. `AddSpec` is the call rule; `addSpec_of_body` gives
  it from the unit theorem.
- `SetPre` and `SetPost`: the arguments of `spill_set`, and the result `Flat.spill_set`. The
  bytes of `spilled` are those of the ids below `Flat.ids idCount`: the ids that `spill_set`
  can read or write. `results` is the word at `rsp`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit

open Bbu.Sep

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
  mem : ∃ v, (Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [] v ∗ F).get s.dmem

-- `al` is the `Status` of `Flat.spillAdd`, and the bytes are its bytes.
def AddPost (p S : Addr) (f : BitVec 32 → BitVec 8) (n : Nat) (F : MProp 64)
    (s t : MachineData) : Prop :=
  al t = code (Flat.spillAdd f (StackSlot.ofWord (rsi s))).1
    ∧ ∃ v, (Wd p S ∗ Spl S (Flat.spillAdd f (StackSlot.ofWord (rsi s))).2 (List.range n)
      ∗ Stk (rsp s) [] v ∗ F).get t.dmem

-- The call rule of `SpillSet::add`: the caller gives the object, the bytes and the frame.
abbrev AddSpec [Host] [FunDecls] : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ p S f n F, AddPre p S f n F s
        ∧ ∀ s', AddPost p S f n F s s' → Sep.mod.Agree s s' → K () s' ⦄
      (Directive.instr (.regular asz osz
        (.call (.rel (.sub (.label Names.spillSetAdd) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem AddPre.isSome {p S : Addr} {f : BitVec 32 → BitVec 8} {n : Nat} {F : MProp 64}
    {s : MachineData} (h : AddPre p S f n F s) :
    (s.dmem.loadInt (s.regs.get64 .rsp - 8#64) 8).isSome = true := by
  obtain ⟨v, hm⟩ := h.mem
  obtain ⟨R, e⟩ : ∃ R, Wd p S ∗ Spl S f (List.range n) ∗ Stk (rsp s) [] v ∗ F
      = Wd (rsp s - 8#64) v ∗ R := ⟨_, by unfold Stk; ecancel⟩
  exact Wd.isSome (e ▸ hm)

theorem addSpec_of_body [Host] [FunDecls] {g₀ : Fragment}
    (hg : FunDecls.at (label Names.spillSetAdd) = some g₀)
    (hb : ∀ p S f n F, Body g₀.prog (AddPre p S f n F) (AddPost p S f n F)) : AddSpec := by
  intro asz osz K E
  refine ⟨fun s ⟨p, S, f, n, F, hp, hk⟩ => ?_⟩
  exact (Program.WP.callSpec_of_triple hg (hb p S f n F) asz osz K E).1 s ⟨hp.isSome, hp, hk⟩

/-! ## `spill_set` -/

-- The free words of the stack of `spill_set`: 6 pushed registers, 3 words of locals and the
-- return slot of `SpillSet::add`.
def setD : Nat := 10

-- The memory of `spill_set(idCount, spilled, adds, addCount, queries, queryCount, results)` in
-- the state `s` at the call: the bytes `f` of the ids at `spilled`, the words of `adds` and of
-- `queries`, the bytes `res` at `r`, the word `r` (`results`) at `rsp`, the stack below `rsp`
-- (the free words `fr` and the return slot `v`) and `F`.
def SetMem (s : MachineData) (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (fr : List Word) (v : Word) : MProp 64 :=
  Spl (rsi s) f (List.range (Flat.ids (rdi s))) ∗ Arr (rdx s) adds ∗ Arr (r8 s) queries
    ∗ Bs r res ∗ Wd (rsp s) r ∗ Stk (rsp s) fr v ∗ F

structure SetPre (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s : MachineData) : Prop where
  hadds : adds.length = (rcx s).toNat
  hqueries : queries.length = (r9 s).toNat
  hres : res.length = (r9 s).toNat
  mem : ∃ fr v, fr.length = setD ∧ (SetMem s f adds queries r res F fr v).get s.dmem

-- The result of the flat model for the arguments in `s`.
def setRes (s : MachineData) (f : BitVec 32 → BitVec 8) (adds queries : List Word)
    (res : List (BitVec 8)) : Word × (BitVec 32 → BitVec 8) × List (BitVec 8) :=
  Flat.spill_set (rdi s) f (adds.map StackSlot.ofWord) (queries.map StackSlot.ofWord) res

-- `rax` is the result of `Flat.spill_set`, and the memory holds its bytes.
def SetPost (f : BitVec 32 → BitVec 8) (adds queries : List Word) (r : Addr)
    (res : List (BitVec 8)) (F : MProp 64) (s t : MachineData) : Prop :=
  rax t = (setRes s f adds queries res).1
    ∧ ∃ fr v, fr.length = setD ∧ (SetMem s (setRes s f adds queries res).2.1 adds queries r
      (setRes s f adds queries res).2.2 F fr v).get t.dmem

end Bbu.Unit
