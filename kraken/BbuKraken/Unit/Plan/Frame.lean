module

public import BbuKraken.Unit.Plan.Defs
import all BbuKraken.Unit.Plan.Defs

@[expose] public section

/-!
# The frame of a planner unit

A unit that pushes registers keeps them in the free words `fr` of its `Kg` stack. Word `x` of
`lo ++ x :: hi` is at `sp - 8 - 8 * (hi.length + 1)`: a `pushq` stores to the top free word, and
the next `pushq` to the word under it. `Kb` is the body state between the pushes and the pops:
the memory of `Kg`, and `rsp` is `d` bytes below the return address.
-/

namespace Bbu.Unit

open Bbu.Sep

/-! ## The words of the stack -/

section
variable {sp a : Addr} {lo hi : List Word} {x v : Word} {P : MProp 64} {m : Mem 64}

theorem Stk.wd_focus (sp : Addr) (lo hi : List Word) (v : Word) (P : MProp 64) :
    ∃ R, ∀ x, Stk sp (lo ++ x :: hi) v ∗ P
      = Wd (sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1))) x ∗ R := by
  refine ⟨Arr (sp - 8#64 - BitVec.ofNat 64 (8 * (lo.length + (hi.length + 1)))) lo
    ∗ Arr (sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1)) + 8#64) hi ∗ Wd (sp - 8#64) v ∗ P,
    fun x => ?_⟩
  have e : sp - 8#64 - BitVec.ofNat 64 (8 * (lo.length + (hi.length + 1)))
      + BitVec.ofNat 64 (8 * lo.length) = sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  unfold Stk
  rw [List.length_append, List.length_cons, Arr.append, e]
  simp only [Arr, MProp.sep_assoc]
  exact sep_lc _ _ _

theorem Stk.wd_isSome (h : (Stk sp (lo ++ x :: hi) v ∗ P).get m)
    (ha : a = sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1))) :
    (m.loadInt a 8).isSome = true := by
  obtain ⟨R, e⟩ := Stk.wd_focus sp lo hi v P
  rw [e] at h
  exact ha ▸ Wd.isSome h

theorem Stk.wd_rd (h : (Stk sp (lo ++ x :: hi) v ∗ P).get m)
    (ha : a = sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1))) : rd m a = x := by
  obtain ⟨R, e⟩ := Stk.wd_focus sp lo hi v P
  rw [e] at h
  exact ha ▸ Wd.rd h

theorem Stk.wd_store (h : (Stk sp (lo ++ x :: hi) v ∗ P).get m)
    (ha : a = sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1))) (w : Word) :
    (Stk sp (lo ++ w :: hi) v ∗ P).get (m.storeInt a 8 w.toInt) := by
  obtain ⟨R, e⟩ := Stk.wd_focus sp lo hi v P
  rw [e] at h ⊢
  exact ha ▸ Wd.store h w

end

/-! ## The body state -/

structure Kb (P : MProp 64) (s : MachineData) (ra : Int64) (fr : List Word) (d : Word)
    (t : MachineData) : Prop where
  mem : (Stk (rsp s) fr ra.toBitVec ∗ P).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 8#64 - d

section
variable {P : MProp 64} {s t t' : MachineData} {ra : Int64} {fr : List Word} {d : Word}

theorem Kb.next (h : Kb P s ra fr d t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp) :
    Kb P s ra fr d t' :=
  ⟨hm ▸ h.mem, hsp ▸ h.sp⟩

theorem Kb.stack (h : Kb P s ra fr d t) (hd : d.toNat < 2 ^ 63) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    rwa [show ∀ a : Word, a - (a - d) = d from fun _ => by bv_omega])

-- The state after the pops: all callee-saved registers have their values at the call.
theorem Kb.kg (h : Kb P s ra fr d t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec = rsp s - 8#64) (hbx : t'.regs.rbx = s.regs.rbx)
    (hbp : t'.regs.rbp = s.regs.rbp) (h12 : t'.regs.r12 = s.regs.r12)
    (h13 : t'.regs.r13 = s.regs.r13) (h14 : t'.regs.r14 = s.regs.r14)
    (h15 : t'.regs.r15 = s.regs.r15) : Kg P s ra fr t' :=
  ⟨hm ▸ h.mem, UInt64.toBitVec_inj.mp hsp, hbx, hbp, h12, h13, h14, h15⟩

end

/-! ## The pushes and the pops -/

-- The memory after `pushq x₁; …; pushq xₖ` from `rsp = q`.
def pushes (m : Mem 64) (q : Addr) : List Word → Mem 64
  | [] => m
  | x :: xs => pushes (m.storeInt (q - 8#64) 8 x.toInt) (q - 8#64) xs

-- The words that the pushes write are in the memory.
def PushOk (m : Mem 64) (q : Addr) : List Word → Prop
  | [] => True
  | x :: xs => (m.loadInt (q - 8#64) 8).isSome = true
      ∧ PushOk (m.storeInt (q - 8#64) 8 x.toInt) (q - 8#64) xs

section
variable {sp : Addr} {v : Word} {P : MProp 64}

theorem Stk.pushes : ∀ {xs lo hi : List Word} {m : Mem 64} {q : Addr},
    (Stk sp (lo ++ hi) v ∗ P).get m → q = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) →
    xs.length ≤ lo.length →
    PushOk m q xs
      ∧ (Stk sp (lo.take (lo.length - xs.length) ++ (xs.reverse ++ hi)) v ∗ P).get (pushes m q xs)
  | [], lo, hi, m, q, h, _, _ => ⟨trivial, by simpa [Unit.pushes] using h⟩
  | x :: xs, lo, hi, m, q, h, hq, hl => by
    obtain ⟨lo', y, rfl⟩ : ∃ lo' y, lo = lo' ++ [y] :=
      ⟨lo.dropLast, lo.getLast (by rintro rfl; simp at hl), (List.dropLast_concat_getLast _).symm⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    have ha : q - 8#64 = sp - 8#64 - BitVec.ofNat 64 (8 * (hi.length + 1)) := by
      subst hq
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    rw [List.append_assoc, List.singleton_append] at h
    have ih := Stk.pushes (xs := xs) (lo := lo') (hi := x :: hi) (q := q - 8#64)
      (Stk.wd_store h ha x)
      (by rw [List.length_cons]; exact ha) (by omega)
    refine ⟨⟨Stk.wd_isSome h ha, ih.1⟩, ?_⟩
    have e : (lo' ++ [y]).take ((lo' ++ [y]).length - (x :: xs).length)
        = lo'.take (lo'.length - xs.length) := by
      rw [List.take_append_of_le_length
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
      congr 1
      simp
    rw [e, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih.2
end

section
variable {P : MProp 64} {s t : MachineData} {ra : Int64} {fr xs : List Word} {d : Word}

-- `pushq x₁; …; pushq xₖ` at the entry of a body.
theorem Kg.pushes (h : Kg P s ra fr t) (hl : xs.length ≤ fr.length) :
    PushOk t.dmem t.regs.rsp.toBitVec xs
      ∧ (Stk (rsp s) (fr.take (fr.length - xs.length) ++ xs.reverse) ra.toBitVec ∗ P).get
        (pushes t.dmem t.regs.rsp.toBitVec xs) := by
  have hq : t.regs.rsp.toBitVec = rsp s - 8#64 - BitVec.ofNat 64 (8 * ([] : List Word).length) := by
    rw [← Reg64s.get64_rsp, h.sp64]; simp
  have := Stk.pushes (xs := xs) (lo := fr) (hi := []) (by simpa using h.mem) hq hl
  simpa using this

-- Word `i` of the frame of a body with `rsp` at the lowest word.
theorem Kb.rd_fr (h : Kb P s ra fr d t) (hd : d = BitVec.ofNat 64 (8 * fr.length)) {i : Nat}
    (hi : i < fr.length) : rd t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) = fr[i] := by
  have hm := h.mem
  unfold Stk at hm
  rw [MProp.sep_assoc] at hm
  rw [h.sp, hd]
  exact Arr.rd hm hi

theorem Kb.isSome_fr (h : Kb P s ra fr d t) (hd : d = BitVec.ofNat 64 (8 * fr.length)) {i : Nat}
    (hi : i < fr.length) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  have hm := h.mem
  unfold Stk at hm
  rw [MProp.sep_assoc] at hm
  rw [h.sp, hd]
  exact Arr.isSome hm hi
end

end Bbu.Unit
