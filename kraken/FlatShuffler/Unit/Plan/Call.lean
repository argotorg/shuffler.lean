module

public import FlatShuffler.Unit.Plan.Frame
import all FlatShuffler.Unit.Plan.Frame

@[expose] public section

/-!
# A call from a planner unit

The frame of a unit is `lo ++ w :: hi`: `hi` holds the pushed registers, `w` is the return slot
of a callee and `lo` are the free words of the callee. Between the pushes and the pops `rsp` is
at `w + 8` (`Kb` with `d = 8 * hi.length`). `Kb.vcall` is the call rule of a callee with a
`VSpec`: the callee gets `lo` and `w`, and its frame is `hi`, the return slot of the unit and `F`.
-/

namespace FlatShuffler.Unit

open FlatShuffler.Sep

-- The free words and the return slot of a callee, under the words `hi`.
theorem Stk.callee (sp : Addr) (lo hi : List Word) (w v : Word) (P F : MProp 64) :
    Stk sp (lo ++ w :: hi) v ∗ (P ∗ F)
      = Stk (sp - 8#64 - BitVec.ofNat 64 (8 * hi.length)) lo w
        ∗ (P ∗ (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * hi.length)) hi ∗ Wd (sp - 8#64) v ∗ F)) := by
  have e0 : sp - 8#64 - BitVec.ofNat 64 (8 * (lo ++ w :: hi).length)
      = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 - BitVec.ofNat 64 (8 * lo.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, List.length_cons, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have e1 : sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 - BitVec.ofNat 64 (8 * lo.length)
      + BitVec.ofNat 64 (8 * lo.length) = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 :=
    BitVec.sub_add_cancel _ _
  have e2 : sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) - 8#64 + 8#64
      = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) := BitVec.sub_add_cancel _ _
  unfold Stk
  rw [e0, Arr.append, e1]
  simp only [Arr, e2, MProp.sep_assoc]
  rw [sep_lc (Wd (sp - 8#64) v) P, sep_lc (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * hi.length)) hi) P]

section
variable {P : MProp 64} {s t : MachineData} {ra : Int64} {lo hi : List Word} {d : Word}

-- The words `hi` of the frame are at `rsp`.
theorem Kb.arr_hi (h : Kb P s ra (lo ++ hi) d t) (hd : d = BitVec.ofNat 64 (8 * hi.length)) :
    ∃ R, (Arr t.regs.rsp.toBitVec hi ∗ R).get t.dmem := by
  have e : rsp s - 8#64 - BitVec.ofNat 64 (8 * (lo ++ hi).length) + BitVec.ofNat 64 (8 * lo.length)
      = t.regs.rsp.toBitVec := by
    rw [h.sp, hd]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hm := h.mem
  unfold Stk at hm
  rw [Arr.append, e, MProp.sep_assoc, MProp.sep_assoc, sep_lc] at hm
  exact ⟨_, hm⟩

theorem Kb.rd_hi (h : Kb P s ra (lo ++ hi) d t) (hd : d = BitVec.ofNat 64 (8 * hi.length))
    {i : Nat} (hlt : i < hi.length) :
    rd t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) = hi[i] :=
  let ⟨_, hm⟩ := h.arr_hi hd; Arr.rd hm hlt

theorem Kb.isSome_hi (h : Kb P s ra (lo ++ hi) d t) (hd : d = BitVec.ofNat 64 (8 * hi.length))
    {i : Nat} (hlt : i < hi.length) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8).isSome = true :=
  let ⟨_, hm⟩ := h.arr_hi hd; Arr.isSome hm hlt
end

section
variable {α : Type} {V : Addr → α → MProp 64} {ok : α → Prop}

-- The call rule of a callee with `k` free words.
theorem Kb.vcall {S : Addr} {a : α} {F : MProp 64} {s c : MachineData} {ra : Int64}
    {lo hi : List Word} {w d : Word} {k : Nat} {A : α → MachineData → Prop}
    {Q : α → α → MachineData → MachineData → Prop} {K : MachineData → Prop}
    (h : Kb (V S a ∗ F) s ra (lo ++ w :: hi) d c) (hd : d = BitVec.ofNat 64 (8 * hi.length))
    (hl : lo.length = k) (hdi : rdi c = S) (hok : ok a) (hA : A a c)
    (hK : ∀ t a' lo' w', Kb (V S a' ∗ F) s ra (lo' ++ w' :: hi) d t → lo'.length = k →
      Q a a' c t → ok a' → Sep.mod.Agree c t → K t) :
    ∃ S' a' F', VPre V ok S' a' F' A k c
      ∧ ∀ s', VPost V ok S' F' k (fun a'' t => Q a' a'' c t) c s' → Sep.mod.Agree c s'
        → K s' := by
  have hsp : rsp c = rsp s - 8#64 - BitVec.ofNat 64 (8 * hi.length) := by
    rw [rsp, Reg64s.get64_rsp, h.sp, hd]
  refine ⟨S, a, Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * hi.length)) hi
      ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F, ⟨hdi, hok, hA, lo, w, hl, ?_⟩,
    fun t ⟨a', hQ, hok', lo', w', hl', hm⟩ hag => hK t a' lo' w' ⟨?_, ?_⟩ hl' hQ hok' hag⟩
  · rw [hsp, ← Stk.callee]; exact h.mem
  · rw [hsp, ← Stk.callee] at hm; exact hm
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp

-- The lowest words `xs` of a frame are not in the frame of the callee.
theorem Stk.split (sp : Addr) (xs ys : List Word) (v : Word) (P : MProp 64) :
    Stk sp (xs ++ ys) v ∗ P
      = Stk sp ys v ∗ (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * (xs.length + ys.length))) xs ∗ P) := by
  have e : sp - 8#64 - BitVec.ofNat 64 (8 * (xs.length + ys.length)) + BitVec.ofNat 64 (8 * xs.length)
      = sp - 8#64 - BitVec.ofNat 64 (8 * ys.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  unfold Stk
  rw [List.length_append, Arr.append, e]
  simp only [MProp.sep_assoc]
  rw [sep_lc (Arr _ xs), sep_lc (Arr _ xs)]

-- The call rule of a callee with `k` free words, above the frame words `xs`.
theorem Kb.vcall_above {S : Addr} {a : α} {F : MProp 64} {s c : MachineData} {ra : Int64}
    {xs lo hi : List Word} {w d : Word} {k : Nat} {A : α → MachineData → Prop}
    {Q : α → α → MachineData → MachineData → Prop} {K : MachineData → Prop}
    (h : Kb (V S a ∗ F) s ra (xs ++ lo ++ w :: hi) d c) (hd : d = BitVec.ofNat 64 (8 * hi.length))
    (hl : lo.length = k) (hdi : rdi c = S) (hok : ok a) (hA : A a c)
    (hK : ∀ t a' lo' w', Kb (V S a' ∗ F) s ra (xs ++ lo' ++ w' :: hi) d t → lo'.length = k →
      Q a a' c t → ok a' → Sep.mod.Agree c t → K t) :
    ∃ S' a' F', VPre V ok S' a' F' A k c
      ∧ ∀ s', VPost V ok S' F' k (fun a'' t => Q a' a'' c t) c s' → Sep.mod.Agree c s'
        → K s' := by
  have split : ∀ (a : α) (lo : List Word) (w : Word) (u : MachineData), lo.length = k →
      ((Stk (rsp s) (xs ++ lo ++ w :: hi) ra.toBitVec ∗ V S a ∗ F).get u.dmem
        ↔ (Stk (rsp s) (lo ++ w :: hi) ra.toBitVec ∗ V S a
          ∗ (Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * (xs.length + (k + 1 + hi.length)))) xs ∗ F)).get
            u.dmem) := by
    intro a lo w u hl
    rw [List.append_assoc, Stk.split, sep_lc (Arr _ xs) (V S a)]
    simp only [List.length_append, List.length_cons, hl]
    rw [show k + (hi.length + 1) = k + 1 + hi.length by omega]
  exact Kb.vcall ⟨(split a lo w c hl).1 h.mem, h.sp⟩ hd hl hdi hok hA
    fun t a' lo' w' hkb hl' hQ hok' hag =>
      hK t a' lo' w' ⟨(split a' lo' w' t hl').2 hkb.mem, hkb.sp⟩ hl' hQ hok' hag
end

/-! ## `testb %al, %al` after a call -/

theorem al_zero {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = false) : al t = 0#8 := by
  simp only [Bool.not_eq_false', beq_iff_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

theorem al_ne {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = true) : al t ≠ 0#8 := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

theorem code_eq_zero {st : Flat.EmissionOutcome} (h : code st = some 0#8) : st = .done := by
  cases st with
  | returned status => cases status <;> revert h <;> decide
  | assertionExit => revert h; decide

theorem code_ne_zero {st : Flat.EmissionOutcome} (h : code st ≠ some 0#8) : st ≠ .done := by
  intro e; subst e; exact h rfl

end FlatShuffler.Unit
