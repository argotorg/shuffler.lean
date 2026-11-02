module

public import FlatShuffler.Unit.Plan.Call
import all FlatShuffler.Unit.Plan.Call
public import FlatShuffler.Unit.Plan.ExitDefs
import all FlatShuffler.Unit.Plan.ExitDefs

@[expose] public section

namespace FlatShuffler.Unit

open FlatShuffler.Sep

section
variable {α : Type} {V : Addr → α → MProp 64} {ok : α → Prop}

-- Restore the caller's memory on a normal return and at an assertion exit.
theorem Kb.vcallWithExit {S : Addr} {a : α} {F : MProp 64} {s c : MachineData} {ra : Int64}
    {lo hi : List Word} {w d : Word} {k : Nat} {A : α → MachineData → Prop}
    {Q X : α → α → MachineData → MachineData → Prop} {K E : MachineData → Prop}
    (h : Kb (V S a ∗ F) s ra (lo ++ w :: hi) d c) (hd : d = BitVec.ofNat 64 (8 * hi.length))
    (hl : lo.length = k) (hdi : rdi c = S) (hok : ok a) (hA : A a c)
    (hK : ∀ t a' lo' w', Kb (V S a' ∗ F) s ra (lo' ++ w' :: hi) d t → lo'.length = k →
      Q a a' c t → ok a' → Sep.mod.Agree c t → K t)
    (hX : ∀ t a' lo' w', (Stk (rsp s) (lo' ++ w' :: hi) ra.toBitVec ∗ V S a' ∗ F).get t.dmem →
      lo'.length = k → X a a' c t → ok a' → t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' a' F', VPre V ok S' a' F' A k c
      ∧ (∀ t, VPost V ok S' F' k (fun a'' t => Q a' a'' c t) c t →
        Sep.mod.Agree c t → K t)
      ∧ (∀ t, VPost V ok S' F' k (fun a'' t => X a' a'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have hsp : rsp c = rsp s - 8#64 - BitVec.ofNat 64 (8 * hi.length) := by
    rw [rsp, Reg64s.get64_rsp, h.sp, hd]
  refine ⟨S, a, Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * hi.length)) hi
      ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F, ⟨hdi, hok, hA, lo, w, hl, ?_⟩, ?_, ?_⟩
  · rw [hsp, ← Stk.callee]; exact h.mem
  · rintro t ⟨a', hQ, hok', lo', w', hl', hm⟩ hag
    apply hK t a' lo' w' ?_ hl' hQ hok' hag
    refine ⟨?_, ?_⟩
    · rw [hsp, ← Stk.callee] at hm; exact hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
  · rintro t ⟨a', hrel, hok', lo', w', hl', hm⟩ harg
    rw [hsp, ← Stk.callee] at hm
    exact hX t a' lo' w' hm hl' hrel hok' harg

-- Preserve the lower frame words while a callee uses its own stack words.
theorem Kb.vcallWithExit_above {S : Addr} {a : α} {F : MProp 64} {s c : MachineData} {ra : Int64}
    {xs lo hi : List Word} {w d : Word} {k : Nat} {A : α → MachineData → Prop}
    {Q X : α → α → MachineData → MachineData → Prop} {K E : MachineData → Prop}
    (h : Kb (V S a ∗ F) s ra (xs ++ lo ++ w :: hi) d c)
    (hd : d = BitVec.ofNat 64 (8 * hi.length))
    (hl : lo.length = k) (hdi : rdi c = S) (hok : ok a) (hA : A a c)
    (hK : ∀ t a' lo' w', Kb (V S a' ∗ F) s ra (xs ++ lo' ++ w' :: hi) d t → lo'.length = k →
      Q a a' c t → ok a' → Sep.mod.Agree c t → K t)
    (hX : ∀ t a' lo' w',
      (Stk (rsp s) (xs ++ lo' ++ w' :: hi) ra.toBitVec ∗ V S a' ∗ F).get t.dmem →
      lo'.length = k → X a a' c t → ok a' → t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' a' F', VPre V ok S' a' F' A k c
      ∧ (∀ t, VPost V ok S' F' k (fun a'' t => Q a' a'' c t) c t →
        Sep.mod.Agree c t → K t)
      ∧ (∀ t, VPost V ok S' F' k (fun a'' t => X a' a'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have split : ∀ (a : α) (lo : List Word) (w : Word) (u : MachineData), lo.length = k →
      ((Stk (rsp s) (xs ++ lo ++ w :: hi) ra.toBitVec ∗ V S a ∗ F).get u.dmem
        ↔ (Stk (rsp s) (lo ++ w :: hi) ra.toBitVec ∗ V S a
          ∗ (Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * (xs.length + (k + 1 + hi.length)))) xs ∗ F)).get
            u.dmem) := by
    intro a lo w u hl
    rw [List.append_assoc, Stk.split, sep_lc (Arr _ xs) (V S a)]
    simp only [List.length_append, List.length_cons, hl]
    rw [show k + (hi.length + 1) = k + 1 + hi.length by omega]
  exact Kb.vcallWithExit ⟨(split a lo w c hl).1 h.mem, h.sp⟩ hd hl hdi hok hA
    (fun t a' lo' w' hb hl' hQ hok' hag =>
      hK t a' lo' w' ⟨(split a' lo' w' t hl').2 hb.mem, hb.sp⟩ hl' hQ hok' hag)
    (fun t a' lo' w' hm hl' hrel hok' harg =>
      hX t a' lo' w' ((split a' lo' w' t hl').2 hm) hl' hrel hok' harg)

end

end FlatShuffler.Unit
