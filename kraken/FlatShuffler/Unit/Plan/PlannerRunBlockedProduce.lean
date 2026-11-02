module

public import FlatShuffler.Unit.Plan.PlannerRunBlockedBasic
import all FlatShuffler.Unit.Plan.PlannerRunBlockedBasic

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open Flat

theorem push_not_blocked (st : Flat.St) (x : StackSlot) (t : Word) :
    (Flat.push st x t).1 ≠ .blocked := by
  unfold Flat.push
  dsimp only
  split <;> simp

theorem dup_not_blocked (st : Flat.St) (c t : Word) :
    (Flat.dup st c t).1 ≠ .blocked := by
  unfold Flat.dup
  dsimp only
  split
  · simp
  · split <;> simp

theorem produce_fin_blocked {r : Flat.EmissionOutcome × Flat.St} {t : Word} {out : Flat.St}
    (hr : ProduceProof.fin r t = (.blocked, out)) : r = (.blocked, out) := by
  unfold ProduceProof.fin at hr
  split at hr
  · exact hr
  · split at hr <;> cases hr

theorem produce_blocked {st out : Flat.St} {t : Word}
    (hm : st.size.toNat ≤ maxStackSize) (hd : DestOk st)
    (hr : Flat.produce st t = (.blocked, out)) : BlockedBounds st.targetSize out := by
  rw [ProduceProof.produce_eq] at hr
  have ha := produce_fin_blocked hr
  unfold ProduceProof.act at ha
  split at ha
  · exact False.elim (push_not_blocked st _ t (congrArg Prod.fst ha))
  · rename_i hj
    split at ha
    · exact False.elim (dup_not_blocked st _ t (congrArg Prod.fst ha))
    · rename_i hdup
      unfold ProduceProof.tail at ha
      split at ha
      · exact False.elim (push_not_blocked st _ t (congrArg Prod.fst ha))
      · split at ha
        · rename_i hc
          have hu : Flat.isDupReachable st (Flat.shallowestCopyPosition st
              (get st.target t)) = false := by
            cases he : Flat.isDupReachable st (Flat.shallowestCopyPosition st
              (get st.target t))
            · rfl
            · exact False.elim (hdup ⟨hc, he⟩)
          exact blockDup_bounds hm hd (shallowestCopy_lt hc) hu ha
        · cases ha

theorem generate_blocked {st out : Flat.St} {t : Word} (hf : Flat.FInv st)
    (hr : Flat.generate st t = (.blocked, out)) : BlockedBounds st.targetSize out := by
  unfold Flat.generate at hr
  split at hr
  · cases hr
  · dsimp only at hr
    split at hr
    · exact produce_blocked (Nat.le_trans hf.size_le hf.n) hf.destOk hr
    · split at hr
      · split at hr
        · cases hr
        · split at hr
          · exact False.elim (Flat.swapWith_status _ _ (congrArg Prod.fst hr))
          · cases hr
      · cases hr

end FlatShuffler.Unit.PlannerRunU
