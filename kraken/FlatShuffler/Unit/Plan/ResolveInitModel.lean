module

public import FlatShuffler.Unit.Plan.ResolveCandidates
import all FlatShuffler.Unit.Plan.ResolveCandidates
public import FlatShuffler.Unit.Plan.ResolveLocalRead
import all FlatShuffler.Unit.Plan.ResolveLocalRead

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open Flat

theorem put_same {α : Type} [Inhabited α] (v : Vector α maxStackSize) (i : Word)
    (hi : i.toNat < maxStackSize) : put v i (get v i) = v := by
  apply Vector.ext
  intro j hj
  simp only [put, Vector.getElem_setIfInBounds hj, Flat.get, dite_eq_left hi]
  split
  · rename_i h; subst j; rfl
  · rfl

theorem zeroFrom_fixed (m o : Word) (dn : Vector (BitVec 8) maxStackSize)
    (hm : m.toNat ≤ maxStackSize) (hz : ∀ q : Word, q < m → get dn q = 0#8) :
    zeroFrom m o dn = dn := by
  rw [zeroFrom]
  split
  · rename_i ho
    have hp : put dn o 0#8 = dn := by
      rw [← hz o ho]
      exact put_same dn o (Nat.lt_of_lt_of_le (BitVec.lt_def.mp ho) hm)
    change zeroFrom m (o + 1) (put dn o 0#8) = dn
    rw [hp]
    exact zeroFrom_fixed m (o + 1) dn hm hz
  · rfl
termination_by (m - o).toNat
decreasing_by exact Flat.sub_succ_lt ‹o < m›

end FlatShuffler.Unit.ResolveU
