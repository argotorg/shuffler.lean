import BbuKraken.Unit.Plan.PlannerRunLowOk
import BbuKraken.Unit.Plan.PlannerRunLowest

namespace Bbu.Unit.PlannerRunU
open Flat

theorem MapInv.destOk {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) : DestOk st := by
  intro i hi
  exact (h.dest (.ofNat 64 i) (ofNat_lt_word h.m_bound hi)).imp_right BitVec.lt_def.mp

theorem Prep.lowest_ready {planned : Vector Word MAX_N} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) (hn : HasNoSurplus st) :
    st.trace.length + 2 * st.size.toNat ≤ 6 * st.targetSize.toNat + 4 * m ∧
      DestOk st ∧ Flat.LowOk planned st := by
  refine ⟨?_, h.map.destOk, lowOk_of_map h.map hn h.support⟩
  have hb := h.trace
  omega

theorem size_pend_nat {m p n : Word}
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N) (hp : p.toNat ≤ n.toNat)
    (hc : m + p = n) : m.toNat + p.toNat = n.toNat := by
  have hN : MAX_N = 1024 := rfl
  bv_omega

theorem checked_loop {st : Flat.St} (m : Nat)
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (hp : st.pend.toNat ≤ st.targetSize.toNat) (ht : st.trace.length ≤ 4 * m)
    (hc : RunU.checks st) : Flat.HInv st 0#64 (4 * m) := by
  refine ⟨hm.finv (size_pend_nat hm.m_bound hm.n_bound hp hc.1) hn, ?_, ?_⟩
  · simp
  · simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
    omega

theorem ctorP_safe {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    (data target : Vector StackSlot MAX_N) (spills : BitVec 32 → BitVec 8)
    (u : Flat.Uninit) :
    RunU.Safe M.pos (Flat.ctorP data m target n M spills u) (4 * m.toNat) := by
  let st := Flat.ctorP data m target n M spills u
  have hp := Prep.ctorP h data target spills u
  refine ⟨⟨?_, hp.map.destOk⟩, ?_, ?_⟩
  · have ht := hp.trace
    omega
  · intro hd
    obtain ⟨ha, hn⟩ := hp.removeSurplus hd
    exact ha.lowest_ready hn
  · intro l hd
    dsimp only
    intro hr hc
    obtain ⟨ha, hn⟩ := hp.removeSurplus hd
    have hlo := lowOk_of_map ha.map hn ha.support
    have he : Flat.permuteAtLowestHeight M.pos l (Flat.removeSurplus st).2 =
        (.done, (Flat.permuteAtLowestHeight M.pos l (Flat.removeSurplus st).2).2) :=
      Prod.ext hr rfl
    obtain ⟨hm, hno, hsz, htarget, hpend, htrace⟩ := lowest_preserves ha.map hn hlo he
    apply checked_loop m.toNat hm hno
    · rw [hpend, htarget]
      exact ha.pend
    · have ht := ha.trace
      omega
    · exact hc

end Bbu.Unit.PlannerRunU
