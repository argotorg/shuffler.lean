import BbuKraken.Unit.Plan.PlannerRunMapping
import BbuKraken.Unit.Defs

/-! The live mapping bounds hold after the emission constructor copies it.
The constructor starts each attempt with an empty trace. -/

namespace Bbu.Unit.PlannerRunU
open Flat

theorem MapInv.dest_inj {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    {p q : Word} (hp : p < m) (hq : q < m) (hn : get M.dest p ≠ NONE)
    (he : get M.dest p = get M.dest q) : p = q := by
  have hnq : get M.dest q ≠ NONE := he ▸ hn
  have hp' := h.dest_inv p hp hn
  rw [he, h.dest_inv q hq hnq] at hp'
  exact hp'.symm

theorem MapInv.pos_inj {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    {p q : Word} (hp : p < n) (hq : q < n) (hn : get M.pos p ≠ NONE)
    (he : get M.pos p = get M.pos q) : p = q := by
  have hnq : get M.pos q ≠ NONE := he ▸ hn
  have hp' := h.pos_inv p hp hn
  rw [he, h.pos_inv q hq hnq] at hp'
  exact hp'.symm

theorem MapInv.finv {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩)
    (hc : st.size.toNat + st.pend.toNat = st.targetSize.toNat)
    (hn : ∀ i, i < st.size → get st.dest i ≠ NONE) : Flat.FInv st := by
  refine ⟨h.n_bound, hc, ?_, ?_, ?_⟩
  · intro i hi
    exact (h.dest i hi).resolve_left (hn i hi)
  · intro i hi
    exact h.dest_inv i hi (hn i hi)
  · intro d hd
    by_cases hp : get st.pos d = NONE
    · exact Or.inl hp
    · exact Or.inr ⟨(h.pos d hd).resolve_left hp, h.pos_inv d hd hp⟩

theorem copy_dest {m n : Word} {M : Flat.Mapping} (u : Flat.Mapping)
    (hm : m.toNat ≤ MAX_N) {p : Word} (hp : p < m) :
    get (u.copy M m n).dest p = get M.dest p := by
  have hpN : p.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hm
  simp only [Flat.Mapping.copy]
  rw [get_toNat _ hpN, Flat.copy_get _ _ _ hm hpN,
    ite_eq_left (BitVec.lt_def.mp hp)]
  exact (get_toNat _ hpN).symm

theorem copy_pos {m n : Word} {M : Flat.Mapping} (u : Flat.Mapping)
    (hn : n.toNat ≤ MAX_N) {t : Word} (ht : t < n) :
    get (u.copy M m n).pos t = get M.pos t := by
  have htN : t.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) hn
  simp only [Flat.Mapping.copy]
  rw [get_toNat _ htN, Flat.copy_get _ _ _ hn htN,
    ite_eq_left (BitVec.lt_def.mp ht)]
  exact (get_toNat _ htN).symm

theorem MapInv.copy {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    (u : Flat.Mapping) : MapInv m n (u.copy M m n) := by
  refine ⟨h.m_bound, h.n_bound, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [copy_dest u h.m_bound hp]
    exact h.dest p hp
  · intro t ht
    rw [copy_pos u h.n_bound ht]
    exact h.pos t ht
  · intro p hp hne
    rw [copy_dest u h.m_bound hp] at hne ⊢
    rw [copy_pos u h.n_bound ((h.dest p hp).resolve_left hne)]
    exact h.dest_inv p hp hne
  · intro t ht hne
    rw [copy_pos u h.n_bound ht] at hne ⊢
    rw [copy_dest u h.m_bound ((h.pos t ht).resolve_left hne)]
    exact h.pos_inv t ht hne

theorem ctorP_destOk {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    (data target : Vector StackSlot MAX_N) (spills : BitVec 32 → BitVec 8)
    (u : Flat.Uninit) : DestOk (Flat.ctorP data m target n M spills u) := by
  simp only [Flat.ctorP, Flat.pend_fold]
  intro i hi
  have hiN : i < MAX_N := Nat.lt_of_lt_of_le hi h.m_bound
  have hi64 : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [MAX_N] at hiN
    omega
  have hip : BitVec.ofNat 64 i < m := by simpa only [BitVec.lt_def, hi64] using hi
  rw [copy_dest ⟨u.dest, u.pos⟩ h.m_bound hip]
  exact (h.dest _ hip).imp_right BitVec.lt_def.mp

theorem ctorP_budget (m n : Word) (M : Flat.Mapping)
    (data target : Vector StackSlot MAX_N) (spills : BitVec 32 → BitVec 8)
    (u : Flat.Uninit) :
    (Flat.ctorP data m target n M spills u).trace.length +
        2 * (Flat.ctorP data m target n M spills u).size.toNat ≤ 6 * n.toNat + 4 * m.toNat := by
  simp only [Flat.ctorP, Flat.pend_fold, List.length_nil]
  omega

end Bbu.Unit.PlannerRunU
