module

public import BbuKraken.Unit.Plan.PlannerRunCtor
import all BbuKraken.Unit.Plan.PlannerRunCtor
public import BbuKraken.Unit.Run.Model
import all BbuKraken.Unit.Run.Model
public import BbuKraken.FlatLowestRel
import all BbuKraken.FlatLowestRel
public import BbuKraken.Unit.Loop.Model
import all BbuKraken.Unit.Loop.Model

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Flat

def exchangeAt (a b i : Word) : Word := if i = a then b else if i = b then a else i

theorem exchangeAt_self (a b i : Word) : exchangeAt a b (exchangeAt a b i) = i := by
  by_cases ha : i = a
  · subst i
    by_cases hb : a = b
    · simp [exchangeAt, hb]
    · simp [exchangeAt, Ne.symm hb]
  by_cases hb : i = b
  · subst i; simp [exchangeAt, ha]
  simp [exchangeAt, ha, hb]

theorem exchangeAt_lt {a b i n : Word} (ha : a < n) (hb : b < n) (hi : i < n) :
    exchangeAt a b i < n := by
  unfold exchangeAt
  split
  · exact hb
  · split
    · exact ha
    · exact hi

theorem swap_dest_read {st : Flat.St} {a b : Word}
    (ha : a.toNat < MAX_N) (hb : b.toNat < MAX_N) (i : Word) :
    get (Flat.swapDestinations st a b).dest i = get st.dest (exchangeAt a b i) := by
  change get (put (put st.dest a (get st.dest b)) b (get st.dest a)) i = _
  rw [get_put _ _ _ hb, get_put _ _ _ ha]
  by_cases hia : i = a <;> by_cases hib : i = b <;> simp_all [exchangeAt]

theorem optional_pos_read (v : Vector Word MAX_N) (key value d : Word)
    (hk : key = NONE ∨ key.toNat < MAX_N) :
    get (if key ≠ NONE then put v key value else v) d =
      if d = key ∧ key ≠ NONE then value else get v d := by
  by_cases hn : key = NONE
  · simp [hn]
  · simp [hn, get_put _ _ _ (hk.resolve_left hn)]

theorem MapInv.swap_pos_read {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) {a b : Word}
    (ha : a < st.size) (hb : b < st.size) {d : Word} (hd : d < st.targetSize) :
    get (Flat.swapDestinations st a b).pos d = exchangeAt a b (get st.pos d) := by
  have ma := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ha) h.m_bound
  have mb := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hb) h.m_bound
  have na : a ≠ NONE := Flat.ne_none ma
  have nb : b ≠ NONE := Flat.ne_none mb
  have nd : d ≠ NONE := Flat.ne_none
    (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hd) h.n_bound)
  have da := (h.dest a ha).imp_right
    (fun hx => Nat.lt_of_lt_of_le (BitVec.lt_def.mp hx) h.n_bound)
  have db := (h.dest b hb).imp_right
    (fun hx => Nat.lt_of_lt_of_le (BitVec.lt_def.mp hx) h.n_bound)
  have dA : get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a =
      if a = b then get st.dest a else get st.dest b := by
    rw [get_put _ _ _ mb, get_put_self _ _ ma]
  have dB : get (put (put st.dest a (get st.dest b)) b (get st.dest a)) b =
      get st.dest a := get_put_self _ _ mb
  change get
    (if get (put (put st.dest a (get st.dest b)) b (get st.dest a)) b ≠ NONE then
      put (if get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a ≠ NONE then
        put st.pos (get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a) a
        else st.pos)
        (get (put (put st.dest a (get st.dest b)) b (get st.dest a)) b) b
      else if get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a ≠ NONE then
        put st.pos (get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a) a
        else st.pos) d = _
  rw [dA, dB]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    rw [optional_pos_read _ _ _ _ da, optional_pos_read _ _ _ _ da]
    by_cases he : d = get st.dest a
    · have hn : get st.dest a ≠ NONE := he ▸ nd
      have hp := h.dest_inv a ha hn
      simp [he, hn, hp, exchangeAt]
    · have hpa : get st.pos d ≠ a := by
        intro hp
        have hi := h.pos_inv d hd (by rw [hp]; exact na)
        exact he (by simpa only [hp] using hi.symm)
      simp [he, hpa, exchangeAt]
  · rw [ite_eq_right hab, optional_pos_read _ _ _ _ da,
      optional_pos_read _ _ _ _ db]
    by_cases hda : d = get st.dest a
    · have hn : get st.dest a ≠ NONE := hda ▸ nd
      have hp := h.dest_inv a ha hn
      simp [hda, hn, hp, exchangeAt]
    by_cases hdb : d = get st.dest b
    · have hn : get st.dest b ≠ NONE := hdb ▸ nd
      have hp := h.dest_inv b hb hn
      have hne : get st.dest b ≠ get st.dest a := by simpa only [hdb] using hda
      simp [hdb, hne, hn, hp, exchangeAt, Ne.symm hab]
    · have hpa : get st.pos d ≠ a := by
        intro hp
        have hi := h.pos_inv d hd (by rw [hp]; exact na)
        exact hda (by simpa only [hp] using hi.symm)
      have hpb : get st.pos d ≠ b := by
        intro hp
        have hi := h.pos_inv d hd (by rw [hp]; exact nb)
        exact hdb (by simpa only [hp] using hi.symm)
      simp [hda, hdb, hpa, hpb, exchangeAt]

theorem MapInv.swapDestinations {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) {a b : Word}
    (ha : a < st.size) (hb : b < st.size) :
    MapInv st.size st.targetSize
      ⟨(Flat.swapDestinations st a b).dest, (Flat.swapDestinations st a b).pos⟩ := by
  have ma := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ha) h.m_bound
  have mb := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hb) h.m_bound
  refine ⟨h.m_bound, h.n_bound, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [swap_dest_read ma mb]
    exact h.dest _ (exchangeAt_lt ha hb hi)
  · intro d hd
    rw [h.swap_pos_read ha hb hd]
    rcases h.pos d hd with hn | hp
    · rw [hn]
      left
      simp [exchangeAt, Ne.symm (Flat.ne_none ma), Ne.symm (Flat.ne_none mb)]
    · exact Or.inr (exchangeAt_lt ha hb hp)
  · intro i hi hn
    rw [swap_dest_read ma mb] at hn ⊢
    rw [h.swap_pos_read ha hb ((h.dest _ (exchangeAt_lt ha hb hi)).resolve_left hn),
      h.dest_inv _ (exchangeAt_lt ha hb hi) hn, exchangeAt_self]
  · intro d hd hn
    rw [h.swap_pos_read ha hb hd] at hn ⊢
    have hp : get st.pos d ≠ NONE := by
      intro he
      simp [he, exchangeAt, Ne.symm (Flat.ne_none ma), Ne.symm (Flat.ne_none mb)] at hn
    rw [swap_dest_read ma mb, exchangeAt_self, h.pos_inv d hd hp]

theorem MapInv.pop_none {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩)
    (h0 : st.size ≠ 0#64) (hn : get st.dest (st.size - 1#64) = NONE) :
    MapInv (Flat.pop st).2.size (Flat.pop st).2.targetSize
      ⟨(Flat.pop st).2.dest, (Flat.pop st).2.pos⟩ := by
  rw [Pop.pop_none st h0 hn]
  refine ⟨?_, h.n_bound, ?_, ?_, ?_, ?_⟩
  · change (st.size - 1#64).toNat ≤ MAX_N
    have hm := h.m_bound
    bv_omega
  · intro i hi
    exact h.dest i (by bv_omega)
  · intro d hd
    rcases h.pos d hd with hp | hp
    · exact Or.inl hp
    · right
      have ht : get st.pos d ≠ st.size - 1#64 := by
        intro he
        have hne : get st.pos d ≠ NONE := Flat.ne_none
          (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) h.m_bound)
        have hi := h.pos_inv d hd hne
        rw [he, hn] at hi
        exact Flat.ne_none
          (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hd) h.n_bound) hi.symm
      bv_omega
  · intro i hi hne
    exact h.dest_inv i (by bv_omega) hne
  · intro d hd hne
    exact h.pos_inv d hd hne

end Bbu.Unit.PlannerRunU
