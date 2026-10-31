import BbuKraken.FlatList.Regroup
import BbuKraken.FlatList.Loop

/-!
The flat `permute` against the list `Bbu.permute` (`sim_permute`): the `leader` loop gives the
result of `Bbu.normalize` (`Regroup.lean`), and `permuteLoop` gives the result of `Bbu.go`
(`PermLoop.lean`). `permuteMapping` against `Bbu.finish` (`PermR`): `readDestinations` reads
the destinations of the list model, then `sim_permute`.
-/

namespace Bbu.Flat

-- `normalize` is the fold of `regroup` over the last copy of each slot, in order.
theorem normalize_eq (vals : List StackSlot) (p : List Nat) :
    normalize vals p = ((List.range' 0 vals.length).filter (isLast vals)).foldlM
      (fun q l => Bbu.regroup vals q vals[l]!) p := by
  rw [normalize, dedup_eq, List.foldlM_map, List.range_eq_range']

-- The measure of a permutation of a nonempty list is below twice its length.
theorem measure_lt {l : List Nat} (h : 0 < l.length) : PermuteKraken.measure l < 2 * l.length := by
  have := List.countP_le_length (p := fun i => decide (l[i]! ≠ i)) (l := List.range (l.length - 1))
  rw [List.length_range] at this
  unfold PermuteKraken.measure
  split <;> omega

-- The flat `permute` against the list `Bbu.permute`, for a permutation `l` of the slots that
-- `v` holds.
theorem sim_permute {e : Env} {fs : St} {st : Bbu.St} {v : Vector Word MAX_N} {l : List Nat}
    (hs : Sim e fs st) (hpv : PermV st.len v l) (hperm : IsPerm l) :
    SimR e (permute fs v) (Bbu.permute st l) := by
  have hN := hs.len_lt
  have hsz := hs.size
  have hn : fs.size.toNat ≤ MAX_N := by rw [hsz]; exact hN
  -- `desiredBy`
  have hdi : DInv st.len 0 (clearDesired fs 0 initial) := fun w hw => by
    rw [clearDesired_spec fs hn st.len 0 initial (by simp [hsz]) (by simp) w,
      ite_eq_left (c := (0 : Word).toNat ≤ w.toNat ∧ w.toNat < fs.size.toNat)
        ⟨by simp, by omega⟩]
    exact Or.inl rfl
  -- the `leader` loop
  obtain ⟨r, h1, out, h2, h3, h4⟩ :=
    sim_regroup hs st.len 0 v (clearDesired fs 0 initial) _ (by simp) (by simp) hpv hperm hdi
  have hnorm : normalize (st.slots.map Slot.val) l = .ok r := by
    rw [normalize_eq, List.length_map]; exact h1
  by_cases h0 : st.len = 0
  · have hf : fs.size = 0 := by bv_omega
    have e1 : permute fs v = (.done, fs) := by rw [permute, ite_eq_left hf]
    have e2 : Bbu.permute st l = .ok st := by
      unfold Bbu.permute
      rw [hnorm]
      exact (dite_eq_left h4).trans (ite_eq_left h0)
    rw [e1, e2]
    exact ⟨rfl, hs⟩
  · have hf : ¬fs.size = 0 := by bv_omega
    have e1 : permute fs v = permuteLoop (2 * fs.size.toNat) fs (fs.size - 1) out := by
      rw [permute, ite_eq_right hf]
      dsimp only
      rw [h2]
    have e2 : Bbu.permute st l = go st ⟨r, h4.1, fun i j hi hj => h4.2 i hi j hj⟩ := by
      unfold Bbu.permute
      rw [hnorm]
      exact (dite_eq_left h4).trans (ite_eq_right h0)
    rw [e1, e2]
    have hrl : r.length = st.len := h3.1
    exact sim_permuteLoop _ fs st _ out hs h3 (by omega) (by bv_omega)
      (by rw [hsz, ← hrl]; exact measure_lt (l := r) (by omega))

theorem permR (e : Env) : PermR e := by
  intro fs st t hs hi hp _
  have hN := hs.len_lt
  have hsz := hs.size
  have hn : fs.size.toNat ≤ MAX_N := by rw [hsz]; exact hN
  have hperm : IsPerm (st.slots.map Slot.dest) := hi.isPerm hp
  have hall : ((List.range st.len).all fun pos => (st.destinationOf pos).isSome) = true :=
    List.all_eq_true.2 fun pos hpos => by rw [St.destinationOf_eq (List.mem_range.1 hpos)]; rfl
  -- the destinations
  have hd : ∀ i : Word, i.toNat < fs.size.toNat → get fs.dest i ≠ NONE := fun i hi =>
    ne_NONE (by
      rw [hs.dest i (by omega)]
      have := hs.dest_lt (i := i.toNat) (by omega)
      rw [hs.n] at this; rw [MAX_N_eq] at hn; omega)
  obtain ⟨v, hv1, hv2⟩ := readDestinations_spec fs hn hd st.len 0 initial (by simp [hsz])
    (by simp)
  have hpv : PermV st.len v (st.slots.map Slot.dest) := ⟨by simp [Bbu.St.len], fun i hi => by
    rw [hv2 i, ite_eq_left (c := (0 : Word).toNat ≤ i.toNat ∧ i.toNat < fs.size.toNat)
      ⟨by simp, by omega⟩, hs.dest i hi, St.dest_eq]
    rfl⟩
  have hc : ¬((!(List.range st.len).all fun pos => (st.destinationOf pos).isSome) = true) := by
    rw [hall]; decide
  have e1 : permuteMapping fs = permute fs v := by rw [permuteMapping, hv1]
  have e2 : Bbu.finish st = Bbu.permute st (st.slots.map Slot.dest) := by
    unfold Bbu.finish
    rw [ite_eq_right hc]
  rw [e1, e2]
  exact sim_permute hs hpv hperm

end Bbu.Flat
