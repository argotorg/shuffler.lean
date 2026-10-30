import BbuKraken.Fn.Loop.Defs

/-!
Model lemmas of the proof of `loop_body`: `step` split at the cut labels, and the
facts that `Ctx` and `Iter` give.
-/

namespace Bbu

namespace Loop

variable {e : Env} {st st' : St} {t t' b p d u c : Nat}

/-! ## `step` -/

theorem step_done (h : t < st.len ∧ st.dest t = t) : step e st t = .ok (st, .next (t + 1)) := by
  simp [step, h]

theorem step_fin (h : ¬ (t < st.len ∧ st.dest t = t)) (hp : st.pendingGenerations = 0) :
    step e st t = .ok (st, .finish) := by
  simp [step, h, hp]

theorem step_urgent (h : ¬ (t < st.len ∧ st.dest t = t)) (hp : st.pendingGenerations ≠ 0) :
    step e st t = (urgentFrom e st t t e.n).bind (afterUrgent e st t) := by
  simp only [step, h, hp, ite_false]
  rfl

theorem takeBound_ge {r : St × Bool} (hpb : positionOf st t = some b) (h : takeBound st t = .ok r) :
    t ≤ b := by
  unfold takeBound at h
  rw [hpb] at h
  dsimp only at h
  split at h
  · cases h
  · omega

-- An iteration keeps `t ≤ len`.
theorem step_le {n : Nat} (hp : Pos n st) (hle : t ≤ st.len)
    (h : step e st t = .ok (st', .next t')) : t' ≤ st'.len := by
  unfold step at h
  split at h
  · cases h; omega
  split at h
  · cases h
  obtain ⟨u, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h; cases h; have := (generate_shape hs).1; omega
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h; cases h; have := (generate_shape hs).1; omega
  split at h
  · rename_i hs0
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs0
    obtain ⟨⟨s, done⟩, hs, h⟩ := bind_ok h
    have hb' := positionOf_some hp hb
    have h1 := (takeBound_shape hb' hb hs).1
    have h2 := takeBound_ge hb hs
    cases done
    · obtain ⟨h3, h4, -⟩ := placeTop_ok h
      cases h3
      have := (placeTop_shape h).1
      omega
    · cases h; dsimp only at h1; omega
  · obtain ⟨s, hs, h⟩ := bind_ok h
    have := (generate_shape hs).1
    split at h
    · cases h; omega
    · obtain ⟨h3, h4, -⟩ := placeTop_ok h
      cases h3
      have := (placeTop_shape h).1
      omega

/-! ## The loop head -/

section
variable {s : MachineData} {T T' : Nat} {st0 : St} {err : Err}

theorem ctx_iter (h : Ctx s T st0) : Iter s T (step (env s) st0 T) := ⟨st0, h, rfl⟩

theorem iter_next (h : Iter s T (.ok (st', .next T'))) :
    InvL (env s) st' T' ∧ loop finishC (env s) st' T' = R0 s := by
  obtain ⟨st0, ⟨hT, ⟨hi, hle⟩, hl⟩, hs⟩ := h
  exact ⟨⟨step_inv hi hT hs, step_le hi.pos hle hs⟩, (loop_next hT hs).symm.trans hl⟩

theorem iter_err (h : Iter s T (.error err)) : R0 s = .error err := by
  obtain ⟨st0, ⟨hT, -, hl⟩, hs⟩ := h
  exact hl.symm.trans (loop_error hT hs)

-- The loop at an offset `T ≥ n`.
theorem loop_end (hT : ¬ T < (env s).n) (hl : loop finishC (env s) st0 T = R0 s) :
    R0 s = if st0.len = (env s).n then .ok st0 else .error .assertion :=
  hl.symm.trans (loop_ge hT)

-- No slot is pending: the result is the final permutation.
theorem ctx_fin (h : Ctx s T st0) (ho : ¬ (T < st0.len ∧ st0.dest T = T))
    (hp : st0.pendingGenerations = 0) :
    R0 s = (if st0.len = (env s).n then finishC st0 else .error .assertion)
      ∧ IsPerm (st0.slots.map Slot.dest) ∧ st0.trace.length + 2 * st0.len ≤ 6 * (env s).n := by
  obtain ⟨hT, ⟨hi, -⟩, hl⟩ := h
  exact ⟨hl.symm.trans (loop_finish hT (step_fin ho hp)), hi.finish hp⟩

-- The bounds at a loop head.
theorem ctx_bounds (h : Ctx s T st0) :
    st0.len + st0.pendingGenerations = (env s).n ∧ (env s).n ≤ MAX_N ∧ T ≤ st0.len
      ∧ st0.trace.length + 2 * st0.pendingGenerations + 2 ≤ 4 * (env s).n := by
  obtain ⟨hT, ⟨hi, hle⟩, -⟩ := h
  have := hi.ops_le
  exact ⟨hi.len_pending, hi.n_le, hle, by omega⟩

-- The precondition of `generate` at a loop head.
theorem ctx_genA (h : Ctx s T st0) (hp : st0.pendingGenerations ≠ 0) :
    st0.len < MAX_N ∧ st0.trace.length + 2 ≤ 6 * (env s).n := by
  obtain ⟨h1, h2, -, h4⟩ := ctx_bounds h
  omega

-- The ops after `generate` at a loop head leave room for a swap.
theorem gen_ops (h : Ctx s T st0) (hg : generate (env s) st0 d = .ok st')
    : st'.trace.length < 6 * (env s).n := by
  obtain ⟨-, -, -, h4⟩ := ctx_bounds h
  have := (generate_shape hg).2.1
  omega

end

/-! ## The `urgentToDup` scan -/

theorem uf_end : urgentFrom e st t e.n u = .ok u := by
  rw [urgentFrom]; simp

-- The scan skips `d`.
theorem uf_skip (hd : d < e.n)
    (h : (positionOf st d).isSome
      ∨ (isJunk e.target[d]! || canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!) = true
      ∨ shallowestCopyPosition st e.target[d]! = none) :
    urgentFrom e st t d u = urgentFrom e st t (d + 1) u := by
  rw [urgentFrom, ite_eq_left hd]
  rcases h with h | h | h
  · rw [ite_eq_left h]
  · split
    · rfl
    · simp only [h, ite_true]
  · split
    · rfl
    · simp only [h]; split <;> rfl

-- A copy out of reach for a dup.
theorem uf_far (hd : d < e.n) (hp : positionOf st d = none)
    (hf : (isJunk e.target[d]! || canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!)
      = false)
    (hc : shallowestCopyPosition st e.target[d]! = some c) (hfar : MAX_DUP_DEPTH < st.len - 1 - c) :
    urgentFrom e st t d u = .error (.blocked c (st.len - 1 - c - MAX_DUP_DEPTH) st) := by
  rw [urgentFrom, ite_eq_left hd]
  simp only [hp, Option.isSome_none, Bool.false_eq_true, ite_false, hf, hc, hfar, ite_true]

-- A copy in reach for a dup.
theorem uf_near (hd : d < e.n) (hp : positionOf st d = none)
    (hf : (isJunk e.target[d]! || canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!)
      = false)
    (hc : shallowestCopyPosition st e.target[d]! = some c)
    (hnear : st.len - 1 - c ≤ MAX_DUP_DEPTH) :
    urgentFrom e st t d u = urgentFrom e st t (d + 1)
      (if st.len - 1 - c = MAX_DUP_DEPTH ∧ c ≠ t ∧ u = e.n then d else u) := by
  rw [urgentFrom, ite_eq_left hd]
  simp only [hp, Option.isSome_none, Bool.false_eq_true, ite_false, hf, hc, Nat.not_lt.mpr hnear]

/-! ## The branches of `step` -/

theorem au_gen (h : u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH) :
    afterUrgent e st t u = (generate e st u).map (·, .next t) := by
  simp only [afterUrgent, h, ne_eq, not_false_eq_true, and_self, ite_true]

theorem au_top (h : u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
      st.len < t + MAX_SWAP_DEPTH) :
    afterUrgent e st t u = (generate e st st.len).map (·, .next t) := by
  unfold afterUrgent
  rw [ite_eq_right (by omega), ite_eq_left h]

theorem au_bound (h1 : ¬ (u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH))
    (h2 : ¬ (u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
      st.len < t + MAX_SWAP_DEPTH)) :
    afterUrgent e st t u = bound e st t := by
  unfold afterUrgent
  rw [ite_eq_right h1, ite_eq_right h2]

theorem bound_none (h : positionOf st t = none) :
    bound e st t = (generate e st t).bind (afterGen t) := by
  simp only [bound, h, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem bound_lt (h : positionOf st t = some b) (hb : b < t) : bound e st t = .error .assertion := by
  simp [bound, h, takeBound, hb, Except.bind]

theorem bound_eq (h : positionOf st t = some b) (hb : t ≤ b) (hv : st.val t = st.val b) :
    bound e st t = .ok (swapDestinations st t b, .next (t + 1)) := by
  simp [bound, h, takeBound, Nat.not_lt.mpr hb, hv, Except.bind, afterTake]

theorem bound_pos (h : positionOf st t = some b) (hb : t ≤ b) (hv : st.val t ≠ st.val b) :
    bound e st t = afterPos st t b ((movableCopy st b).getD b) := by
  simp only [bound, h, Option.isSome_some, ite_true, takeBound, Nat.not_lt.mpr hb, hv, ite_false,
    afterPos]
  generalize (movableCopy st b).getD b = p
  split
  · rfl
  split
  · rfl
  split
  · split
    · rfl
    · cases swapWith (swapDestinations st p b) p <;> rfl
  · rfl

theorem ag_done (h : t < st.len ∧ st.dest t = t) : afterGen t st = .ok (st, .next (t + 1)) := by
  simp [afterGen, h]

theorem ag_top (h : ¬ (t < st.len ∧ st.dest t = t)) : afterGen t st = placeTop st t := by
  simp only [afterGen, h, ite_false]

/-! ## `movableCopy` -/

theorem movableCopy_last (hb : b + 1 = st.len) : movableCopy st b = none := by
  simp [movableCopy, show st.len - 1 - b = 0 by omega]

theorem movableCopy_eq (hb : b < st.len) : movableCopy st b = movFrom st b (st.len - 1) := by
  simp only [movableCopy, movFrom, show st.len - 1 + 1 = st.len by omega]

theorem movFrom_self : movFrom st b b = none := by
  simp [movFrom]

theorem movFrom_step {k : Nat} (hk : b < k) :
    movFrom st b k = if (st.val k == st.val b && st.dest k != k) then some k
      else movFrom st b (k - 1) := by
  unfold movFrom
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.range_succ, List.reverse_append, show j + 1 - b = (j - b) + 1 by omega]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.take_succ_cons, List.find?_cons, Nat.add_sub_cancel]
  split <;> simp_all

/-! ## `afterPos` -/

theorem ap_bad (hv : st.val p ≠ st.val b) : afterPos st t b p = .error .assertion := by
  unfold afterPos
  rw [ite_eq_left hv]

theorem ap_self (hv : st.val p = st.val b) (hp : p = t) : afterPos st t b p =
    .ok (swapDestinations st p b, .next (t + 1)) := by
  unfold afterPos; dsimp only
  rw [ite_eq_right (not_not_intro hv), ite_eq_left hp, hp]

theorem ap_top (hv : st.val p = st.val b) (hp : p ≠ t) (hl : p = st.len - 1) :
    afterPos st t b p = placeTop (swapDestinations st p b) t := by
  unfold afterPos; dsimp only
  rw [ite_eq_right (not_not_intro hv), (swapDest_shape st p b).1, ite_eq_right hp,
    ite_eq_right (by omega)]

theorem ap_far (hv : st.val p = st.val b) (hp : p ≠ t) (hl : p ≠ st.len - 1)
    (hf : MAX_SWAP_DEPTH < st.len - 1 - p) :
    afterPos st t b p =
      .error (.blocked p (st.len - 1 - p - MAX_SWAP_DEPTH) (swapDestinations st p b)) := by
  unfold afterPos; dsimp only
  rw [ite_eq_right (not_not_intro hv), (swapDest_shape st p b).1, ite_eq_right hp, ite_eq_left hl,
    ite_eq_left hf]

theorem ap_swap (hv : st.val p = st.val b) (hp : p ≠ t) (hl : p ≠ st.len - 1)
    (hf : st.len - 1 - p ≤ MAX_SWAP_DEPTH) :
    afterPos st t b p = (swapWith (swapDestinations st p b) p).bind (placeTop · t) := by
  unfold afterPos; dsimp only
  rw [ite_eq_right (not_not_intro hv), (swapDest_shape st p b).1, ite_eq_right hp, ite_eq_left hl,
    ite_eq_right (by omega)]

/-! ## `placeTop` -/

theorem pt_ge (h : st.len ≤ t) : placeTop st t = .error .assertion := by
  simp [placeTop, h]

theorem pt_fixed (h : st.dest t = t) : placeTop st t = .error .assertion := by
  simp [placeTop, h]

theorem pt_last (hlt : t < st.len) (hd : st.dest t ≠ t) (h : t = st.len - 1) :
    placeTop st t = .ok (st, .next (t + 1)) := by
  unfold placeTop
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem pt_far (hlt : t < st.len) (hd : st.dest t ≠ t) (h : t ≠ st.len - 1)
    (hf : MAX_SWAP_DEPTH < st.len - 1 - t) :
    placeTop st t = .error (.blocked t (st.len - 1 - t - MAX_SWAP_DEPTH) st) := by
  unfold placeTop
  rw [ite_eq_right (by omega), ite_eq_left h]
  simp [hf]

theorem pt_swap (hlt : t < st.len) (hd : st.dest t ≠ t) (h : t ≠ st.len - 1)
    (hf : st.len - 1 - t ≤ MAX_SWAP_DEPTH) :
    placeTop st t = (swapWith st t).map (·, .next (t + 1)) := by
  unfold placeTop
  rw [ite_eq_right (by omega), ite_eq_left h]
  simp [Nat.not_lt.mpr hf]

end Loop

end Bbu
