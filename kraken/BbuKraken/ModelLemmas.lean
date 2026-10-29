import BbuKraken.Model
import PermuteKraken.Trace

/-!
Lemmas about the model: the shape of each action, the invariant of
`buildBottomUp.loop`, the bounds at `finish`, the unfolding of `loop`, and the
congruence of `buildBottomUp` in the spilled bytes that it reads.
-/

namespace Bbu

open PermuteKraken (swapEntries)

/-! ## Destinations -/

def St.dests (st : St) : List Nat := st.slots.map Slot.dest

-- The destinations are distinct and below `n`.
def Dests (n : Nat) (l : List Nat) : Prop :=
  (∀ i (h : i < l.length), l[i] < n) ∧
    ∀ i (hi : i < l.length) j (hj : j < l.length), l[i] = l[j] → i = j

theorem St.length_dests (st : St) : st.dests.length = st.len := by
  simp [St.dests, St.len]

theorem Dests.append {n d : Nat} {l : List Nat} (h : Dests n l) (hd : d < n) (hl : d ∉ l) :
    Dests n (l ++ [d]) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rw [List.getElem_append]
    split
    · exact h1 i _
    · simpa using hd
  · intro i hi j hj hij
    simp only [List.length_append, List.length_singleton] at hi hj
    rw [List.getElem_append, List.getElem_append] at hij
    split at hij <;> split at hij
    · exact h2 i _ j _ hij
    · simp at hij; exact absurd (hij ▸ List.getElem_mem _) hl
    · simp at hij; exact absurd (hij ▸ List.getElem_mem _) hl
    · omega

theorem Dests.swap {n a b : Nat} {l : List Nat} (h : Dests n l) (ha : a < l.length)
    (hb : b < l.length) : Dests n (swapEntries l a b) := by
  obtain ⟨h1, h2⟩ := h
  unfold swapEntries
  constructor
  · intro i hi
    simp only [List.length_set] at hi
    simp only [List.getElem_set, getElem!_pos l a ha, getElem!_pos l b hb]
    split
    · exact h1 a ha
    · split
      · exact h1 b hb
      · exact h1 i hi
  · intro i hi j hj hij
    simp only [List.length_set] at hi hj
    simp only [List.getElem_set, getElem!_pos l a ha, getElem!_pos l b hb] at hij
    have := h2 a ha b hb
    have := h2 i hi a ha
    have := h2 i hi b hb
    have := h2 j hj a ha
    have := h2 j hj b hb
    have := h2 i hi j hj
    split at hij <;> split at hij <;> (try split at hij) <;> (try split at hij) <;> grind

theorem St.dest_eq (st : St) (i : Nat) : st.dest i = st.dests[i]! := by
  simp [St.dest, St.dests, getElem!_def]
  cases st.slots[i]? <;> rfl

theorem swapDest_dests (st : St) (a b : Nat) :
    (swapDestinations st a b).dests = swapEntries st.dests a b := by
  simp [swapDestinations, St.dests, swapEntries, List.map_set, St.dest_eq]

theorem positionOf_none {st : St} {d : Nat} (h : positionOf st d = none) : d ∉ st.dests := by
  simp only [positionOf, List.findIdx?_eq_none_iff] at h
  simp only [St.dests, List.mem_map, not_exists, not_and]
  intro x hx hd
  have := h x hx
  simp [hd] at this

theorem positionOf_some {st : St} {d b : Nat} (h : positionOf st d = some b) : b < st.len := by
  simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hb, -⟩ := h
  exact hb

theorem shallowestCopy_lt {st : St} {v : Word} {c : Nat}
    (h : shallowestCopyPosition st v = some c) :
    c < st.len := by
  simpa using List.mem_reverse.mp (List.mem_of_find?_eq_some h)

/-! ## Shape of the actions -/

theorem add_ok {st st' : St} {v : Word} {d : Nat} {op : Op} (h : add st v d op = .ok st') :
    positionOf st d = none
      ∧ st' = { st with slots := st.slots ++ [⟨v, d⟩], trace := st.trace ++ [op] } := by
  unfold add at h
  split at h
  · cases h
  · cases h; rename_i hp; exact ⟨Option.not_isSome_iff_eq_none.mp hp, rfl⟩

theorem add_shape {st st' : St} {v : Word} {d : Nat} {op : Op} (h : add st v d op = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace = st.trace ++ [op]
      ∧ st'.pendingGenerations = st.pendingGenerations
      ∧ st'.slots = st.slots ++ [⟨v, d⟩] := by
  obtain ⟨-, rfl⟩ := add_ok h
  simp [St.len]

theorem add_dests {st st' : St} {v : Word} {d : Nat} {op : Op} (h : add st v d op = .ok st') :
    d ∉ st.dests ∧ st'.dests = st.dests ++ [d] := by
  obtain ⟨hp, rfl⟩ := add_ok h
  exact ⟨positionOf_none hp, by simp [St.dests]⟩

theorem swapWith_ok {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    pos < st.len ∧ 1 ≤ st.len - 1 - pos ∧ st.len - 1 - pos ≤ MAX_SWAP_DEPTH ∧
      st' = { st with
        slots := (st.slots.set pos ⟨st.val (st.len - 1), st.dest (st.len - 1)⟩).set (st.len - 1)
          ⟨st.val pos, st.dest pos⟩
        trace := st.trace ++ [.swap (st.len - 1 - pos)] } := by
  unfold swapWith at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; rename_i h1 h2; exact ⟨by omega, by omega, by omega, rfl⟩

theorem swapWith_shape {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    st'.len = st.len ∧ st'.trace.length = st.trace.length + 1
      ∧ st'.pendingGenerations = st.pendingGenerations := by
  obtain ⟨-, -, -, rfl⟩ := swapWith_ok h
  simp [St.len]

theorem swapWith_dests {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    pos < st.len ∧ st'.dests = swapEntries st.dests pos (st.len - 1) := by
  obtain ⟨hp, -, -, rfl⟩ := swapWith_ok h
  exact ⟨hp, by simp [St.dests, swapEntries, List.map_set, St.dest_eq]⟩

theorem swapDest_shape (st : St) (a b : Nat) :
    (swapDestinations st a b).len = st.len ∧ (swapDestinations st a b).trace = st.trace
      ∧ (swapDestinations st a b).pendingGenerations = st.pendingGenerations := by
  simp [swapDestinations, St.len]

theorem emit_add {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    ∃ v op, add st v d op = .ok st' := by
  unfold emit at h
  dsimp only at h
  repeat' split at h
  all_goals first | exact ⟨_, _, h⟩ | cases h

theorem emit_shape {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace.length = st.trace.length + 1
      ∧ st'.pendingGenerations = st.pendingGenerations := by
  obtain ⟨v, op, h⟩ := emit_add h
  obtain ⟨h1, h2, h3, -⟩ := add_shape h
  simp [h1, h2, h3]

theorem produce_ok {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    ∃ s, emit e st d = .ok s ∧ st' = { s with pendingGenerations := s.pendingGenerations - 1 } := by
  obtain ⟨s, hs, h⟩ := bind_ok h
  split at h
  · cases h
  · cases h; exact ⟨s, hs, rfl⟩

theorem produce_shape {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace.length = st.trace.length + 1
      ∧ st'.pendingGenerations = st.pendingGenerations - 1 := by
  obtain ⟨s, hs, rfl⟩ := produce_ok h
  obtain ⟨h1, h2, h3⟩ := emit_shape hs
  simp [St.len] at h1 ⊢
  simp [h1, h2, h3]

theorem produce_dests {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    d ∉ st.dests ∧ st'.dests = st.dests ++ [d] := by
  obtain ⟨s, hs, rfl⟩ := produce_ok h
  obtain ⟨v, op, h⟩ := emit_add hs
  exact add_dests (st' := s) h

theorem generate_ok {e : Env} {st st' : St} {d : Nat} (h : generate e st d = .ok st') :
    d < e.n ∧ ∃ s, produce e st d = .ok s ∧
      (st' = s ∨ (d + 1 < s.len ∧ st' = swapDestinations s d (s.len - 1))
         ∨ swapWith s d = .ok st') := by
  unfold generate at h
  split at h
  · cases h
  · obtain ⟨s, hs, h⟩ := bind_ok h
    refine ⟨by omega, s, hs, ?_⟩
    dsimp only at h
    split at h
    · rename_i hc
      split at h
      · cases h; exact .inr (.inl ⟨hc.1, rfl⟩)
      · split at h
        · exact .inr (.inr h)
        · cases h; exact .inl rfl
    · cases h; exact .inl rfl

theorem generate_shape {e : Env} {st st' : St} {d : Nat} (h : generate e st d = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace.length ≤ st.trace.length + 2
      ∧ st'.pendingGenerations = st.pendingGenerations - 1 := by
  obtain ⟨-, s, hs, h⟩ := generate_ok h
  obtain ⟨h1, h2, h3⟩ := produce_shape hs
  rcases h with rfl | ⟨-, rfl⟩ | h
  · omega
  · obtain ⟨h4, h5, h6⟩ := swapDest_shape s d (s.len - 1)
    rw [h5]
    omega
  · obtain ⟨h4, h5, h6⟩ := swapWith_shape h
    omega

theorem generate_dests {e : Env} {st st' : St} {d : Nat} (h : generate e st d = .ok st')
    (hd : Dests e.n st.dests) : Dests e.n st'.dests := by
  obtain ⟨hn, s, hs, h⟩ := generate_ok h
  obtain ⟨hm, hds⟩ := produce_dests hs
  have hs' : Dests e.n s.dests := hds ▸ hd.append hn hm
  have hl := s.length_dests
  rcases h with rfl | ⟨hlt, rfl⟩ | h
  · exact hs'
  · rw [swapDest_dests]; exact hs'.swap (by omega) (by omega)
  · obtain ⟨hp, h⟩ := swapWith_dests h
    rw [h]; exact hs'.swap (by omega) (by omega)

theorem movableCopy_lt {st : St} {b c : Nat} (h : movableCopy st b = some c) : c < st.len := by
  have := List.mem_of_find?_eq_some h
  simpa using List.mem_of_mem_take this

theorem takeBound_ok {st : St} {t b : Nat} {r : St × Bool} (hb : b < st.len)
    (h : takeBound st t b = .ok r) :
    ∃ pos, pos < st.len ∧ (r.1 = swapDestinations st pos b
      ∨ swapWith (swapDestinations st pos b) pos = .ok r.1) := by
  unfold takeBound at h
  split at h
  · cases h
  rename_i hbt
  dsimp only at h
  have hpos : (if st.val t = st.val b then t else (movableCopy st b).getD b) < st.len := by
    split
    · omega
    · cases hc : movableCopy st b
      · exact hb
      · exact movableCopy_lt hc
  generalize (if st.val t = st.val b then t else (movableCopy st b).getD b) = pos at h hpos
  refine ⟨pos, hpos, ?_⟩
  repeat' split at h
  all_goals first
    | (cases h; exact .inl rfl)
    | cases h
    | (obtain ⟨s, hs, h⟩ := map_ok h; cases h; exact .inr hs)

theorem takeBound_shape {st : St} {t b : Nat} {r : St × Bool} (hb : b < st.len)
    (h : takeBound st t b = .ok r) :
    r.1.len = st.len ∧ r.1.trace.length ≤ st.trace.length + 1
      ∧ r.1.pendingGenerations = st.pendingGenerations := by
  obtain ⟨pos, -, h | h⟩ := takeBound_ok hb h
  · rw [h]
    obtain ⟨h1, h2, h3⟩ := swapDest_shape st pos b
    rw [h2]; omega
  · obtain ⟨h1, h2, h3⟩ := swapDest_shape st pos b
    obtain ⟨h4, h5, h6⟩ := swapWith_shape h
    rw [h2] at h5; omega

theorem takeBound_dests {n : Nat} {st : St} {t b : Nat} {r : St × Bool} (hb : b < st.len)
    (h : takeBound st t b = .ok r) (hd : Dests n st.dests) : Dests n r.1.dests := by
  obtain ⟨pos, hpos, h⟩ := takeBound_ok hb h
  have hl := st.length_dests
  have h1 : Dests n (swapDestinations st pos b).dests := by
    rw [swapDest_dests]; exact hd.swap (by omega) (by omega)
  rcases h with h | h
  · rw [h]; exact h1
  · obtain ⟨hp, h⟩ := swapWith_dests h
    have := (swapDestinations st pos b).length_dests
    rw [h]; exact h1.swap (by omega) (by omega)

theorem placeTop_ok {st st' : St} {t : Nat} {nx : Next} (h : placeTop st t = .ok (st', nx)) :
    nx = .next (t + 1) ∧ t < st.len ∧ (st' = st ∨ swapWith st t = .ok st') := by
  refine ⟨placeTop_next h, ?_⟩
  unfold placeTop at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; rename_i h1; exact ⟨by omega, .inl rfl⟩)
    | (cases h; rename_i h1 _; exact ⟨by omega, .inl rfl⟩)
    | cases h
    | (obtain ⟨s, hs, h⟩ := map_ok h; cases h; exact ⟨(swapWith_ok hs).1, .inr hs⟩)

theorem placeTop_shape {st st' : St} {t : Nat} {nx : Next} (h : placeTop st t = .ok (st', nx)) :
    st'.len = st.len ∧ st'.trace.length ≤ st.trace.length + 1
      ∧ st'.pendingGenerations = st.pendingGenerations := by
  obtain ⟨-, -, rfl | h⟩ := placeTop_ok h
  · omega
  · obtain ⟨h1, h2, h3⟩ := swapWith_shape h
    omega

theorem placeTop_dests {n : Nat} {st st' : St} {t : Nat} {nx : Next}
    (h : placeTop st t = .ok (st', nx)) (hd : Dests n st.dests) : Dests n st'.dests := by
  obtain ⟨-, -, rfl | h⟩ := placeTop_ok h
  · exact hd
  · obtain ⟨hp, h⟩ := swapWith_dests h
    have := st.length_dests
    rw [h]; exact hd.swap (by omega) (by omega)

-- The four ways of an iteration that continues.
theorem step_next {e : Env} {st st' : St} {t t' : Nat} (h : step e st t = .ok (st', .next t')) :
    (t' = t + 1 ∧ st' = st)
    ∨ (t' = t ∧ 0 < st.pendingGenerations ∧ ∃ d, generate e st d = .ok st')
    ∨ (t' = t + 1 ∧ ∃ b r, positionOf st t = some b ∧ takeBound st t b = .ok r ∧
        (st' = r.1 ∨ ∃ nx, placeTop r.1 t = .ok (st', nx)))
    ∨ (t' = t + 1 ∧ 0 < st.pendingGenerations ∧ ∃ s, generate e st t = .ok s ∧
        (st' = s ∨ ∃ nx, placeTop s t = .ok (st', nx))) := by
  unfold step at h
  split at h
  · cases h; exact .inl ⟨rfl, rfl⟩
  split at h
  · cases h
  rename_i hp
  obtain ⟨u, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h
    cases h
    exact .inr (.inl ⟨rfl, by omega, _, hs⟩)
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h
    cases h
    exact .inr (.inl ⟨rfl, by omega, _, hs⟩)
  split at h
  · rename_i b hb
    obtain ⟨⟨s, done⟩, hs, h⟩ := bind_ok h
    cases done
    · cases placeTop_next h
      exact .inr (.inr (.inl ⟨rfl, b, _, hb, hs, .inr ⟨_, h⟩⟩))
    · cases h
      exact .inr (.inr (.inl ⟨rfl, b, _, hb, hs, .inl rfl⟩))
  · obtain ⟨s, hs, h⟩ := bind_ok h
    split at h
    · cases h
      exact .inr (.inr (.inr ⟨rfl, by omega, _, hs, .inl rfl⟩))
    · cases placeTop_next h
      exact .inr (.inr (.inr ⟨rfl, by omega, s, hs, .inr ⟨_, h⟩⟩))

theorem step_finish {e : Env} {st st' : St} {t : Nat} (h : step e st t = .ok (st', .finish)) :
    st' = st ∧ st.pendingGenerations = 0 := by
  unfold step at h
  split at h
  · cases h
  split at h
  · cases h; rename_i hp; exact ⟨rfl, hp⟩
  obtain ⟨u, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨s, _, h⟩ := map_ok h; cases h
  split at h
  · obtain ⟨s, _, h⟩ := map_ok h; cases h
  split at h
  · obtain ⟨⟨s, done⟩, _, h⟩ := bind_ok h
    cases done
    · cases placeTop_next h
    · cases h
  · obtain ⟨s, _, h⟩ := bind_ok h
    split at h
    · cases h
    · cases placeTop_next h

theorem step_shape {e : Env} {st st' : St} {t t' : Nat} (h : step e st t = .ok (st', .next t')) :
    st'.trace.length ≤ st.trace.length + 3 ∧ st'.len ≤ st.len + 1
      ∧ st'.len + st'.pendingGenerations = st.len + st.pendingGenerations := by
  rcases step_next h with ⟨-, rfl⟩ | ⟨-, hp, d, h⟩ | ⟨-, b, r, hb, hr, h⟩ | ⟨-, hp, s, hs, h⟩
  · omega
  · obtain ⟨h1, h2, h3⟩ := generate_shape h
    omega
  · obtain ⟨h1, h2, h3⟩ := takeBound_shape (positionOf_some hb) hr
    rcases h with rfl | ⟨nx, h⟩
    · omega
    · obtain ⟨h4, h5, h6⟩ := placeTop_shape h
      omega
  · obtain ⟨h1, h2, h3⟩ := generate_shape hs
    rcases h with rfl | ⟨nx, h⟩
    · omega
    · obtain ⟨h4, h5, h6⟩ := placeTop_shape h
      omega

/-! ## The loop invariant -/

-- The invariant of `loop` at `targetOffset`. Each iteration lowers
-- `2 * pending + 2 * (n - targetOffset)` by at least the number of operations it adds.
structure Inv (e : Env) (st : St) (targetOffset : Nat) : Prop where
  len_pending : st.len + st.pendingGenerations = e.n
  n_le : e.n ≤ MAX_N
  t_le : targetOffset ≤ e.n
  dests : Dests e.n st.dests
  ops_le : st.trace.length + 2 * st.pendingGenerations + 2 * (e.n - targetOffset) ≤ 4 * e.n

theorem map_dest_zipWith (source : List Word) (dests : List Nat)
    (h : source.length = dests.length) : (List.zipWith Slot.mk source dests).map Slot.dest = dests := by
  induction source generalizing dests with
  | nil => cases dests <;> simp_all
  | cons x xs ih => cases dests <;> simp_all

theorem Inv_init {e : Env} {source : List Word} {dests : List Nat}
    (hl : source.length = dests.length) (hm : dests.length ≤ e.n) (hn : e.n ≤ MAX_N)
    (hd : Dests e.n dests) :
    Inv e ⟨List.zipWith Slot.mk source dests, e.n - source.length, []⟩ 0 := by
  have hds : St.dests ⟨List.zipWith Slot.mk source dests, e.n - source.length, []⟩ = dests :=
    map_dest_zipWith source dests hl
  refine ⟨?_, hn, Nat.zero_le _, by rw [hds]; exact hd, ?_⟩
  · simp only [St.len, List.length_zipWith]; omega
  · simp only [List.length_nil]; omega

theorem step_inv {e : Env} {st st' : St} {t t' : Nat} (hi : Inv e st t) (ht : t < e.n)
    (h : step e st t = .ok (st', .next t')) : Inv e st' t' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  rcases step_next h with ⟨rfl, rfl⟩ | ⟨rfl, hp, d, h⟩ | ⟨rfl, b, r, hb, hr, h⟩ | ⟨rfl, hp, s, hs, h⟩
  · exact ⟨h1, h2, by omega, h4, by omega⟩
  · obtain ⟨g1, g2, g3⟩ := generate_shape h
    exact ⟨by omega, h2, h3, generate_dests h h4, by omega⟩
  · have hb' := positionOf_some hb
    obtain ⟨g1, g2, g3⟩ := takeBound_shape hb' hr
    have gd := takeBound_dests hb' hr h4
    rcases h with rfl | ⟨nx, h⟩
    · exact ⟨by omega, h2, by omega, gd, by omega⟩
    · obtain ⟨k1, k2, k3⟩ := placeTop_shape h
      exact ⟨by omega, h2, by omega, placeTop_dests h gd, by omega⟩
  · obtain ⟨g1, g2, g3⟩ := generate_shape hs
    have gd := generate_dests hs h4
    rcases h with rfl | ⟨nx, h⟩
    · exact ⟨by omega, h2, by omega, gd, by omega⟩
    · obtain ⟨k1, k2, k3⟩ := placeTop_shape h
      exact ⟨by omega, h2, by omega, placeTop_dests h gd, by omega⟩

-- The precondition of `step`.
theorem Inv.lt {e : Env} {st : St} {t : Nat} (hi : Inv e st t) (ht : t < e.n) :
    st.len + st.pendingGenerations ≤ e.n ∧ st.trace.length + 3 ≤ 6 * e.n := by
  have := hi.len_pending
  have := hi.ops_le
  omega

/-! ## Finish -/

-- The precondition of `finish`.
theorem Inv.finish {e : Env} {st : St} {t : Nat} (hi : Inv e st t)
    (hp : st.pendingGenerations = 0) :
    IsPerm (st.slots.map Slot.dest) ∧ st.trace.length + 2 * st.len ≤ 6 * e.n := by
  have h1 := hi.len_pending
  have h2 := hi.ops_le
  have hl := st.length_dests
  obtain ⟨d1, d2⟩ := hi.dests
  refine ⟨⟨fun i h => ?_, d2⟩, by omega⟩
  have := d1 i h
  unfold St.dests at hl this
  omega

theorem depth_le (p : PermuteKraken.Perm) : p.depth ≤ 16 := by
  unfold PermuteKraken.Perm.depth
  split
  · rename_i h; exact (PermuteKraken.step_swap h).2.1
  · exact Nat.zero_le _

theorem mem_trace (p : PermuteKraken.Perm) (k : Nat) : ∀ x ∈ p.trace k, x ≤ 16 := by
  induction k generalizing p with
  | zero => simp [PermuteKraken.Perm.trace]
  | succ k ih =>
    intro x hx
    simp only [PermuteKraken.Perm.trace, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact depth_le p
    · exact ih p.advance x hx

theorem permute_ok {p : PermuteKraken.Perm} {ds : List Nat} (h : PermuteKraken.permute p = .ok ds) :
    ds.length ≤ 2 * p.toList.length ∧ ∀ x ∈ ds, x ≤ 16 := by
  rw [p.permute_eq] at h
  have hds : ds = p.trace (PermuteKraken.steps p) := by
    split at h <;> cases h <;> rfl
  subst hds
  refine ⟨?_, mem_trace p _⟩
  rw [p.length_trace]
  by_cases hl : p.toList.length = 0
  · rw [p.steps_zero hl]; omega
  · have := p.steps_lt (by omega); omega

/-! ## Unfolding of `loop` -/

theorem loop_next {e : Env} {st st' : St} {t t' : Nat} (ht : t < e.n)
    (h : step e st t = .ok (st', .next t')) : loop e st t = loop e st' t' := by
  rw [loop, ite_eq_left ht]
  split <;> simp_all

theorem loop_finish {e : Env} {st st' : St} {t : Nat} (ht : t < e.n)
    (h : step e st t = .ok (st', .finish)) :
    loop e st t = if st'.len = e.n then finish st' else .error .assertion := by
  rw [loop, ite_eq_left ht]
  split <;> simp_all

theorem loop_error {e : Env} {st : St} {t : Nat} {err : Err} (ht : t < e.n)
    (h : step e st t = .error err) : loop e st t = .error err := by
  rw [loop, ite_eq_left ht]
  split <;> simp_all

theorem loop_ge {e : Env} {st : St} {t : Nat} (ht : ¬t < e.n) :
    loop e st t = if st.len = e.n then .ok st.trace else .error .assertion := by
  rw [loop, ite_eq_right ht]

/-! ## Spilled congruence -/

section Congr

-- `s` and `s'` agree on the ids of the variables in the target.
variable {tg : List Word} {s s' : Nat → UInt8}
  (H : ∀ v ∈ tg, 2 ≤ v.toNat → v.toNat % 2 = 0 → s ((v.toNat - 2) / 2) = s' ((v.toNat - 2) / 2))
include H

theorem isSpilled_congr (d : Nat) : isSpilled ⟨tg, s⟩ tg[d]! = isSpilled ⟨tg, s'⟩ tg[d]! := by
  unfold isSpilled
  dsimp only
  by_cases hd : d < tg.length
  · rw [getElem!_pos tg d hd]
    by_cases hv : 2 ≤ tg[d].toNat ∧ tg[d].toNat % 2 = 0
    · rw [H _ (List.getElem_mem hd) hv.1 hv.2]
    · have : (decide (2 ≤ tg[d].toNat) && tg[d].toNat % 2 == 0) = false := by grind
      simp only [this, Bool.false_and]
  · rw [getElem!_neg tg d hd]
    rfl

theorem emit_congr (st : St) (d : Nat) : emit ⟨tg, s⟩ st d = emit ⟨tg, s'⟩ st d := by
  simp only [emit, isSpilled_congr H d]

theorem produce_congr (st : St) (d : Nat) : produce ⟨tg, s⟩ st d = produce ⟨tg, s'⟩ st d := by
  simp only [produce, emit_congr H st d]

theorem generate_congr (st : St) (d : Nat) : generate ⟨tg, s⟩ st d = generate ⟨tg, s'⟩ st d := by
  simp only [generate, Env.n, produce_congr H st d]

theorem urgentFrom_congr (st : St) (t d u : Nat) :
    urgentFrom ⟨tg, s⟩ st t d u = urgentFrom ⟨tg, s'⟩ st t d u := by
  conv => lhs; rw [urgentFrom]
  conv => rhs; rw [urgentFrom]
  simp only [Env.n, isSpilled_congr H d]
  by_cases hd : d < tg.length
  · have : tg.length - (d + 1) < tg.length - d := by omega
    simp only [hd, ↓reduceIte, urgentFrom_congr st t (d + 1)]
    rfl
  · simp only [hd, ↓reduceIte]
termination_by tg.length - d

theorem step_congr (st : St) (t : Nat) : step ⟨tg, s⟩ st t = step ⟨tg, s'⟩ st t := by
  simp only [step, urgent, Env.n, urgentFrom_congr H, generate_congr H]
  rfl

theorem loop_congr (st : St) (t : Nat) : loop ⟨tg, s⟩ st t = loop ⟨tg, s'⟩ st t := by
  by_cases ht : t < tg.length
  · have hs := step_congr H st t
    cases h : step ⟨tg, s⟩ st t with
    | error err => rw [loop_error ht h, loop_error ht (hs ▸ h :)]
    | ok r =>
      obtain ⟨st', nx⟩ := r
      cases nx with
      | finish => rw [loop_finish ht h, loop_finish ht (hs ▸ h :)]; rfl
      | next t' =>
        have := step_progress h
        rw [loop_next ht h, loop_next ht (hs ▸ h :)]
        exact loop_congr st' t'
  · rw [loop_ge ht, loop_ge ht]
    rfl
termination_by (tg.length - t, st.pendingGenerations)
decreasing_by
  rcases this with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

end Congr

-- `buildBottomUp` reads `spilled` only at the ids of the variables in the target.
theorem buildBottomUp_congr {e e' : Env} (ht : e.target = e'.target)
    (hs : ∀ v ∈ e.target, 2 ≤ v.toNat → v.toNat % 2 = 0 →
      e.spills ((v.toNat - 2) / 2) = e'.spills ((v.toNat - 2) / 2))
    (source : List Word) (dests : List Nat) :
    buildBottomUp e source dests = buildBottomUp e' source dests := by
  obtain ⟨tg, s⟩ := e
  obtain ⟨tg', s'⟩ := e'
  dsimp only at ht hs
  subst ht
  exact loop_congr hs _ _

end Bbu
