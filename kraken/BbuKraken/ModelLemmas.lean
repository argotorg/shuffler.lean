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

theorem St.dest_eq (st : St) (i : Nat) : st.dest i = st.dests[i]! := by
  simp [St.dest, St.dests, getElem!_def]
  cases st.slots[i]? <;> rfl

theorem St.destinationOf_eq {st : St} {i : Nat} (h : i < st.len) :
    st.destinationOf i = some (st.dest i) := by
  simp [St.destinationOf, St.dest, List.getElem?_eq_getElem (show i < st.slots.length from h)]

-- Each slot has a destination: the check of `permuteDestinations` holds.
theorem St.all_destinationOf (st : St) :
    (List.range st.len).all (fun pos => (st.destinationOf pos).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  rw [St.destinationOf_eq hi]
  rfl

theorem swapDest_len (st : St) (a b : Nat) : (swapDestinations st a b).len = st.len := by
  simp [swapDestinations, St.len]

-- For two slots of the stack, both checks of `swapDestinations` hold.
theorem swapDest_positionOf {st : St} {a b : Nat} (ha : a < st.len) (hb : b < st.len) :
    (swapDestinations st a b).positionOf = (st.positionOf.set
      ((swapDestinations st a b).dest a) (some a)).set ((swapDestinations st a b).dest b) (some b) := by
  have hl := swapDest_len st a b
  show bindIf (bindIf st.positionOf ((swapDestinations st a b).destinationOf a) a)
    ((swapDestinations st a b).destinationOf b) b = _
  rw [St.destinationOf_eq (hl ▸ ha), St.destinationOf_eq (hl ▸ hb)]
  rfl

-- For two slots of the stack, `swapDestinations` without the checks.
theorem swapDest_eq {st : St} {a b : Nat} (ha : a < st.len) (hb : b < st.len) :
    swapDestinations st a b =
      let st := { st with
        slots := (st.slots.set a ⟨st.val a, st.dest b⟩).set b ⟨st.val b, st.dest a⟩ }
      { st with positionOf := (st.positionOf.set (st.dest a) (some a)).set (st.dest b) (some b) } := by
  have hp := swapDest_positionOf ha hb
  rw [show swapDestinations st a b = { swapDestinations st a b with
    positionOf := (swapDestinations st a b).positionOf } from rfl, hp]
  rfl

theorem swapDest_dests (st : St) (a b : Nat) :
    (swapDestinations st a b).dests = swapEntries st.dests a b := by
  simp [swapDestinations, St.dests, swapEntries, List.map_set, St.dest_eq]

theorem shallowestCopy_lt {st : St} {slot : StackSlot} {c : Nat}
    (h : shallowestCopyPosition st slot = some c) :
    c < st.len := by
  simpa using List.mem_reverse.mp (List.mem_of_find?_eq_some h)

/-! ## Positions -/

-- `m_positionOf` is the inverse of `m_destinationOf`.
structure Pos (n : Nat) (st : St) : Prop where
  length : st.positionOf.length = n
  iff : ∀ d i, positionOf st d = some i ↔ ∃ h : i < st.dests.length, st.dests[i] = d

theorem Pos.congr {n : Nat} {st st' : St} (hp : Pos n st) (h1 : st'.positionOf = st.positionOf)
    (h2 : st'.dests = st.dests) : Pos n st' := by
  refine ⟨h1 ▸ hp.length, fun d i => ?_⟩
  simp only [positionOf, h1, h2]
  exact hp.iff d i

theorem positionOf_none {n : Nat} {st : St} {d : Nat} (hp : Pos n st)
    (h : positionOf st d = none) : d ∉ st.dests := by
  intro hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have := (hp.iff _ i).2 ⟨hi, rfl⟩
  simp [h] at this

theorem positionOf_some {n : Nat} {st : St} {d b : Nat} (hp : Pos n st)
    (h : positionOf st d = some b) : b < st.len := by
  obtain ⟨hb, -⟩ := (hp.iff d b).1 h
  simpa [St.length_dests] using hb

theorem positionOf_dest {n : Nat} {st : St} {d b : Nat} (hp : Pos n st)
    (h : positionOf st d = some b) : st.dest b = d := by
  obtain ⟨hb, hd⟩ := (hp.iff d b).1 h
  rw [St.dest_eq, getElem!_pos st.dests b hb, hd]

theorem positionOf_lt {n : Nat} {st : St} {d b : Nat} (hp : Pos n st)
    (h : positionOf st d = some b) : d < n := by
  rw [← hp.length]
  refine Nat.lt_of_not_le fun hd => ?_
  simp [positionOf, List.getElem?_eq_none hd] at h

-- The model of the original: the first slot bound for `d`.
theorem Pos.findIdx {n : Nat} {st : St} (hp : Pos n st) (d : Nat) :
    positionOf st d = st.slots.findIdx? (·.dest == d) := by
  have hf : st.slots.findIdx? (·.dest == d) = st.dests.findIdx? (· == d) := by
    simp [St.dests, List.findIdx?_map, Function.comp_def]
  rw [hf]
  cases h : positionOf st d with
  | none =>
    have := positionOf_none hp h
    symm
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact this hx
  | some i =>
    obtain ⟨hi, hd⟩ := (hp.iff d i).1 h
    symm
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hi, by simp [hd], fun j hj => ?_⟩
    have hj' : j < st.dests.length := by omega
    simp only [ne_eq]
    intro hjd
    have := (hp.iff d j).2 ⟨hj', by simpa using hjd⟩
    rw [h] at this
    cases this
    omega

theorem Pos.addState {n : Nat} {st : St} {v : StackSlot} {d : Nat} {op : Op} (hp : Pos n st)
    (hd : d < n) (hn : positionOf st d = none) :
    Pos n { st with
      slots := st.slots ++ [⟨v, d⟩]
      positionOf := st.positionOf.set d (some st.len)
      trace := st.trace ++ [op] } := by
  have hm := positionOf_none hp hn
  have hl := hp.length
  refine ⟨by simp [hl], fun d' i => ?_⟩
  have hi := hp.iff d' i
  simp only [positionOf, St.dests, St.len, List.getElem?_set] at hi hm ⊢
  simp only [List.map_append, List.length_append, List.length_map, List.length_singleton,
    List.map_cons, List.map_nil]
  by_cases e : d = d'
  · subst e
    simp only [↓reduceIte, hl, hd]
    constructor
    · rintro ⟨⟩; exact ⟨by omega, by simp⟩
    · rintro ⟨h1, h2⟩
      rw [List.getElem_append] at h2
      split at h2
      · exact absurd (h2 ▸ List.getElem_mem _) hm
      · rename_i hlt; simp only [List.length_map] at hlt; simp only [Option.join_some, Option.some.injEq]; omega
  · simp only [e, ↓reduceIte, hi]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simp at h1 ⊢; omega, by rw [List.getElem_append_left]; exact h2⟩
    · rintro ⟨h1, h2⟩
      rw [List.getElem_append] at h2
      split at h2
      · rename_i hlt; exact ⟨hlt, h2⟩
      · simp at h2; exact absurd h2 e

theorem Pos.unique {n : Nat} {st : St} (hp : Pos n st) {i j : Nat} (hi : i < st.dests.length)
    (hj : j < st.dests.length) (h : st.dests[i] = st.dests[j]) : i = j := by
  have h1 := (hp.iff st.dests[j] i).2 ⟨hi, h⟩
  have h2 := (hp.iff st.dests[j] j).2 ⟨hj, rfl⟩
  rw [h1] at h2
  cases h2
  rfl

theorem Pos.swapDest {n : Nat} {st : St} {a b : Nat} (hp : Pos n st) (ha : a < st.len)
    (hb : b < st.len) : Pos n (swapDestinations st a b) := by
  rw [← St.length_dests] at ha hb
  have hl := hp.length
  have hu := @Pos.unique n st hp
  have hpa := hp.iff st.dests[a] a
  have hpb := hp.iff st.dests[b] b
  have hda := positionOf_lt hp (hpa.2 ⟨ha, rfl⟩)
  have hdb := positionOf_lt hp (hpb.2 ⟨hb, rfl⟩)
  have hd : ∀ i (h : i < st.dests.length), (swapDestinations st a b).dests[i]'(by
      rw [swapDest_dests]; simpa [swapEntries] using h) =
      if i = b then st.dests[a] else if i = a then st.dests[b] else st.dests[i] := by
    intro i h
    simp only [swapDest_dests, swapEntries, List.getElem_set, getElem!_pos st.dests a ha,
      getElem!_pos st.dests b hb]
    grind
  have hq : ∀ d, positionOf (swapDestinations st a b) d =
      if d = st.dests[a] then some b else if d = st.dests[b] then some a else positionOf st d := by
    have hA : (swapDestinations st a b).dest a = st.dests[b] := by
      rw [St.dest_eq, getElem!_pos _ a (by rw [swapDest_dests]; simpa [swapEntries] using ha), hd a ha]
      grind
    have hB : (swapDestinations st a b).dest b = st.dests[a] := by
      rw [St.dest_eq, getElem!_pos _ b (by rw [swapDest_dests]; simpa [swapEntries] using hb), hd b hb]
      simp
    have hP : (swapDestinations st a b).positionOf = (st.positionOf.set
        ((swapDestinations st a b).dest a) (some a)).set ((swapDestinations st a b).dest b) (some b) :=
      swapDest_positionOf (by simpa [St.length_dests] using ha) (by simpa [St.length_dests] using hb)
    intro d
    rw [positionOf, hP, hA, hB, positionOf]
    simp only [List.getElem?_set, List.length_set, hl, hda, hdb, ↓reduceIte]
    by_cases h1 : st.dests[a] = d <;> by_cases h2 : st.dests[b] = d <;> simp_all [eq_comm]
  have hl' : (swapDestinations st a b).dests.length = st.dests.length := by
    simp [swapDest_dests, swapEntries]
  refine ⟨by rw [swapDest_positionOf (by simpa [St.length_dests] using ha)
    (by simpa [St.length_dests] using hb)]; simp [hl], fun d i => ?_⟩
  rw [hq]
  have hi := hp.iff d i
  constructor
  · intro h
    by_cases e1 : d = st.dests[a]
    · rw [ite_eq_left e1, Option.some.injEq] at h
      subst h
      exact ⟨hl' ▸ hb, by rw [hd b hb, ite_eq_left rfl, e1]⟩
    by_cases e2 : d = st.dests[b]
    · rw [ite_eq_right e1, ite_eq_left e2, Option.some.injEq] at h
      subst h
      have hab : a ≠ b := fun h => e1 (by subst h; exact e2)
      exact ⟨hl' ▸ ha, by rw [hd a ha, ite_eq_right hab, ite_eq_left rfl, e2]⟩
    rw [ite_eq_right e1, ite_eq_right e2] at h
    obtain ⟨hi', hdi⟩ := hi.1 h
    have hib : i ≠ b := fun h => e2 (by subst h; exact hdi.symm)
    have hia : i ≠ a := fun h => e1 (by subst h; exact hdi.symm)
    exact ⟨hl' ▸ hi', by rw [hd i hi']; simp [hib, hia, hdi]⟩
  · rintro ⟨hi', hdi⟩
    rw [hd i (hl' ▸ hi')] at hdi
    by_cases hib : i = b
    · subst hib; simp [← hdi]
    by_cases hia : i = a
    · subst hia
      simp only [hib, ↓reduceIte] at hdi
      have : d ≠ st.dests[i] := fun h => hib (hu ha hb (h ▸ hdi).symm)
      rw [ite_eq_right this, ite_eq_left hdi.symm]
    simp only [hib, hia, ↓reduceIte] at hdi
    have e1 : d ≠ st.dests[a] := fun h => hia (hu (hl' ▸ hi') ha (hdi.trans h))
    have e2 : d ≠ st.dests[b] := fun h => hib (hu (hl' ▸ hi') hb (hdi.trans h))
    simp only [e1, e2, ↓reduceIte]
    exact hi.2 ⟨hl' ▸ hi', hdi⟩

theorem Pos.dests {n : Nat} {st : St} (hp : Pos n st) : Dests n st.dests :=
  ⟨fun i h => positionOf_lt hp ((hp.iff _ i).2 ⟨h, rfl⟩), fun _ hi _ hj h => hp.unique hi hj h⟩

/-! ## Shape of the actions -/

-- `add` with the check first: the check does not read the new slot.
theorem add_eq (st : St) (slot : StackSlot) (d : Nat) (op : Op) :
    add st slot d op = if (positionOf st d).isSome then .error .assertion else .ok { st with
        slots := st.slots ++ [⟨slot, d⟩]
        positionOf := st.positionOf.set d (some st.len)
        trace := st.trace ++ [op] } := by
  unfold add positionOf
  split <;> simp_all [St.len]

theorem add_ok {st st' : St} {slot : StackSlot} {d : Nat} {op : Op}
    (h : add st slot d op = .ok st') :
    positionOf st d = none
      ∧ st' = { st with
        slots := st.slots ++ [⟨slot, d⟩]
        positionOf := st.positionOf.set d (some st.len)
        trace := st.trace ++ [op] } := by
  unfold add at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rename_i hp
    exact ⟨Option.not_isSome_iff_eq_none.mp hp, by simp [St.len]⟩

theorem add_shape {st st' : St} {slot : StackSlot} {d : Nat} {op : Op}
    (h : add st slot d op = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace = st.trace ++ [op]
      ∧ st'.pendingGenerations = st.pendingGenerations
      ∧ st'.slots = st.slots ++ [⟨slot, d⟩] := by
  obtain ⟨-, rfl⟩ := add_ok h
  simp [St.len]

theorem Pos.add {n : Nat} {st st' : St} {slot : StackSlot} {d : Nat} {op : Op} (hp : Pos n st)
    (hd : d < n) (h : add st slot d op = .ok st') : Pos n st' := by
  obtain ⟨hn, rfl⟩ := add_ok h
  exact hp.addState hd hn

-- The value exchange of `swapWith` keeps the destinations.
theorem set_getElem!_self (l : List Nat) (a : Nat) : l.set a l[a]! = l := by
  by_cases h : a < l.length
  · rw [getElem!_pos l a h, List.set_getElem_self]
  · exact List.set_eq_of_length_le (by omega)

theorem swapVals_dests (st : St) (a b : Nat) :
    ((st.slots.set a ⟨st.val b, st.dest a⟩).set b ⟨st.val a, st.dest b⟩).map Slot.dest
      = st.dests := by
  rw [List.map_set, List.map_set]
  change (st.dests.set a (st.dest a)).set b (st.dest b) = st.dests
  rw [St.dest_eq, St.dest_eq, set_getElem!_self, set_getElem!_self]

theorem swapWith_ok {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    pos < st.len ∧ 1 ≤ st.len - 1 - pos ∧ st.len - 1 - pos ≤ MAX_SWAP_DEPTH ∧
      st' = swapDestinations { st with
        slots := (st.slots.set pos ⟨st.val (st.len - 1), st.dest pos⟩).set (st.len - 1)
          ⟨st.val pos, st.dest (st.len - 1)⟩
        trace := st.trace ++ [.swap (st.len - 1 - pos)] } pos (st.len - 1) := by
  unfold swapWith at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; rename_i h1 h2; exact ⟨by omega, by omega, by omega, rfl⟩

theorem swapDest_shape (st : St) (a b : Nat) :
    (swapDestinations st a b).len = st.len ∧ (swapDestinations st a b).trace = st.trace
      ∧ (swapDestinations st a b).pendingGenerations = st.pendingGenerations := by
  simp [swapDestinations, St.len]

theorem swapWith_shape {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    st'.len = st.len ∧ st'.trace.length = st.trace.length + 1
      ∧ st'.pendingGenerations = st.pendingGenerations := by
  obtain ⟨-, -, -, rfl⟩ := swapWith_ok h
  simp [swapDestinations, St.len]

theorem Pos.swapWith {n : Nat} {st st' : St} {pos : Nat} (hp : Pos n st)
    (h : swapWith st pos = .ok st') : Pos n st' := by
  obtain ⟨h1, -, -, rfl⟩ := swapWith_ok h
  refine Pos.swapDest (hp.congr rfl (swapVals_dests st pos (st.len - 1))) ?_ ?_
  · simp [St.len] at h1 ⊢; omega
  · simp [St.len] at h1 ⊢; omega

theorem emit_add {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    ∃ slot op, add st slot d op = .ok st' := by
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

-- `sizeDec` does not wrap above 0.
theorem sizeDec_pos {x : Nat} (h : 0 < x) : sizeDec x = x - 1 := by
  simp [sizeDec, Nat.pos_iff_ne_zero.mp h]

theorem produce_ok {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    ∃ s, emit e st d = .ok s ∧ st' = { s with pendingGenerations := sizeDec s.pendingGenerations } := by
  obtain ⟨s, hs, h⟩ := bind_ok h
  split at h
  · cases h
  · cases h; exact ⟨s, hs, rfl⟩

theorem produce_shape {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    st'.len = st.len + 1 ∧ st'.trace.length = st.trace.length + 1
      ∧ st'.pendingGenerations = sizeDec st.pendingGenerations := by
  obtain ⟨s, hs, rfl⟩ := produce_ok h
  obtain ⟨h1, h2, h3⟩ := emit_shape hs
  simp [St.len] at h1 ⊢
  simp [h1, h2, h3]

theorem Pos.produce {n : Nat} {e : Env} {st st' : St} {d : Nat} (hp : Pos n st) (hd : d < n)
    (h : produce e st d = .ok st') : Pos n st' := by
  obtain ⟨s, hs, rfl⟩ := produce_ok h
  obtain ⟨v, op, hs⟩ := emit_add hs
  exact (hp.add hd hs).congr rfl rfl

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
      ∧ st'.pendingGenerations = sizeDec st.pendingGenerations := by
  obtain ⟨-, s, hs, h⟩ := generate_ok h
  obtain ⟨h1, h2, h3⟩ := produce_shape hs
  rcases h with rfl | ⟨-, rfl⟩ | h
  · omega
  · obtain ⟨h4, h5, h6⟩ := swapDest_shape s d (s.len - 1)
    rw [h5]
    omega
  · obtain ⟨h4, h5, h6⟩ := swapWith_shape h
    omega

theorem Pos.generate {e : Env} {st st' : St} {d : Nat} (hp : Pos e.n st)
    (h : generate e st d = .ok st') : Pos e.n st' := by
  obtain ⟨hn, s, hs, h⟩ := generate_ok h
  have hs' := hp.produce hn hs
  rcases h with rfl | ⟨hlt, rfl⟩ | h
  · exact hs'
  · exact hs'.swapDest (by omega) (by omega)
  · exact hs'.swapWith h

theorem movableCopy_lt {st : St} {b c : Nat} (h : movableCopy st b = some c) : c < st.len := by
  have := List.mem_of_find?_eq_some h
  simpa using List.mem_of_mem_take this

theorem takeBound_ok {st : St} {t b : Nat} {r : St × Bool} (hb : b < st.len)
    (hpb : positionOf st t = some b) (h : takeBound st t = .ok r) :
    ∃ pos, pos < st.len ∧ (r.1 = swapDestinations st pos b
      ∨ swapWith (swapDestinations st pos b) pos = .ok r.1) := by
  unfold takeBound at h
  rw [hpb] at h
  dsimp only at h
  split at h
  · cases h
  rename_i hbt
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
    (hpb : positionOf st t = some b) (h : takeBound st t = .ok r) :
    r.1.len = st.len ∧ r.1.trace.length ≤ st.trace.length + 1
      ∧ r.1.pendingGenerations = st.pendingGenerations := by
  obtain ⟨pos, -, h | h⟩ := takeBound_ok hb hpb h
  · rw [h]
    obtain ⟨h1, h2, h3⟩ := swapDest_shape st pos b
    rw [h2]; omega
  · obtain ⟨h1, h2, h3⟩ := swapDest_shape st pos b
    obtain ⟨h4, h5, h6⟩ := swapWith_shape h
    rw [h2] at h5; omega

theorem Pos.takeBound {n : Nat} {st : St} {t b : Nat} {r : St × Bool} (hp : Pos n st)
    (hb : b < st.len) (hpb : positionOf st t = some b) (h : takeBound st t = .ok r) : Pos n r.1 := by
  obtain ⟨pos, hpos, h | h⟩ := takeBound_ok hb hpb h
  · rw [h]; exact hp.swapDest hpos hb
  · exact (hp.swapDest hpos hb).swapWith h

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

theorem Pos.placeTop {n : Nat} {st st' : St} {t : Nat} {nx : Next} (hp : Pos n st)
    (h : placeTop st t = .ok (st', nx)) : Pos n st' := by
  obtain ⟨-, -, rfl | h⟩ := placeTop_ok h
  · exact hp
  · exact hp.swapWith h

-- The four ways of an iteration that continues.
theorem step_next {e : Env} {st st' : St} {t t' : Nat} (h : step e st t = .ok (st', .next t')) :
    (t' = t + 1 ∧ st' = st)
    ∨ (t' = t ∧ 0 < st.pendingGenerations ∧ ∃ d, generate e st d = .ok st')
    ∨ (t' = t + 1 ∧ ∃ b r, positionOf st t = some b ∧ takeBound st t = .ok r ∧
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
  · rename_i hs
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
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


theorem step_shape {n : Nat} {e : Env} {st st' : St} {t t' : Nat} (hp : Pos n st)
    (h : step e st t = .ok (st', .next t')) :
    st'.trace.length ≤ st.trace.length + 3 ∧ st'.len ≤ st.len + 1
      ∧ st'.len + st'.pendingGenerations = st.len + st.pendingGenerations := by
  rcases step_next h with ⟨-, rfl⟩ | ⟨-, hp', d, h⟩ | ⟨-, b, r, hb, hr, h⟩ | ⟨-, hp', s, hs, h⟩
  · omega
  · obtain ⟨h1, h2, h3⟩ := generate_shape h
    rw [sizeDec_pos hp'] at h3
    omega
  · obtain ⟨h1, h2, h3⟩ := takeBound_shape (positionOf_some hp hb) hb hr
    rcases h with rfl | ⟨nx, h⟩
    · omega
    · obtain ⟨h4, h5, h6⟩ := placeTop_shape h
      omega
  · obtain ⟨h1, h2, h3⟩ := generate_shape hs
    rw [sizeDec_pos hp'] at h3
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
  pos : Pos e.n st
  ops_le : st.trace.length + 2 * st.pendingGenerations + 2 * (e.n - targetOffset) ≤ 4 * e.n

theorem Inv.dests {e : Env} {st : St} {t : Nat} (hi : Inv e st t) : Dests e.n st.dests :=
  hi.pos.dests

theorem map_dest_zipWith (source : List StackSlot) (dests : List Nat)
    (h : source.length = dests.length) : (List.zipWith Slot.mk source dests).map Slot.dest = dests := by
  induction source generalizing dests with
  | nil => cases dests <;> simp_all
  | cons x xs ih => cases dests <;> simp_all

-- `initPositionOf` after the first `k` binds.
theorem initPositionOf_prefix {n : Nat} {dests : List Nat} (hd : Dests n dests) :
    ∀ k (hk : k ≤ dests.length),
      ((List.range k).foldl (fun p i => p.set dests[i]! (some i)) (List.replicate n none)).length = n
      ∧ ∀ d i, (((List.range k).foldl (fun p i => p.set dests[i]! (some i))
          (List.replicate n none))[d]?).join = some i ↔ ∃ h : i < k, dests[i]'(by omega) = d := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, fun d i => ?_⟩
    simp only [List.range_zero, List.foldl_nil, List.getElem?_replicate]
    constructor
    · intro h; split at h <;> simp at h
    · rintro ⟨h, -⟩; omega
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk' : k < dests.length := by omega
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [getElem!_pos dests k hk']
    refine ⟨by rw [List.length_set, ih1], fun d i => ?_⟩
    rw [List.getElem?_set]
    by_cases e : dests[k] = d
    · rw [ite_eq_left e, ih1, ite_eq_left (e ▸ hd.1 k hk'), Option.join_some, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨by omega, e⟩
      · rintro ⟨hi, hid⟩
        exact (hd.2 i (by omega) k hk' (hid.trans e.symm)).symm
    · rw [ite_eq_right e, ih2]
      constructor
      · rintro ⟨hi, hid⟩; exact ⟨by omega, hid⟩
      · rintro ⟨hi, hid⟩
        refine ⟨Nat.lt_of_le_of_ne (by omega) fun h => e ?_, hid⟩
        subst h; exact hid

theorem Pos_init {e : Env} {source : List StackSlot} {dests : List Nat}
    (hl : source.length = dests.length) (hd : Dests e.n dests) : Pos e.n (init e source dests) := by
  have hds : (init e source dests).dests = dests := map_dest_zipWith source dests hl
  obtain ⟨h1, h2⟩ := initPositionOf_prefix hd dests.length (Nat.le_refl _)
  refine ⟨h1, fun d i => ?_⟩
  simp only [positionOf, hds]
  exact h2 d i

theorem Pos.isNone_iff {n : Nat} {st : St} (hp : Pos n st) (d : Nat) :
    (positionOf st d).isNone = decide (d ∉ st.dests) := by
  cases h : positionOf st d with
  | none => simp [positionOf_none hp h]
  | some i =>
    obtain ⟨hi, hd⟩ := (hp.iff d i).1 h
    simp only [Option.isNone_some, Bool.false_eq, decide_eq_false_iff_not, Decidable.not_not]
    exact hd ▸ List.getElem_mem hi

-- `n - length` offsets below `n` are not in a list of distinct offsets below `n`.
theorem countP_not_mem {n : Nat} {l : List Nat} (hd : Dests n l) :
    (List.range n).countP (fun d => decide (d ∉ l)) = n - l.length := by
  have hnd : l.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    exact absurd (hd.2 i hi j hj heq) (by omega)
  have hp : ((List.range n).filter (fun d => decide (d ∈ l))).Perm l := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd]
    intro a
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
    intro ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact hd.1 i hi
  have := List.length_eq_countP_add_countP (fun d => decide (d ∈ l)) (l := List.range n)
  rw [List.countP_eq_length_filter (l := List.range n), hp.length_eq, List.length_range] at this
  simp only [decide_eq_true_eq] at this
  omega

-- The count of the constructor is `n - m`.
theorem init_pending {e : Env} {source : List StackSlot} {dests : List Nat}
    (hl : source.length = dests.length) (hd : Dests e.n dests) :
    (init e source dests).pendingGenerations = e.n - dests.length := by
  have hp : Pos e.n (init e source dests) := Pos_init hl hd
  have hds : (init e source dests).dests = dests := map_dest_zipWith source dests hl
  show (List.range e.n).countP (fun d => (positionOf (init e source dests) d).isNone) = _
  simp only [hp.isNone_iff, hds]
  exact countP_not_mem hd

theorem Inv_init {e : Env} {source : List StackSlot} {dests : List Nat}
    (hl : source.length = dests.length) (hm : dests.length ≤ e.n) (hn : e.n ≤ MAX_N)
    (hd : Dests e.n dests) : Inv e (init e source dests) 0 := by
  have hp := init_pending hl hd
  refine ⟨?_, hn, Nat.zero_le _, Pos_init hl hd, ?_⟩
  · rw [hp]; simp only [init, St.len, List.length_zipWith]; omega
  · rw [hp]; simp only [init, List.length_nil]; omega

theorem step_inv {e : Env} {st st' : St} {t t' : Nat} (hi : Inv e st t) (ht : t < e.n)
    (h : step e st t = .ok (st', .next t')) : Inv e st' t' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  rcases step_next h with ⟨rfl, rfl⟩ | ⟨rfl, hp, d, h⟩ | ⟨rfl, b, r, hb, hr, h⟩ | ⟨rfl, hp, s, hs, h⟩
  · exact ⟨h1, h2, by omega, h4, by omega⟩
  · obtain ⟨g1, g2, g3⟩ := generate_shape h
    rw [sizeDec_pos hp] at g3
    exact ⟨by omega, h2, h3, h4.generate h, by omega⟩
  · have hb' := positionOf_some h4 hb
    obtain ⟨g1, g2, g3⟩ := takeBound_shape hb' hb hr
    have gp := h4.takeBound hb' hb hr
    rcases h with rfl | ⟨nx, h⟩
    · exact ⟨by omega, h2, by omega, gp, by omega⟩
    · obtain ⟨k1, k2, k3⟩ := placeTop_shape h
      exact ⟨by omega, h2, by omega, gp.placeTop h, by omega⟩
  · obtain ⟨g1, g2, g3⟩ := generate_shape hs
    rw [sizeDec_pos hp] at g3
    have gp := h4.generate hs
    rcases h with rfl | ⟨nx, h⟩
    · exact ⟨by omega, h2, by omega, gp, by omega⟩
    · obtain ⟨k1, k2, k3⟩ := placeTop_shape h
      exact ⟨by omega, h2, by omega, gp.placeTop h, by omega⟩

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

theorem finish_ok {st st' : St} (h : finish st = .ok st') :
    ∃ (hp : IsPerm (st.slots.map Slot.dest)) (swaps : List Nat),
      PermuteKraken.permute ⟨_, hp.1, fun i j hi hj => hp.2 i hi j hj⟩ = .ok swaps
        ∧ st' = swaps.foldl swapTop st := by
  unfold finish at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · rename_i hp
    split at h
    · rename_i swaps hs
      cases h
      exact ⟨hp, swaps, hs, rfl⟩
    · cases h
  · cases h

-- The swaps of `finish` keep the length, the mapping and `pendingGenerations`, and
-- add a swap each to the trace.
theorem foldl_swapTop (swaps : List Nat) (st : St) :
    (swaps.foldl swapTop st).len = st.len
      ∧ (swaps.foldl swapTop st).positionOf = st.positionOf
      ∧ (swaps.foldl swapTop st).pendingGenerations = st.pendingGenerations
      ∧ (swaps.foldl swapTop st).trace = st.trace ++ swaps.map Op.swap := by
  induction swaps generalizing st with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (swapTop st x)
    simp only [List.foldl_cons, h1, h2, h3, h4]
    simp [swapTop, St.len]

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
    loop e st t = if st.len = e.n then .ok st else .error .assertion := by
  rw [loop, ite_eq_right ht]

/-! ## Spilled congruence -/

section Congr

-- `s` and `s'` agree on the ids of the variables in the target.
variable {tg : List StackSlot} {s s' : Nat → UInt8}
  (H : ∀ v ∈ tg, v.kind = Value → v.valueOpcode ≠ Const →
    s v.payload.toNat = s' v.payload.toNat)
include H

theorem isSpilled_congr (d : Nat) : isSpilled ⟨tg, s⟩ tg[d]! = isSpilled ⟨tg, s'⟩ tg[d]! := by
  unfold isSpilled
  dsimp only
  by_cases hd : d < tg.length
  · rw [getElem!_pos tg d hd]
    by_cases hv : tg[d].kind = Value ∧ tg[d].valueOpcode ≠ Const
    · rw [H _ (List.getElem_mem hd) hv.1 hv.2]
    · have : (tg[d].kind == Value && !isLiteralValue tg[d]) = false := by
        simp only [isLiteralValue, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq]
        grind
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

-- `buildBottomUp` reads `spills` only at the ids of the variables in the target.
theorem buildBottomUp_congr {e e' : Env} (ht : e.target = e'.target)
    (hs : ∀ v ∈ e.target, v.kind = Value → v.valueOpcode ≠ Const →
      e.spills v.payload.toNat = e'.spills v.payload.toNat)
    (source : List StackSlot) (dests : List Nat) :
    buildBottomUp e source dests = buildBottomUp e' source dests := by
  obtain ⟨tg, s⟩ := e
  obtain ⟨tg', s'⟩ := e'
  dsimp only at ht hs
  subst ht
  exact loop_congr hs _ _

end Bbu
