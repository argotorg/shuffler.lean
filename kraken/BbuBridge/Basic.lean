import BbuBridge.Defs

/-!
Basic facts: the queries of the model on canonical slots equal the queries of
the original on the decoded values, and the queries of related states agree.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

/-! ## Values -/

theorem decode_eq_iff {a b : Bbu.StackSlot} (ha : Canon a) (hb : Canon b) :
    decode a = decode b ↔ a = b :=
  ⟨decode_inj ha hb, congrArg decode⟩

theorem isJunk_iff (v : Bbu.StackSlot) : (decode v).is_junk ↔ Bbu.isJunk v = true := by
  unfold decode Bbu.isJunk
  split_ifs <;> simp_all [Value.is_junk]

theorem isFree_iff (v : Bbu.StackSlot) :
    Bbu.canBeFreelyGenerated v = true ↔ (decode v).can_be_freely_generated := by
  unfold Bbu.canBeFreelyGenerated Bbu.isLiteralValue decode
  split_ifs <;> simp_all [Value.can_be_freely_generated]

theorem isSpilled_iff (e : Bbu.Env) (v : Bbu.StackSlot) :
    Bbu.isSpilled e v = true ↔ (spillSet e).is_spilled (decode v) := by
  unfold decode
  split_ifs with h0 h1
  · simp [SpillSet.is_spilled, Bbu.isSpilled, h0, Bbu.Junk, Bbu.Value]
  · rcases h1 with h1 | h1
    · simp [SpillSet.is_spilled, Bbu.isSpilled, Bbu.isLiteralValue, h1]
    · simp [SpillSet.is_spilled, Bbu.isSpilled, h1, Bbu.FunctionCallReturnLabel, Bbu.Value]
  · simp only [SpillSet.is_spilled, spillSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, VarId.mk.injEq]
    constructor
    · intro h; exact ⟨number v, ⟨number_lt v, by rw [ofNumber_number]; exact h⟩, rfl⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩; rwa [ofNumber_number] at hi

theorem tgt_length (e : Bbu.Env) : (tgt e).length = e.n := by
  simp [tgt, Bbu.Env.n]

theorem tgt_get (e : Bbu.Env) (d : Nat) (hd : d < (tgt e).length) :
    (tgt e)[d] = decode e.target[d]! := by
  simp only [tgt, List.getElem_map]
  rw [getElem!_pos e.target d (by simpa using hd)]

/-! ## Related states -/

variable {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}

theorem Rel.len (h : Rel e st state) : state.stack.length = st.len := by
  rw [h.stack]; simp [Bbu.St.len]

theorem Rel.slot_lt (h : Rel e st state) (i : Fin state.stack.length) : i.val < st.slots.length := by
  have := h.len; have := i.isLt; simp only [Bbu.St.len] at *; omega

theorem Rel.get (h : Rel e st state) (i : Fin state.stack.length) :
    state.stack[i] = decode (st.val i) := by
  have hi := h.slot_lt i
  have := List.getElem_of_eq h.stack i.isLt
  rw [Fin.getElem_fin, this]
  simp [Bbu.St.val, List.getElem?_eq_getElem hi]

-- Each slot is bound for its model destination.
theorem Rel.mapping (h : Rel e st state) (i : Fin state.stack.length) :
    ∃ j : Fin (tgt e).length, state.mapping i = some j ∧ j.val = st.dest i := by
  obtain ⟨j, hj, hjd⟩ := Option.map_eq_some_iff.mp (h.dest i)
  exact ⟨j, hj, hjd⟩

theorem Rel.isFinal (h : Rel e st state) (i : Fin state.stack.length) :
    state.isFinal i ↔ st.dest i = i := by
  unfold State.isFinal State.destinationOf
  rw [h.dest i]
  simp

-- The destinations of related states are distinct and below `n`.
theorem Rel.dests (h : Rel e st state) : Bbu.Dests e.n st.dests := h.pos.dests

theorem Rel.slot_dest (_h : Rel e st state) (k : Nat) (hk : k < st.slots.length) :
    st.slots[k].dest = st.dest k := by
  simp [Bbu.St.dest, List.getElem?_eq_getElem hk]

-- A slot is bound for `d` if and only if it is the position of `d`.
theorem Rel.dest_iff (h : Rel e st state) (d : Fin (tgt e).length) (k : Fin state.stack.length) :
    st.dest k = d.val ↔ state.mapping.symm d = some k := by
  obtain ⟨j, hj, hjd⟩ := h.mapping k
  rw [PEquiv.eq_some_iff, hj, ← hjd, Option.some_inj, Fin.val_inj]

-- The position of the slot bound for `d`.
theorem Rel.positionOf (h : Rel e st state) (d : Fin (tgt e).length) :
    (state.positionOf d).map Fin.val = Bbu.positionOf st d := by
  have hl := h.len
  rw [h.pos.findIdx]
  unfold State.positionOf
  cases hs : state.mapping.symm d with
  | some i =>
    symm
    rw [Option.map_some, List.findIdx?_eq_some_iff_getElem]
    have hi := h.slot_lt i
    refine ⟨hi, ?_, ?_⟩
    · simpa [h.slot_dest] using (h.dest_iff d i).mpr hs
    · intro k hk
      have hk' : k < state.stack.length := by have := i.isLt; omega
      rw [h.slot_dest k (by omega)]
      simp only [beq_iff_eq]
      rw [h.dest_iff d ⟨k, hk'⟩, hs]
      intro he; injection he with he
      have := congrArg Fin.val he; simp at this; omega
  | none =>
    symm
    rw [Option.map_none, List.findIdx?_eq_none_iff]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk' : k < state.stack.length := by simp only [Bbu.St.len] at hl; omega
    rw [h.slot_dest k hk]
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [h.dest_iff d ⟨k, hk'⟩, hs]
    simp

-- No slot is bound for an offset beyond the target.
theorem Rel.positionOf_ge (h : Rel e st state) {d : Nat} (hd : e.n ≤ d) :
    Bbu.positionOf st d = none := by
  cases hp : Bbu.positionOf st d with
  | none => rfl
  | some b => exact absurd (Bbu.positionOf_lt h.pos hp) (by omega)

-- Each slot of a state with canonical slots is canonical.
theorem canon_val {st : Bbu.St} (hc : ∀ s ∈ st.slots, Canon s.val) (i : Nat) :
    Canon (st.val i) := by
  unfold Bbu.St.val
  cases hs : st.slots[i]? with
  | none => exact canon_default
  | some s => exact hc s (List.mem_of_getElem? hs)

theorem Rel.canonVal (h : Rel e st state) (i : Nat) : Canon (st.val i) := canon_val h.canon i

theorem Rel.canonTarget (h : Rel e st state) (d : Nat) : Canon e.target[d]! := by
  by_cases hd : d < e.target.length
  · rw [getElem!_pos e.target d hd]; exact h.target _ (List.getElem_mem hd)
  · rw [getElem!_neg e.target d hd]; exact canon_default

-- A set keeps the slots canonical.
theorem canon_set {l : List Bbu.Slot} (hl : ∀ s ∈ l, Canon s.val) {i : Nat} {s : Bbu.Slot}
    (hs : Canon s.val) : ∀ x ∈ l.set i s, Canon x.val := fun x hx =>
  (List.mem_or_eq_of_mem_set hx).elim (hl x) fun h => h ▸ hs

-- The shallowest copy of a canonical value.
theorem Rel.shallowestCopyPosition (h : Rel e st state) {v : Bbu.StackSlot} (hv : Canon v) :
    (state.stack.shallowestCopyPosition (decode v)).map Fin.val
      = Bbu.shallowestCopyPosition st v := by
  unfold Stack.shallowestCopyPosition Bbu.shallowestCopyPosition
  rw [← h.len, ← List.map_coe_finRange_eq_range, ← List.map_reverse, List.find?_map]
  congr 1
  congr 1
  funext pos
  rw [Bool.eq_iff_iff]
  simp [h.get, decode_eq_iff (h.canonVal pos) hv]

end BbuBridge
