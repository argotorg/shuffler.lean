import BbuBridge.Defs

/-!
Basic facts: the queries of the model on words equal the queries of the
original on the decoded values, and the queries of related states agree.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

/-! ## Values -/

theorem decode_eq_iff {a b : Bbu.Word} : decode a = decode b ↔ a = b :=
  decode_injective.eq_iff

theorem isJunk_iff (v : Bbu.Word) : (decode v).is_junk ↔ v = 0 := by
  have h0 : v = 0 ↔ v.toNat = 0 := by
    constructor
    · rintro rfl; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  rw [h0]
  unfold decode
  split_ifs <;> simp_all [Value.is_junk]

theorem isFree_iff (v : Bbu.Word) : Bbu.isFree v = true ↔ (decode v).can_be_freely_generated := by
  have h0 : (v == 0) = decide (v.toNat = 0) := by
    by_cases h : v.toNat = 0
    · simp [show v = 0 from BitVec.eq_of_toNat_eq h]
    · simp only [h, decide_false, beq_eq_false_iff_ne]
      rintro rfl; exact h rfl
  have h1 : (v != 1) = !decide (v.toNat = 1) := by
    by_cases h : v.toNat = 1
    · simp [show v = 1 from BitVec.eq_of_toNat_eq h]
    · simp only [h, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
      rintro rfl; exact h rfl
  unfold Bbu.isFree decode
  rw [h0, h1]
  split_ifs <;> simp_all [Value.can_be_freely_generated]

theorem isSpilled_iff (e : Bbu.Env) (v : Bbu.Word) :
    Bbu.isSpilled e v = true ↔ (spillSet e).is_spilled (decode v) := by
  have hv := v.isLt
  unfold Bbu.isSpilled decode
  split_ifs with h0 h1 h2
  · simp [h0, SpillSet.is_spilled]
  · simp [h1, SpillSet.is_spilled]
  · have h63 : (v.toNat - 2) / 2 < 2 ^ 63 := by omega
    have h2' : 2 ≤ v.toNat := by omega
    simp [SpillSet.is_spilled, spillSet, h2, h2']
    intro; omega
  · simp [SpillSet.is_spilled, h2]

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
theorem Rel.dests (h : Rel e st state) : Bbu.Dests e.n st.dests := by
  have hl := h.len
  have hds := st.length_dests
  have key : ∀ i (hi : i < st.dests.length), ∃ j : Fin (tgt e).length,
      state.mapping ⟨i, by omega⟩ = some j ∧ j.val = st.dests[i] := by
    intro i hi
    obtain ⟨j, hj, hjd⟩ := h.mapping ⟨i, by omega⟩
    refine ⟨j, hj, ?_⟩
    rw [hjd, Bbu.St.dest_eq, getElem!_pos st.dests i hi]
  constructor
  · intro i hi
    obtain ⟨j, -, hj⟩ := key i hi
    rw [← hj, ← tgt_length e]
    exact j.isLt
  · intro i hi k hk hik
    obtain ⟨j, hj, hjv⟩ := key i hi
    obtain ⟨j', hj', hjv'⟩ := key k hk
    have hjj : j = j' := Fin.ext (by rw [hjv, hjv', hik])
    subst hjj
    have := state.mapping.inj hj hj'
    simpa using this

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
  unfold State.positionOf Bbu.positionOf
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
  have hds := h.dests
  unfold Bbu.positionOf
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have := hds.1 k (by simp [Bbu.St.dests]; exact hk)
  simp only [Bbu.St.dests, List.getElem_map] at this
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

-- The shallowest copy of a value.
theorem Rel.shallowestCopyPosition (h : Rel e st state) (v : Bbu.Word) :
    (state.stack.shallowestCopyPosition (decode v)).map Fin.val
      = Bbu.shallowestCopyPosition st v := by
  unfold Stack.shallowestCopyPosition Bbu.shallowestCopyPosition
  rw [← h.len, ← List.map_coe_finRange_eq_range, ← List.map_reverse, List.find?_map]
  congr 1
  congr 1
  funext pos
  rw [Bool.eq_iff_iff]
  simp [h.get, decode_eq_iff]
end BbuBridge
