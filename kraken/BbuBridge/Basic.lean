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

-- A value of the source or the target is spilled in the model if and only if it is spilled in the
-- original.
theorem isSpilled_iff (e : Bbu.Env) (source : Stack) (v : Bbu.StackSlot)
    (hv : decode v ∈ source ++ tgt e) :
    Bbu.isSpilled e v = true ↔ (spillSet e source).is_spilled (decode v) := by
  unfold decode
  split_ifs with h0 h1 h2
  · simp [SpillSet.is_spilled, Bbu.isSpilled, h0, Bbu.Junk, Bbu.Value]
  · rcases h1 with h1 | h1
    · simp [SpillSet.is_spilled, Bbu.isSpilled, Bbu.isLiteralValue, h1]
    · simp [SpillSet.is_spilled, Bbu.isSpilled, h1, Bbu.FunctionCallReturnLabel, Bbu.Value]
  · simp [SpillSet.is_spilled, Bbu.isSpilled, h2, Bbu.FunctionReturnLabel, Bbu.Value]
  · rw [show decode v = .Var ⟨number v⟩ by simp [decode, h0, h1, h2]] at hv
    simp only [SpillSet.is_spilled, spillSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, VarId.mk.injEq]
    constructor
    · intro h; exact ⟨number v, ⟨number_lt v, by rw [ofNumber_number]; exact h, hv⟩, rfl⟩
    · rintro ⟨i, ⟨-, hi, -⟩, rfl⟩; rwa [ofNumber_number] at hi

-- A canonical slot decodes to a function return label if and only if its kind
-- is a function return label.
theorem isFRL_iff {v : Bbu.StackSlot} (hv : Canon v) :
    (decode v).isFunctionReturnLabel ↔ v.kind = Bbu.FunctionReturnLabel := by
  unfold decode
  split_ifs with h0 h1 h2
  · simp only [Value.isFunctionReturnLabel, false_iff]
    rw [h0]; decide
  · simp only [Value.isFunctionReturnLabel, false_iff]
    intro hk
    rw [hv.2 hk] at h1
    revert h1; decide
  · simp [Value.isFunctionReturnLabel, h2]
  · simp [Value.isFunctionReturnLabel, h2]

theorem tgt_length (e : Bbu.Env) : (tgt e).length = e.n := by
  simp [tgt, Bbu.Env.n]

theorem tgt_get (e : Bbu.Env) (d : Nat) (hd : d < (tgt e).length) :
    (tgt e)[d] = decode e.target[d]! := by
  simp only [tgt, List.getElem_map]
  rw [getElem!_pos e.target d (by simpa using hd)]

/-! ## Results -/

-- `Corr` for a weaker relation.
theorem corr_mono {α β : Type} {R S : α → β → Prop} {x : Bbu.M α} {y : Except ShuffleErr β}
    (h : Corr R x y) (hs : ∀ a b, x = .ok a → R a b → S a b) : Corr S x y := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | b <;> simp_all [Corr]

-- `ResCorr` goes through a bind that returns a block at once.
theorem rescorr_bind {source target : Stack} {spills : SpillSet}
    {R : Bbu.St → State source target spills → Prop}
    {x : Bbu.M Bbu.St} {y : Except ShuffleErr (Result source target spills)}
    {f : Bbu.St → Bbu.M Bbu.St}
    {g : Result source target spills → Except ShuffleErr (Result source target spills)}
    (h : ResCorr R x y) (hf : ∀ a r, R a r.state → ResCorr R (f a) (g r)) :
    ResCorr R (x.bind f) (y >>= fun r => if r.blocked.isSome then pure r else g r) := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | ⟨_ | _, b⟩ <;>
    simp_all [ResCorr, Except.bind, bind, pure, Except.pure]

-- An action that does not block, then the end.
theorem rescorr_pure {source target : Stack} {spills : SpillSet}
    {R : Bbu.St → State source target spills → Prop}
    {x : Bbu.M Bbu.St} {y : Except ShuffleErr (State source target spills)}
    (h : Corr R x y) : ResCorr R x (y >>= fun s => pure ⟨none, s⟩) := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | b <;>
    simp_all [Corr, ResCorr, Except.bind, bind, pure, Except.pure]

-- `attach` does not change a bind.
theorem attach_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x.attach >>= fun a => f a.1) = x >>= f := by
  cases x <;> rfl

-- A generation that does not block continues with the loop at `t`.
theorem stepcorr_generate {e : Bbu.Env} {source : Stack} {state : OState e source}
    {x : Bbu.M Bbu.St} {y : Except ShuffleErr (OResult e source)} (t : Nat)
    (h : ResCorr (Rel e) x y) :
    StepCorr e (x.map (·, .next t)) state
      (y >>= fun r => if r.blocked.isSome then pure r else buildBottomUp.loop t r.state) := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | ⟨_ | _, b⟩ <;>
    simp_all [ResCorr, StepCorr, Except.map, Except.bind, bind, pure, Except.pure]
  exact ⟨_, h, rfl⟩

-- An action, then the loop at `t`.
theorem stepcorr_next {e : Bbu.Env} {source : Stack} {state : OState e source}
    {x : Bbu.M Bbu.St} {y : Except ShuffleErr (OState e source)} (t : Nat)
    (h : Corr (Rel e) x y) :
    StepCorr e (x.map (·, .next t)) state (y >>= buildBottomUp.loop t) := by
  rcases x with (⟨_, _, _⟩ | _) | a <;> rcases y with (_ | _) | b <;> simp only [Corr] at h
  · exact ⟨_, rfl⟩
  · exact ⟨b, h, rfl⟩

-- A generation, then a step that continues as `g`.
theorem stepcorr_bind {e : Bbu.Env} {source : Stack} {state : OState e source}
    {x : Bbu.M Bbu.St} {y : Except ShuffleErr (OResult e source)}
    {f : Bbu.St → Bbu.M (Bbu.St × Bbu.Next)} {g : OResult e source → Except ShuffleErr (OResult e source)}
    (h : ResCorr (Rel e) x y) (hf : ∀ a r, r.blocked = none → Rel e a r.state → StepCorr e (f a) state (g r)) :
    StepCorr e (x.bind f) state (y >>= fun r => if r.blocked.isSome then pure r else g r) := by
  rcases x with (⟨pos, ex, a⟩ | _) | a <;> rcases y with (_ | _) | ⟨_ | b, s⟩ <;>
    simp only [ResCorr, reduceCtorEq, false_and] at h
  · obtain ⟨hb, hr⟩ := h
    exact ⟨s, hr, by rw [hb]; rfl⟩
  · exact ⟨_, rfl⟩
  · exact hf a ⟨none, s⟩ rfl h.2

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
  unfold State.isFinal Mapping.destinationOf
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
    (state.mapping.positionOf d).map Fin.val = Bbu.positionOf st d := by
  have hl := h.len
  rw [h.pos.findIdx]
  unfold Mapping.positionOf
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
