import BbuBridge.Statements

/-!
`Bbu.movableCopy` is the search of the loop for a movable copy.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- A loop that stops at the first element that satisfies `p` is `find?`.
private theorem copyScan_forIn {ε : Type} (p : Nat → Bool) (f : Nat → Nat → Except ε (ForInStep Nat)) :
    ∀ (l : List Nat) (pos : Nat), (∀ c ∈ l, ∀ pos, f c pos = .ok (if p c then .done c else .yield pos)) →
      forIn l pos f = .ok ((l.find? p).getD pos)
  | [], pos, _ => rfl
  | c :: l, pos, hf => by
    rw [List.forIn_cons, hf c List.mem_cons_self, List.find?_cons]
    cases p c
    · exact copyScan_forIn p f l pos fun c hc => hf c (List.mem_cons_of_mem _ hc)
    · rfl

theorem copyScan_corr : CopyScanStmt := by
  intro e source st state b h
  have hl := h.len
  unfold origCopyScan Bbu.movableCopy
  have hd : (state.depthOf b).val = st.len - 1 - b.val := by
    simp [State.depthOf, Stack.offsetToDepth, hl]
  rw [hd, ← hl]
  refine (bind_pure _).trans (copyScan_forIn _ _ _ _ ?_)
  intro c hc pos
  have hc' : c < state.stack.length := by
    have := List.mem_of_mem_take hc
    simpa using this
  rw [show c = (⟨c, hc'⟩ : Fin _).val from rfl, slotAt_index, slotAt_index, index_eq]
  simp only [except_ok_bind, h.get, decode_eq_iff (h.canonVal c) (h.canonVal b), h.isFinal, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq]
  split_ifs <;> rfl

end BbuBridge
