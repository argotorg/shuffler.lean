import BbuBridge.Statements

/-!
The branch of the loop for an urgent offset.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- `attach` does not change a bind.
theorem restUrgent_attach_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x.attach >>= fun a => f a.1) = x >>= f := by
  cases x <;> rfl

theorem restUrgent_corr (hgen : GenerateStmt) : RestUrgentStmt := by
  intro e source st state t u uo h hp0 ht hu ⟨hun, hut, hlen⟩
  cases uo with
  | none => exact absurd hu hun
  | some x =>
    obtain ⟨hx, rfl⟩ := hu
    have hc : (some u).isSome ∧ some u ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH := by
      refine ⟨rfl, by simpa using hut, ?_⟩
      rw [h.len]; unfold MAX_SWAP_DEPTH; unfold Bbu.MAX_SWAP_DEPTH at hlen; omega
    unfold origRest
    rw [dite_eq_left_of_eq_true (eq_true hc)]
    show StepCorr e _ state ((state.generate u).attach >>= fun a => buildBottomUp.loop t a.1)
    rw [restUrgent_attach_bind]
    have hg := hgen e source st state u h hp0
    generalize Bbu.generate e st u = m at hg ⊢
    generalize state.generate u = r at hg ⊢
    cases m <;> cases r <;> simp only [Corr] at hg
    · exact ⟨_, rfl, hg⟩
    · exact ⟨_, hg, rfl⟩

end BbuBridge
