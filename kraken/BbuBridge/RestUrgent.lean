import BbuBridge.Statements

/-!
The branch of the loop for an urgent offset.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

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
    show StepCorr e _ state ((state.generate u).attach >>= fun a =>
      if a.1.blocked.isSome then pure a.1 else buildBottomUp.loop t a.1.state)
    have ha := attach_bind (state.generate u)
      (fun r => if r.blocked.isSome then pure r else buildBottomUp.loop t r.state)
    rw [ha]
    exact stepcorr_generate t (hgen e source st state u h hp0)

end BbuBridge
