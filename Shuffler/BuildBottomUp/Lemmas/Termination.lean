import Shuffler.BuildBottomUp.Lemmas.Loop

namespace Shuffler.BuildBottomUp.Lemmas

theorem loop_terminates (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    Acc (Continues (loopParts source target spills).val) ((none, cursor), state) := by
  constructor
  rintro ⟨⟨result, cursor'⟩, next⟩ hstep
  have hs := (action_triple_iff _ _ _).mp (loop_body_triple (none, cursor) state rfl inv)
  change ((loopParts source target spills).val () (none, cursor)).run state =
    .ok (.yield (result, cursor'), next) at hstep
  have hp : BodyPost cursor state (.yield (result, cursor')) next := by
    simpa only [hstep, Spec] using hs
  change result = none ∧ Invariant cursor' next ∧
    Prod.Lex Nat.lt Nat.lt (terminationMeasure cursor' next)
      (terminationMeasure cursor state) at hp
  obtain ⟨rfl, hi, hlt⟩ := hp
  exact loop_terminates cursor' next hi
termination_by terminationMeasure cursor state
decreasing_by exact hlt

end Shuffler.BuildBottomUp.Lemmas
