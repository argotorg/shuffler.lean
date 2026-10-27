import Shuffler.Basic

-- Runtime checks shared by BuildBottomUp and BuildMapping.
-- The definitions check conditions at runtime with `requires`; separate theorems prove that the
-- checks never fail.

namespace Shuffler

-- returns a proof of `condition` if it holds, or throws with an assertion error otherwise.
def requires (condition : Prop) [Decidable condition] (reason : String) : Except ShuffleErr (PLift condition) :=
  if h : condition then pure ⟨h⟩ else throw (.assertion reason)

theorem except_ok_bind (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

theorem except_error_bind (err : ε) (next : α → Except ε β) :
    (Except.error err >>= next) = .error err := rfl

theorem requires_of_true (condition : Prop) [Decidable condition] (h : condition) (reason : String) :
    requires condition reason = .ok ⟨h⟩ := by
  simp [requires, h, pure, Except.pure]

end Shuffler
