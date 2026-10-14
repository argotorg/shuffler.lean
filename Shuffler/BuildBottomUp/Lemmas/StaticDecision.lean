import Shuffler.BuildBottomUp.Lemmas.StaticData

namespace Shuffler.BuildBottomUp.Success

instance (initial : State source target spills) (cursor : Nat) (value : Value) :
    Decidable (NeedsCopy initial cursor value) := by
  unfold NeedsCopy
  infer_instance

instance (initial : State source target spills) (cursor : Nat) :
    Decidable (Ready initial cursor) := by
  unfold Ready
  infer_instance

-- The two natural-number quantifiers range over finite sets of indices.
instance (initial : State source target spills) (cursor : Nat) :
    Decidable (CyclesReady initial cursor) :=
  decidable_of_iff
    (∀ i : Fin (target.length - (MAX_SWAP_DEPTH + 1)), cursor ≤ i.val →
      ∀ k : Fin target.length,
        (completedNext initial)^[k.val] i.val < cursor ∨
          (completedNext initial)^[k.val] i.val = i.val)
    (by
      constructor
      · intro hs i hi hid k hk
        exact hs ⟨i, hid⟩ hi ⟨k, hk⟩
      · intro hs i hi k
        exact hs i.val hi i.isLt k.val k.isLt)

-- Only the value returned by this option can satisfy the premise of BoundarySafe.
instance (initial : State source target spills) : Decidable (BoundarySafe initial) := by
  unfold BoundarySafe
  cases he : initial.expectedStack[boundary initial]? with
  | none => simp; infer_instance
  | some value =>
    simp only [Option.some.injEq]
    exact decidable_of_iff
      ((augmentedStack initial)[boundary initial]? = some value ∨
        ¬NeedsCopy initial (boundary initial) value ∨ 2 ≤ copies initial (boundary initial) value)
      ⟨fun hs v he => he ▸ hs, fun hs => hs value rfl⟩

end Shuffler.BuildBottomUp.Success

namespace Shuffler.BuildBottomUp

instance (initial : State source target spills) : Decidable (StaticSuccess initial) := by
  unfold StaticSuccess
  infer_instance

end Shuffler.BuildBottomUp
