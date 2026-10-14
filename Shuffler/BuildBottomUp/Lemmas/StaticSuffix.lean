import Shuffler.BuildBottomUp.Lemmas.StaticData

namespace Shuffler.BuildBottomUp.Success

def Terminal (initial : State source target spills) : Prop :=
  if generationEnd initial ≤ boundary initial then
    CyclesReady initial (generationEnd initial)
  else BoundarySafe initial

-- A suffix of the same finite conjunction used by StaticSuccess.
def Suffix (initial : State source target spills) (cursor : Nat) : Prop :=
  (∀ i, cursor ≤ i → i < cutoff initial →
    (augmentedStack initial)[i]? = initial.expectedStack[i]?) ∧
  (∀ i, cursor ≤ i → i ≤ cutoff initial → Ready initial i) ∧ Terminal initial

theorem suffix_step (initial : State source target spills) (cursor : Nat)
    (hc : cursor < cutoff initial) :
    Suffix initial cursor ↔
      ((augmentedStack initial)[cursor]? = initial.expectedStack[cursor]?) ∧
      Ready initial cursor ∧ Suffix initial (cursor + 1) := by
  constructor
  · rintro ⟨hv, hr, ht⟩
    refine ⟨hv cursor le_rfl hc, hr cursor le_rfl hc.le, ?_⟩
    exact ⟨fun i hi hq => hv i (by omega) hq,
      fun i hi hq => hr i (by omega) hq, ht⟩
  · rintro ⟨hv, hr, hvs, hrs, ht⟩
    refine ⟨?_, ?_, ht⟩
    · intro i hi hq
      by_cases he : i = cursor
      · simpa [he] using hv
      · exact hvs i (by omega) hq
    · intro i hi hq
      by_cases he : i = cursor
      · simpa [he] using hr
      · exact hrs i (by omega) hq

theorem suffix_cutoff (initial : State source target spills) :
    Suffix initial (cutoff initial) ↔ Ready initial (cutoff initial) ∧ Terminal initial := by
  constructor
  · rintro ⟨_, hr, ht⟩
    exact ⟨hr _ le_rfl le_rfl, ht⟩
  · rintro ⟨hr, ht⟩
    refine ⟨fun i hi hq => (by omega), ?_, ht⟩
    intro i hi hq
    have he : i = cutoff initial := by omega
    simpa [he] using hr

theorem staticSuccess_iff_suffix_of_large (initial : State source target spills)
    (hlarge : MAX_DUP_DEPTH + 1 < initial.stack.length) :
    StaticSuccess initial ↔ Suffix initial 0 := by
  simp [StaticSuccess, show ¬initial.stack.length ≤ MAX_DUP_DEPTH + 1 by omega,
    Suffix, Terminal]

end Shuffler.BuildBottomUp.Success
