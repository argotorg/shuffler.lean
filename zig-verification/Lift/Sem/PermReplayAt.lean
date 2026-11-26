module
public import Lift.Sem.PermReplay
@[expose] public section
namespace Lift.Sem.CallFrame
open Lift.P2.Total

/-- Replay a permuted call at a selected ordering of its input objects. -/
theorem PermLift.canonicalAt {policy : CpuPolicy} {R : Heap → Heap → Prop} {H K H' : Heap}
    (hh : ∃ m, H.Holds policy m) (hk : H.Perm K)
    (replay : ∀ (h k h' : Heap), (∃ m, h.Holds policy m) → h.Perm k → R h h' →
      ∃ k', R k k' ∧ h'.Perm k')
    (hr : PermLift R H H') : ∃ k', R K k' ∧ H'.Perm k' := by
  obtain ⟨h, h', hr, hs⟩ := hr
  obtain ⟨m, hm⟩ := hh
  have hheld : ∃ m, h.Holds policy m := ⟨m, (Heap.Holds_perm hs.perm_in).mp hm⟩
  obtain ⟨k', hr, hp⟩ := replay h K h' hheld (hs.perm_in.symm.trans hk) hr
  exact ⟨k', hr, hs.perm_out.trans hp⟩

end Lift.Sem.CallFrame
