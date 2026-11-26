module
public import Lift.Sem.CallFrame
@[expose] public section
namespace Lift.Sem.CallFrame
open Lift.P2.Total

/-- Replay a permuted callee return from the caller's input heap. -/
theorem PermLift.canonical {policy : CpuPolicy} {R : Heap → Heap → Prop} {H H' : Heap}
    (hh : ∃ m, H.Holds policy m)
    (replay : ∀ (h k h' : Heap), (∃ m, h.Holds policy m) → h.Perm k → R h h' →
      ∃ k', R k k' ∧ h'.Perm k')
    (hr : PermLift R H H') : ∃ k', R H k' ∧ H'.Perm k' := by
  obtain ⟨h, h', hr, hs⟩ := hr
  obtain ⟨m, hm⟩ := hh
  have hheld : ∃ m, h.Holds policy m := ⟨m, (Heap.Holds_perm hs.perm_in).mp hm⟩
  obtain ⟨k', hk, hp⟩ := replay h H h' hheld hs.perm_in.symm hr
  exact ⟨k', hk, hs.perm_out.trans hp⟩

end Lift.Sem.CallFrame
