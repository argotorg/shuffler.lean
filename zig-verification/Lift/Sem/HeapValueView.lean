module
public import Lift.Sem.HeapReadShape

@[expose] public section

open Lift.P2.Total
namespace Lift.Sem

def Heap.ValueView (entry current : Heap) (policy : CpuPolicy) : Prop :=
  entry.SameShape current ∧
  (∀ o ∈ entry, o.writable = false → o ∈ current) ∧
  ∃ m, current.Holds policy m

theorem Heap.ValueView.refl {h : Heap} {policy : CpuPolicy}
    (hh : ∃ m, h.Holds policy m) : Heap.ValueView h h policy :=
  ⟨rfl, fun _ ho _ => ho, hh⟩

theorem Heap.ValueView.store {entry h k : Heap} {policy : CpuPolicy}
    {a : BitVec 64} {w : Width} {v : w.type}
    (hv : Heap.ValueView entry h policy) (hs : h.store a w v = .ok k) :
    Heap.ValueView entry k policy := by
  obtain ⟨hshape, hro, m, hh⟩ := hv
  obtain ⟨m', hwrite, hh', hfr⟩ := Heap.store_sound hh hs
  exact ⟨hshape.trans (Heap.store_sameShape hs),
    fun o ho hw => Heap.store_readonly_mem hs (hro o ho hw) hw, m', hh'⟩

end Lift.Sem
