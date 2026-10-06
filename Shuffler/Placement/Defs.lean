import Shuffler.Feasibility.Spec

theorem Trace.noPop_cast (h : result = other) (trace : Trace spills source result) :
    (h ▸ trace).noPop ↔ trace.noPop := by cases h; rfl

theorem Trace.additions_cast (h : result = other) (trace : Trace spills source result) :
    (h ▸ trace).additions = trace.additions := by cases h; rfl

theorem Trace.noPop_concat (first : Trace spills source middle)
    (second : Trace spills middle result) (hfirst : first.noPop) (hsecond : second.noPop) :
    (first.concat second).noPop := by
  induction second with
  | Lit => exact hfirst
  | Pop _ _ => exact False.elim hsecond
  | Swap _ _ _ _ _ ih | Dup _ _ _ _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih hsecond

theorem Trace.additions_concat (first : Trace spills source middle)
    (second : Trace spills middle result) :
    (first.concat second).additions = first.additions + second.additions := by
  induction second with
  | Lit => simp [Trace.concat, Trace.additions]
  | Pop _ _ ih | Swap _ _ _ _ _ ih => exact ih
  | Dup _ _ _ _ _ ih | Push _ _ _ ih | Load _ _ _ ih =>
    simp only [Trace.concat, Trace.additions, ih, Multiset.add_assoc]

namespace Shuffler.Placement

theorem CanPlace.refl (spills : SpillSet) (source : Stack) : CanPlace spills source source 0 :=
  ⟨.Lit source, trivial, rfl⟩

theorem CanPlace.trans {source middle target : Stack} {first second : Multiset Value}
    (hfirst : CanPlace spills source middle first) (hsecond : CanPlace spills middle target second) :
    CanPlace spills source target (first + second) := by
  obtain ⟨left, hl, ha⟩ := hfirst
  obtain ⟨right, hr, hb⟩ := hsecond
  exact ⟨left.concat right, left.noPop_concat right hl hr,
    by rw [Trace.additions_concat, ha, hb]⟩

end Shuffler.Placement
