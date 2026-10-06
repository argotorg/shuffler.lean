import Shuffler.Feasibility.Spec

theorem Trace.onlyGenerates_cast (h : result = other)
    (trace : Trace spills source result) :
    (h ▸ trace).onlyGenerates ↔ trace.onlyGenerates := by
  cases h
  rfl

theorem Trace.onlyGenerates_concat (first : Trace spills source middle)
    (second : Trace spills middle result) (hfirst : first.onlyGenerates)
    (hsecond : second.onlyGenerates) : (first.concat second).onlyGenerates := by
  induction second with
  | Lit => exact hfirst
  | Swap _ _ _ _ _ => exact False.elim hsecond
  | Pop _ _ => exact False.elim hsecond
  | Dup _ _ _ _ _ ih => exact ih hsecond
  | Push _ _ _ ih => exact ih hsecond
  | Load _ _ _ ih => exact ih hsecond
