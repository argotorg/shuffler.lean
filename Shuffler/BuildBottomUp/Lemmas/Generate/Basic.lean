module

public import Shuffler.Trace

@[expose] public section

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
  | Dup _ _ _ _ _ _ ih => exact ih hsecond
  | Push _ _ _ ih => exact ih hsecond
  | Load _ _ _ ih => exact ih hsecond

theorem Trace.onlyGenerates_noPop (trace : Trace spills source target) (h : trace.onlyGenerates) :
    trace.noPop := by
  induction trace with
  | Lit => trivial
  | Swap _ _ _ _ _ | Pop _ _ => exact h.elim
  | Dup _ _ _ _ _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih h
