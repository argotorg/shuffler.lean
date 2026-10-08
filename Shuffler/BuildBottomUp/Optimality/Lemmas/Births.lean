import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.GeneralBound
import Shuffler.CostModel
import Shuffler.BuildBottomUp.Lemmas.Placement.TraceInvariants

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

def dupCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Push _ _ trace | .Load _ _ trace => dupCount trace
  | .Dup _ _ _ _ trace => dupCount trace + 1

def pushCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Dup _ _ _ _ trace | .Load _ _ trace => pushCount trace
  | .Push _ _ trace => pushCount trace + 1

def loadCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Dup _ _ _ _ trace | .Push _ _ trace => loadCount trace
  | .Load _ _ trace => loadCount trace + 1

theorem births_eq_sum (trace : Trace spills source target) :
    trace.additions.card = dupCount trace + pushCount trace + loadCount trace := by
  induction trace <;> simp_all [Trace.additions, dupCount, pushCount, loadCount] <;> omega

end Shuffler.Optimality.BBU
