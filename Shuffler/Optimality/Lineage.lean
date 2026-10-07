import Shuffler.Feasibility.Spec
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Count the operations that can move a value's last occurrence upward. A DUP
can add its copy at most sixteen slots above its source. A SWAP can move its
lower selected value at most sixteen slots upward. PUSH and LOAD start a new
lineage. These counts do not change the production Trace type.
-/

namespace Shuffler.Optimality.Lineage

def maxIndex (value : Value) (stack : Stack) : Nat :=
  (Finset.range stack.length).sup fun index => if stack[index]? = some value then index else 0

def dupCount (value : Value) : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => dupCount value trace
  | @Trace.Dup _ _ prev index hlen hlo _ trace =>
      dupCount value trace + if prev[prev.length - index]'(by omega) = value then 1 else 0
  | .Pop _ trace => dupCount value trace
  | .Push _ _ trace => dupCount value trace
  | .Load _ _ trace => dupCount value trace

def directCount (value : Value) : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => directCount value trace
  | .Dup _ _ _ _ trace => directCount value trace
  | .Pop _ trace => directCount value trace
  | .Push added _ trace => directCount value trace + if added = value then 1 else 0
  | .Load id _ trace => directCount value trace + if .Var id = value then 1 else 0

-- One SWAP is charged to at most one value. Equal-value swaps can be counted
-- even though they do not advance the last occurrence.
def upwardCount (value : Value) : Trace spills source target → Nat
  | .Lit _ => 0
  | @Trace.Swap _ _ prev index hlen _ _ trace =>
      upwardCount value trace + if prev[prev.length - 1 - index]'(by omega) = value then 1 else 0
  | .Dup _ _ _ _ trace => upwardCount value trace
  | .Pop _ trace => upwardCount value trace
  | .Push _ _ trace => upwardCount value trace
  | .Load _ _ trace => upwardCount value trace

-- Round the remaining positive distance up to a multiple of sixteen.
def requiredSwaps (value : Value) (source target : Stack) (missing : Multiset Value) : Nat :=
  (maxIndex value target - maxIndex value source - 16 * missing.count value + 15) / 16

def retainedBound (values : Finset Value) (source target : Stack) (missing : Multiset Value) : Nat :=
  values.sum fun value => requiredSwaps value source target missing

end Shuffler.Optimality.Lineage
