import Shuffler.Optimality.ValueGraph.Build
import Shuffler.Optimality.Replay

namespace Shuffler.Optimality.SwapRuns

open Shuffler.Placement

-- A run has no POP and adds no copies, so every operation is a SWAP.
-- Skip the graph construction for an empty run.
def improve (run : BuiltTrace spills source target 0) : BuiltTrace spills source target 0 :=
  if run.trace.swapCount = 0 then run
  else (ValueGraph.build spills source target).getD run

structure Pending (spills : SpillSet) (source target : Stack) where
  middle : Stack
  before : Trace spills source middle
  run : BuiltTrace spills middle target 0

def Pending.flush (pending : Pending spills source target) : Trace spills source target :=
  pending.before.concat (improve pending.run).trace

def Pending.raw (pending : Pending spills source target) : Trace spills source target :=
  pending.before.concat pending.run.trace

def Pending.ofTrace (trace : Trace spills source target) : Pending spills source target :=
  ⟨target, trace, ⟨.Lit target, trivial, rfl⟩⟩

def Pending.appendSwap (pending : Pending spills source target) (depth : Nat)
    (hlen : depth < target.length) (hlo : 1 ≤ depth) (hhi : depth ≤ MAX_SWAP_DEPTH) :
    Pending spills source (target.swap (target.length - 1) (target.length - 1 - depth)) :=
  ⟨pending.middle, pending.before,
    ⟨.Swap depth hlen hlo hhi pending.run.trace, pending.run.noPop, pending.run.additions⟩⟩

-- Keep one maximal SWAP run pending. A growth operation or POP closes it.
-- The endpoint types ensure that the next original operation sees the
-- same concrete stack as before normalization.
def scan (trace : Trace spills source target) : Pending spills source target := by
  cases trace with
  | Lit => exact .ofTrace (.Lit source)
  | Swap depth hlen hlo hhi earlier =>
      exact (scan earlier).appendSwap depth hlen hlo hhi
  | Dup depth hlen hlo hhi earlier =>
      exact .ofTrace (.Dup depth hlen hlo hhi (scan earlier).flush)
  | Pop hlen earlier => exact .ofTrace (.Pop hlen (scan earlier).flush)
  | Push value hfree earlier => exact .ofTrace (.Push value hfree (scan earlier).flush)
  | Load id hspill earlier => exact .ofTrace (.Load id hspill (scan earlier).flush)
termination_by structural trace

def normalize (trace : Trace spills source target) : Trace spills source target := (scan trace).flush

def withoutSwaps : Trace spills source target → List Op
  | .Lit _ => []
  | .Swap _ _ _ _ trace => withoutSwaps trace
  | .Dup depth _ _ _ trace => withoutSwaps trace ++ [.dup depth]
  | .Pop _ trace => withoutSwaps trace ++ [.pop]
  | .Push value _ trace => withoutSwaps trace ++ [.push value]
  | .Load id _ trace => withoutSwaps trace ++ [.load id]

def births : Trace spills source target → List Value
  | .Lit _ => []
  | .Swap _ _ _ _ trace => births trace
  | @Trace.Dup _ _ previous depth hlen hlo _ trace =>
      births trace ++ [previous[previous.length - depth]'(by omega)]
  | .Pop _ trace => births trace
  | .Push value _ trace => births trace ++ [value]
  | .Load id _ trace => births trace ++ [.Var id]

end Shuffler.Optimality.SwapRuns
