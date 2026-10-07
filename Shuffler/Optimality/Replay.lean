import Shuffler.Optimality.Cost
import Shuffler.Placement.Build

namespace Shuffler.Optimality

-- Depth is one-based for both DUP and SWAP, as in the emitted instruction.
-- POP is retained for trace extraction. The no-POP replay rejects it.
inductive Op where
  | swap (depth : Nat)
  | dup (index : Nat)
  | push (value : Value)
  | load (id : VarId)
  | pop
  deriving DecidableEq

def Op.cost (costs : PrimitiveCosts) : Op → Cost
  | .swap _ => costs.swap
  | .dup _ => costs.dup
  | .push value => costs.push value
  | .load id => costs.load id
  | .pop => costs.pop

def opsCost (costs : PrimitiveCosts) : List Op → Cost
  | [] => Cost.zero
  | op :: rest => (op.cost costs).add (opsCost costs rest)

theorem opsCost_append (costs : PrimitiveCosts) (first second : List Op) :
    opsCost costs (first ++ second) =
      (opsCost costs first).add (opsCost costs second) := by
  induction first with
  | nil => simp [opsCost]
  | cons op rest ih => simp [opsCost, ih, Cost.add_assoc]

-- Extraction keeps execution order. A vector implementation can collect in
-- reverse order and reverse once; the list form keeps the cost proof short.
def flatten : Trace spills source target → List Op
  | .Lit _ => []
  | .Swap depth _ _ _ trace => flatten trace ++ [.swap depth]
  | .Dup index _ _ _ trace => flatten trace ++ [.dup index]
  | .Pop _ trace => flatten trace ++ [.pop]
  | .Push value _ trace => flatten trace ++ [.push value]
  | .Load id _ trace => flatten trace ++ [.load id]

theorem opsCost_flatten (costs : PrimitiveCosts) (trace : Trace spills source target) :
    opsCost costs (flatten trace) = traceCost costs trace := by
  induction trace <;>
    simp_all [flatten, traceCost, opsCost_append, opsCost, Op.cost]

structure ReplayResult (spills : SpillSet) (source : Stack) where
  target : Stack
  added : Multiset Value
  built : Shuffler.Placement.BuiltTrace spills source target added

def ReplayResult.nil (spills : SpillSet) (source : Stack) : ReplayResult spills source :=
  ⟨source, 0, ⟨.Lit source, trivial, rfl⟩⟩

def ReplayResult.append (first : ReplayResult spills source)
    (second : ReplayResult spills first.target) : ReplayResult spills source :=
  ⟨second.target, first.added + second.added, first.built.trans second.built⟩

-- Each successful branch constructs a production Trace instruction.
def replayStep (spills : SpillSet) (source : Stack) : Op → Option (ReplayResult spills source)
  | .swap depth =>
      if h : depth < source.length ∧ 1 ≤ depth ∧ depth ≤ MAX_SWAP_DEPTH then
        some ⟨source.swap (source.length - 1) (source.length - 1 - depth), 0,
          ⟨.Swap depth h.1 h.2.1 h.2.2 (.Lit source), trivial, rfl⟩⟩
      else none
  | .dup index =>
      if h : index ≤ source.length ∧ 1 ≤ index ∧ index ≤ MAX_DUP_DEPTH + 1 then
        let value := source[source.length - index]'(by omega)
        some ⟨source ++ [value], {value},
          ⟨.Dup index h.1 h.2.1 h.2.2 (.Lit source), trivial,
            by simp only [Trace.additions, zero_add]; rfl⟩⟩
      else none
  | .push value =>
      if h : value.can_be_freely_generated then
        some ⟨source ++ [value], {value},
          ⟨.Push value h (.Lit source), trivial,
            by simp only [Trace.additions, zero_add]⟩⟩
      else none
  | .load id =>
      if h : id ∈ spills then
        let trace : Trace spills source (source ++ [.Var id]) :=
          .Load id h (.Lit source)
        some ⟨source ++ [.Var id], {.Var id},
          ⟨trace, by trivial,
            by simp only [trace, Trace.additions, zero_add]⟩⟩
      else none
  | .pop => none

def replayFrom (state : ReplayResult spills source) : List Op → Option (ReplayResult spills source)
  | [] => some state
  | op :: rest => do
      let step ← replayStep spills state.target op
      replayFrom (state.append step) rest

def replay (spills : SpillSet) (source : Stack) (ops : List Op) :
    Option (ReplayResult spills source) :=
  replayFrom (ReplayResult.nil spills source) ops

-- Check the concrete target and the exact additions before exposing a plan.
def replayExact (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (ops : List Op) : Option (Shuffler.Placement.BuiltTrace spills source target missing) := do
  let result ← replay spills source ops
  if ht : result.target = target then
    if hm : result.added = missing then
      some (result.built.cast rfl ht hm)
    else none
  else none

end Shuffler.Optimality
