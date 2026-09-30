import Shuffler.BuildBottomUp.Defs

namespace BuildBottomUpTestSupport
open Shuffler.BuildBottomUp

inductive Operation where
  | swap (depth : ℕ) | dup (index : ℕ) | pop | push (value : Value) | load (id : VarId)
  deriving DecidableEq

-- Include every trace operation and operand, in order.
def operations : Trace spills source result → List Operation
  | .Lit _ => []
  | .Swap depth _ _ _ trace => operations trace ++ [.swap depth]
  | .Dup index _ _ _ trace => operations trace ++ [.dup index]
  | .Pop _ trace => operations trace ++ [.pop]
  | .Push value _ trace => operations trace ++ [.push value]
  | .Load id _ trace => operations trace ++ [.load id]

def observe (result : Except Error ((res : Stack) × Trace spills source res)) :
    Except Error (Stack × List Operation) :=
  result.map fun ⟨stack, trace⟩ => (stack, operations trace)


end BuildBottomUpTestSupport
