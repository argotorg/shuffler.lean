import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Basic
import Batteries.Data.List.Basic

-- Zero indexed from the top of the stack.
def MAX_SWAP_DEPTH := 16
def MAX_DUP_DEPTH := 15

inductive ShuffleErr : Type where
  -- The slot at `offset` of the working stack is out of reach by `excess` slots.
  -- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:277-281.
  | Blocked (offset : ℕ) (excess : ℕ)
  | assertion (reason : String)
  deriving DecidableEq, Repr

abbrev Word := Fin (2 ^ 256)

structure VarId where
  val : ℕ
  deriving DecidableEq
