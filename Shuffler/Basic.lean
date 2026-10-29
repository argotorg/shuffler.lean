module

public import Mathlib.Data.Nat.Notation
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Zero indexed from the top of the stack.
def MAX_SWAP_DEPTH := 16
def MAX_DUP_DEPTH := 15

-- The slot at `offset` of the working stack is out of reach by `excess` slots.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:277-281.
structure Blocked where
  offset : ℕ
  excess : ℕ
  deriving DecidableEq, Repr

inductive ShuffleErr : Type where
  | Blocked (blocked : Blocked)
  | assertion (reason : String)
  deriving DecidableEq, Repr

abbrev Word := Fin (2 ^ 256)

abbrev Byte := Fin (2 ^ 8)

structure VarId where
  val : ℕ
  deriving DecidableEq
