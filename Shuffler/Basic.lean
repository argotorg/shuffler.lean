import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Basic
import Batteries.Data.List.Basic

-- Zero indexed from the top of the stack.
def MAX_SWAP_DEPTH := 16
def MAX_DUP_DEPTH := 15

inductive ShuffleErr : Type where
  | Blocked : ℕ → ShuffleErr

abbrev Word := Fin (2 ^ 256)

structure VarId where
  val : ℕ
  deriving DecidableEq
