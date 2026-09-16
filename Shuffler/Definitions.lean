import Init.Data.List.Basic
import Mathlib.Data.Nat.Basic

abbrev Value := ℕ

abbrev Stack := List Value

def List.swap
  {α : Type u} (xs : List α) (i j : ℕ)
  (hi : i < xs.length := by get_elem_tactic)
  (hj : j < xs.length := by get_elem_tactic)
  := (xs.set i xs[j]).set j xs[i]

inductive Trace : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap (prev.length - 1) (prev.length - 1 - idx))

def Source : Stack := [0, 1, 2, 3]
def Target : Stack := [0, 3, 2, 1]

def TraceLitProducesExactStack : Trace Source Source := Trace.Lit Source
def Swap2Swaps2 : Trace Source Target := Trace.Swap 2
  (by dsimp[Source]; simp) (by simp) (by simp) (Trace.Lit Source)


def ApplyPermutation
  (source : Stack)
  (perm : List (Fin source.length))
  : Stack
  := sorry

def permute
  (source : Stack)
  (perm : List (Fin source.length))
  (hlen : source.length < 17)
   : (Trace source (ApplyPermutation source perm))
  :=
  sorry
