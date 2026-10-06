import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Basic
import Batteries.Data.List.Basic
import Shuffler.Basic
import Shuffler.Stack

abbrev SpillSet := Finset VarId

def SpillSet.is_spilled (spills : SpillSet) : (val : Value) → Prop
| .Var id => id ∈ spills
| _ => false

instance (spills : SpillSet) (v : Value) : Decidable (spills.is_spilled v) := by
  cases v <;> unfold SpillSet.is_spilled <;> infer_instance

inductive Trace (spills : SpillSet) : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace spills s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx ≤ MAX_SWAP_DEPTH)
    → Trace spills start prev
    → Trace spills start (prev.swap (prev.length - 1) (prev.length - 1 - idx))
  -- TODO: dup should not accept a function return label
  | Dup
    : (idx : ℕ)
    → (hlen : idx ≤ prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx ≤ MAX_DUP_DEPTH + 1)
    → Trace spills start prev
    → Trace spills start (prev ++ [prev[prev.length - idx]])
  | Pop
    : (hlen : 0 < prev.length)
    → Trace spills start prev
    → Trace spills start prev.dropLast
  | Push
    : (v : Value)
    → (hfree : v.can_be_freely_generated := by decide)
    → Trace spills start prev
    → Trace spills start (prev ++ [v])
  | Load
    : (id : VarId)
    → (hspilled : id ∈ spills)
    → Trace spills start prev
    → Trace spills start (prev ++ [.Var id])

def Trace.concat (t1 : Trace spills a b) (t2 : Trace spills b c) : Trace spills a c :=
  match t2 with
  | .Lit _ => t1
  | .Swap idx hlen hlo hhi t => .Swap idx hlen hlo hhi (t1.concat t)
  | .Dup idx hlen hlo hhi t => .Dup idx hlen hlo hhi (t1.concat t)
  | .Pop hlen t => .Pop hlen (t1.concat t)
  | .Push v hfree t => .Push v hfree (t1.concat t)
  | .Load id hspilled t => .Load id hspilled (t1.concat t)

def Trace.swapCount : Trace spills source result → ℕ
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.swapCount + 1
  | .Dup _ _ _ _ trace => trace.swapCount
  | .Pop _ trace => trace.swapCount
  | .Push _ _ trace => trace.swapCount
  | .Load _ _ trace => trace.swapCount
