module

public import Shuffler.Contracts
public import Shuffler.Stack
public import Mathlib.Data.Finset.Insert

@[expose] public section

abbrev SpillSet := Finset VarId

-- Add a variable slot to the spill set; reject other slots and duplicate IDs.
-- See solidity/libyul/backends/evm/ssa/spill/SpillSet.h:42.
def SpillSet.add (spills : SpillSet) (slot : Value) : Except ShuffleErr SpillSet := do
  let .Var id := slot | throw (.assertion "spill candidate must be a variable")
  _ ← Shuffler.requires (id ∉ spills) "value already spilled"
  return insert id spills

def SpillSet.is_spilled (spills : SpillSet) : (val : Value) → Prop
| .Var id => id ∈ spills
| _ => False

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

-- The trace adds values without changing or removing existing positions.
def Trace.onlyGenerates : Trace spills source result → Prop
  | .Lit _ => True
  | .Swap _ _ _ _ _ => False
  | .Dup _ _ _ _ trace => trace.onlyGenerates
  | .Pop _ _ => False
  | .Push _ _ trace => trace.onlyGenerates
  | .Load _ _ trace => trace.onlyGenerates

def Trace.noPop : Trace spills source result → Prop
  | .Lit _ => True
  | .Swap _ _ _ _ trace => trace.noPop
  | .Dup _ _ _ _ trace => trace.noPop
  | .Pop _ _ => False
  | .Push _ _ trace => trace.noPop
  | .Load _ _ trace => trace.noPop

-- Record the values actually added by DUP, PUSH, and LOAD.
def Trace.additions : Trace spills source result → Multiset Value
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.additions
  | @Dup _ _ prev idx hlen hlo _ trace =>
      trace.additions + {prev[prev.length - idx]'(by omega)}
  | .Pop _ trace => trace.additions
  | .Push value _ trace => trace.additions + {value}
  | .Load id _ trace => trace.additions + {.Var id}
