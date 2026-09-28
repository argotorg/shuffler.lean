import Mathlib.Data.Nat.Notation
import Batteries.Data.List.Basic

abbrev Word := Fin (2 ^ 256)

structure VarId where
  val : ℕ
  deriving DecidableEq

-- Zero indexed from the top of the stack.
def MAX_SWAP_DEPTH := 16
def MAX_DUP_DEPTH := 15

inductive ShuffleErr : Type where
  | Blocked : ℕ → ShuffleErr

inductive Value : Type where
  | Var (id : VarId)
  | Lit (val : Word)
  | Wildcard

deriving instance DecidableEq for Value

def Value.is_junk : Value → Prop
| Wildcard => true
| _ => false

instance (v : Value) : Decidable v.is_junk := by
  cases v <;> unfold Value.is_junk <;> infer_instance

def Value.can_be_freely_generated : Value → Prop
| Var _ => false
| _ => true

instance (v : Value) : Decidable v.can_be_freely_generated := by
  cases v <;> unfold Value.can_be_freely_generated <;> infer_instance

theorem Value.can_be_freely_generated_of_is_junk (v : Value) (hjunk : v.is_junk) :
    v.can_be_freely_generated := by
  cases v <;> simp_all [Value.is_junk, Value.can_be_freely_generated]

abbrev Stack := List Value

inductive Trace : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx ≤ MAX_SWAP_DEPTH)
    → Trace start prev
    → Trace start (prev.swap (prev.length - 1) (prev.length - 1 - idx))
  | Dup
    : (idx : ℕ)
    → (hlen : idx ≤ prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx ≤ MAX_DUP_DEPTH + 1)
    → Trace start prev
    → Trace start (prev ++ [prev[prev.length - idx]])
  | Pop
    : (hlen : 0 < prev.length)
    → Trace start prev
    → Trace start prev.dropLast
  | Push
    : (v : Value)
    → (hfree : v.can_be_freely_generated := by decide)
    → Trace start prev
    → Trace start (prev ++ [v])

def Trace.concat (t1 : Trace a b) (t2 : Trace b c) : Trace a c :=
  match t2 with
  | .Lit _ => t1
  | .Swap idx hlen hlo hhi t => .Swap idx hlen hlo hhi (t1.concat t)
  | .Dup idx hlen hlo hhi t => .Dup idx hlen hlo hhi (t1.concat t)
  | .Pop hlen t => .Pop hlen (t1.concat t)
  | .Push v hfree t => .Push v hfree (t1.concat t)

def Trace.swapCount : Trace source result → ℕ
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.swapCount + 1
  | .Dup _ _ _ _ trace => trace.swapCount
  | .Pop _ trace => trace.swapCount
  | .Push _ _ trace => trace.swapCount
