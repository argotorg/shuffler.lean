import Mathlib.Data.Nat.Notation
import Batteries.Data.List.Basic

inductive ShuffleErr : Type where
  | Blocked : ℕ → ShuffleErr

inductive Value : Type where
  | Var (idx : ℕ )
  | Lit (val : Fin (2 ^ 256))
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

abbrev Stack := List Value

inductive Trace : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap (prev.length - 1) (prev.length - 1 - idx))

def Trace.concat (t1 : Trace a b) (t2 : Trace b c) : Trace a c :=
  match t2 with
  | .Lit _ => t1
  | .Swap idx hlen hlo hhi t => .Swap idx hlen hlo hhi (t1.concat t)

def Trace.swapCount : Trace source result → ℕ
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.swapCount + 1
