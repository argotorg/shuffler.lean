import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Basic
import Batteries.Data.List.Basic
import Shuffler.Basic
import Mathlib.Data.List.Forall2


--- Values -----------------------------------------------------------------------------------------


/-
c++ compares Lits by instructionId, not by literal value, but since the Lits
are all deduped so every same value Lit has the same instId, this is a valid
model.

https://github.com/argotorg/solidity/blob/6db6505030e17ce9a9c1dd9525fee509ad6cc2ac/libyul/backends/evm/ssa/InstructionStore.h#L199-L212
-/
inductive Value : Type where
  | Var (id : VarId)
  | Lit (val : Word)
  | Wildcard
  | FunctionReturnLabel

deriving instance DecidableEq for Value

def Value.is_junk : Value → Prop
| Wildcard => True
| _ => False

instance (v : Value) : Decidable v.is_junk := by
  cases v <;> unfold Value.is_junk <;> infer_instance

def Value.can_be_freely_generated : Value → Prop
| Lit _ => True
| Wildcard => True
| Var _ => False
| FunctionReturnLabel => False

instance (v : Value) : Decidable v.can_be_freely_generated := by
  cases v <;> unfold Value.can_be_freely_generated <;> infer_instance

-- Function return labels are not modelled yet
def Value.isFunctionReturnLabel : Value → Prop
| FunctionReturnLabel => True
| _ => False

instance (v : Value) : Decidable v.isFunctionReturnLabel := by
  cases v <;> unfold Value.isFunctionReturnLabel <;> infer_instance

theorem Value.can_be_freely_generated_of_is_junk (v : Value) (hjunk : v.is_junk) :
    v.can_be_freely_generated := by
  cases v <;> simp_all [Value.is_junk, Value.can_be_freely_generated]


--- Stacks -----------------------------------------------------------------------------------------


abbrev Stack := List Value

def Stack.offsetToDepth (stack : Stack) (idx : Fin stack.length) : Fin stack.length :=
  ⟨stack.length - 1 - idx, by omega⟩

def Stack.shallowestCopyPosition (stack : Stack) (slot : Value) : Option (Fin stack.length) :=
  (List.finRange stack.length).reverse.find?
    (fun pos => stack[pos] = slot)

def Stack.isDupReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.offsetToDepth pos) ≤ MAX_DUP_DEPTH

instance (stack : Stack) (pos : Fin stack.length) : Decidable (stack.isDupReachable pos) :=
  by unfold Stack.isDupReachable; infer_instance

-- Whether a copy of `slot` is within DUP reach
def Stack.hasCopy (stack : Stack) (slot : Value) : Prop :=
  ∃ pos : Fin stack.length, stack[pos] = slot ∧ stack.isDupReachable pos

def Stack.isSwapReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.offsetToDepth pos) ≤ MAX_SWAP_DEPTH

instance (stack : Stack) (pos : Fin stack.length) : Decidable (stack.isSwapReachable pos) :=
  by unfold Stack.isSwapReachable; infer_instance

lemma dup_stack_eq (stack : Stack) (copy : Fin stack.length) :
    stack ++ [stack[stack.length - ((stack.offsetToDepth copy).val + 1)]] =
      stack ++ [stack[copy]] := by
  have hcopy : stack.length - ((stack.offsetToDepth copy).val + 1) = copy.val := by
    dsimp [Stack.offsetToDepth]; omega
  exact congrArg (fun slot => stack ++ [slot]) (getElem_congr_idx hcopy)

lemma swap_stack_eq (stack : Stack) (pos : Fin stack.length) :
    stack.swap (stack.length - 1) (stack.length - 1 - (stack.offsetToDepth pos).val) =
      stack.swap pos (stack.length - 1) := by
  have hpos : stack.length - 1 - (stack.offsetToDepth pos).val = pos.val := by
    dsimp [Stack.offsetToDepth]; omega
  rw [hpos, List.swap_comm]

lemma top_lt_length (stack : Stack) (pos : Fin stack.length) :
    stack.length - 1 < stack.length := by
  have := pos.isLt
  omega

lemma stack_push_len (stack : Stack) (slot : Value) :
  stack.length + 1 = (stack ++ [slot]).length := by simp


--- Matching ---------------------------------------------------------------------------------------


-- A wildcard in the target accepts any source value.
def SlotMatches (actual target : Value) : Prop :=
  target.is_junk ∨ actual = target

instance (actual target : Value) : Decidable (SlotMatches actual target) := by
  unfold SlotMatches
  infer_instance

def StackMatches (actual target : Stack) : Prop :=
  List.Forall₂ SlotMatches actual target

instance (actual target : Stack) : Decidable (StackMatches actual target) := by
  unfold StackMatches
  infer_instance

theorem SlotMatches.refl (value : Value) : SlotMatches value value := Or.inr rfl

theorem StackMatches.refl (stack : Stack) : StackMatches stack stack := by
  induction stack with
  | nil => exact .nil
  | cons value rest ih => exact .cons (SlotMatches.refl value) ih

theorem StackMatches.length_eq (h : StackMatches actual target) :
    actual.length = target.length := List.Forall₂.length_eq h
