module

public import Batteries.Data.List.Basic
public import Shuffler.Basic
public import Mathlib.Tactic.ToDual
import Batteries.Data.List.Lemmas
import Mathlib.Data.Finset.Attr
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

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

def Value.isVariable : Value → Prop
| Var _ => True
| _ => False

instance (v : Value) : Decidable v.isVariable := by
  cases v <;> unfold Value.isVariable <;> infer_instance

def Value.can_be_freely_generated : Value → Prop
| Lit _ => True
| Wildcard => True
| Var _ => False
| FunctionReturnLabel => False

instance (v : Value) : Decidable v.can_be_freely_generated := by
  cases v <;> unfold Value.can_be_freely_generated <;> infer_instance

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

abbrev Stack.offsetToDepth (stack : Stack) (idx : Fin stack.length) : Fin stack.length :=
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

-- Whether a swap can exchange the top with the slot at `pos`: below the top and within swap reach
def Stack.isValidSwapTarget (stack : Stack) (pos : Fin stack.length) : Prop :=
  1 ≤ (stack.offsetToDepth pos).val ∧ stack.offsetToDepth pos ≤ MAX_SWAP_DEPTH

instance (stack : Stack) (pos : Fin stack.length) : Decidable (stack.isValidSwapTarget pos) :=
  by unfold Stack.isValidSwapTarget; infer_instance

lemma dup_slot_eq (stack : Stack) (copy : Fin stack.length) :
    stack[stack.length - ((stack.offsetToDepth copy).val + 1)] = stack[copy] := by
  have hcopy : stack.length - ((stack.offsetToDepth copy).val + 1) = copy.val := by
    dsimp [Stack.offsetToDepth]; omega
  exact getElem_congr_idx hcopy

lemma dup_stack_eq (stack : Stack) (copy : Fin stack.length) :
    stack ++ [stack[stack.length - ((stack.offsetToDepth copy).val + 1)]] =
      stack ++ [stack[copy]] :=
  congrArg (fun slot => stack ++ [slot]) (dup_slot_eq stack copy)

lemma swap_stack_eq (stack : Stack) (pos : Fin stack.length) :
    stack.swap (stack.length - 1) (stack.length - 1 - (stack.offsetToDepth pos).val) =
      stack.swap pos (stack.length - 1) := by
  have hpos : stack.length - 1 - (stack.offsetToDepth pos).val = pos.val := by
    dsimp [Stack.offsetToDepth]; omega
  rw [hpos, List.swap_comm]

-- The offset of the top slot of a non-empty stack
abbrev Stack.topOffset (stack : Stack) (h : 0 < stack.length) : Fin stack.length :=
  ⟨stack.length - 1, by omega⟩

lemma stack_push_len (stack : Stack) (slot : Value) :
  stack.length + 1 = (stack ++ [slot]).length := by simp

lemma stack_pop_len (stack : Stack) (h : 0 < stack.length) :
    stack.length = stack.dropLast.length + 1 := by
  simp; omega

theorem swap_eq_of_equal (stack : Stack) (a b : Fin stack.length)
    (heq : stack[a] = stack[b]) : stack.swap a b = stack := by
  apply List.ext_getElem (by simp)
  intro i hi hs
  by_cases ha : i = a.val
  · subst i; simpa [List.getElem_swap, a.isLt, b.isLt] using heq.symm
  by_cases hb : i = b.val
  · subst i; simpa [ha, a.isLt] using heq
  simp [ha, hb]


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
