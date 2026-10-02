import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Basic
import Batteries.Data.List.Basic
import Shuffler.Basic


--- Values -----------------------------------------------------------------------------------------


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

-- Function return labels are not modelled yet, so no value is one.
def Value.isFunctionReturnLabel : Value → Bool
| _ => false

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

lemma swap_depth_pos (stack : Stack) (pos : Fin stack.length)
    (hbelow : pos.val + 1 < stack.length) : 1 ≤ (stack.offsetToDepth pos).val := by
  dsimp [Stack.offsetToDepth]; omega

lemma top_lt_length (stack : Stack) (pos : Fin stack.length) :
    stack.length - 1 < stack.length := by
  have := pos.isLt
  omega

lemma stack_push_len (stack : Stack) (slot : Value) :
  stack.length + 1 = (stack ++ [slot]).length := by simp
