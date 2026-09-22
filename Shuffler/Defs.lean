import Mathlib.Data.Nat.Notation
import Batteries.Data.List.Basic
import Mathlib.Data.PEquiv

abbrev Value := ℕ
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

abbrev Mapping := PEquiv ℕ ℕ

abbrev Mapping' (target : Stack) := (source : Stack) × PEquiv (Fin source.length) (Fin target.length)

abbrev Mapping'' (source : Stack) (target : Stack) := PEquiv (Fin source.length) (Fin target.length)

structure Hi (source : Stack) (t : Stack) where
  mapping : Mapping' t
  mapping' : Mapping'' source t
  mapping'' : Mapping

def pop : (mapping : Mapping' target) → Mapping' target
| ⟨xs, ⟨toFun, invFun, hinv⟩⟩ => by
  have hlen : xs.dropLast.length ≤ xs.length := by
    simp only [List.length_dropLast]
    exact Nat.sub_le _ _
  let toFun' := fun (x : Fin xs.dropLast.length) =>
    toFun ⟨x.val, Nat.lt_of_lt_of_le x.isLt hlen⟩
  let invFun' : Fin target.length → Option (Fin xs.dropLast.length) := fun x =>
    (invFun x).bind fun i =>
      if h : i.val < xs.dropLast.length then some ⟨i.val, h⟩ else none
  refine ⟨xs.dropLast, ⟨toFun', invFun', ?_⟩⟩
  intro a b
  dsimp [toFun', invFun']
  rw [← hinv]
  cases invFun b <;> simp [Fin.ext_iff]
  intro h
  simpa only [h, List.length_dropLast] using a.isLt

--def src := [1,2,3,4]
--def
/-
	void pop()
	{
		m_stack.pop();
		m_mapping.pop();
	}

	void push(StackSlot const& _slot, StackOffset const _destination)
	{
		m_stack.push(_slot);
		m_mapping.push(_destination);
	}

	void dup(StackOffset const _copy, StackOffset const _destination)
	{
		m_stack.dup(_copy);
		m_mapping.push(_destination);
	}

-/
