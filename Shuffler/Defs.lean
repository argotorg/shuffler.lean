import Mathlib.Data.Nat.Notation
import Batteries.Data.List.Basic
import Mathlib.Data.PEquiv

inductive ShuffleErr : Type where
  | Blocked : ℕ → ShuffleErr


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

def Trace.concat (t1 : Trace a b) (t2 : Trace b c) : Trace a c :=
  match t2 with
  | .Lit _ => t1
  | .Swap idx hlen hlo hhi t => .Swap idx hlen hlo hhi (t1.concat t)

def Trace.swapCount : Trace source result → ℕ
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.swapCount + 1


abbrev Mapping (source : Stack) (target : Stack) := PEquiv (Fin source.length) (Fin target.length)


def pop : (mapping : Mapping source target) → Mapping source.dropLast target
| ⟨toFun, invFun, hinv⟩ => by
  have hlen : source.dropLast.length ≤ source.length := by
    simp only [List.length_dropLast]
    exact Nat.sub_le _ _
  let toFun' := fun (x : Fin source.dropLast.length) =>
    toFun ⟨x.val, Nat.lt_of_lt_of_le x.isLt hlen⟩
  let invFun' : Fin target.length → Option (Fin source.dropLast.length) := fun x =>
    (invFun x).bind fun i =>
      if h : i.val < source.dropLast.length then some ⟨i.val, h⟩ else none
  refine ⟨toFun', invFun', ?_⟩
  simp only [toFun', invFun', ← hinv]
  intro a b
  cases invFun b <;> simp +contextual [Fin.ext_iff, -List.length_dropLast]

def bind (f : Mapping source target) (p : Fin source.length) (d : Fin target.length)
    (hp : f p = none) (hd : f.symm d = none) : Mapping source target where
  toFun := Function.update f p (some d)
  invFun := Function.update f.symm d (some p)
  inv a b := by
    simp only [Function.update_apply]
    split_ifs with ha hb hb
    · subst ha hb; simp
    · subst ha; simp [← PEquiv.eq_some_iff, hd, Ne.symm hb]
    · subst hb; simp [PEquiv.eq_some_iff, hp, Ne.symm ha]
    · exact PEquiv.mem_iff_mem f

-- to be edited
def push (val : Value) : (mapping : Mapping source target) → Mapping (source ++[val]) target
| ⟨toFun, invFun, hinv⟩ => by sorry

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
