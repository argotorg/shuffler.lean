import Shuffler.BuildBottomUp.Lemmas.Placement.Basic

namespace Shuffler.Optimality.BBU

-- The earlier trace can contain POPs. Only the new suffix is restricted.
def Extends (first : Trace spills source middle) (whole : Trace spills source target) : Prop :=
  ∃ suffix : Trace spills middle target, suffix.noPop ∧ whole = first.concat suffix

@[simp] theorem Extends.refl (trace : Trace spills source target) : Extends trace trace :=
  ⟨.Lit target, trivial, rfl⟩

private theorem concat_assoc (a : Trace spills source first) (b : Trace spills first middle)
    (c : Trace spills middle target) : (a.concat b).concat c = a.concat (b.concat c) := by
  induction c <;> simp_all [Trace.concat]

theorem swapCount_concat (first : Trace spills source middle)
    (second : Trace spills middle target) :
    (first.concat second).swapCount = first.swapCount + second.swapCount := by
  induction second <;> simp_all [Trace.concat, Trace.swapCount, Nat.add_assoc]

theorem Extends.trans {a : Trace spills source first} {b : Trace spills source middle}
    {c : Trace spills source target} (hab : Extends a b) (hbc : Extends b c) : Extends a c := by
  rcases hab with ⟨left, hl, rfl⟩
  rcases hbc with ⟨right, hr, rfl⟩
  exact ⟨left.concat right, left.noPop_concat right hl hr, concat_assoc _ _ _⟩

@[simp] theorem Extends.transport (h : a = b) (first : Trace spills source middle)
    (trace : Trace spills source a) :
    Extends first (h ▸ trace : Trace spills source b) ↔ Extends first trace := by cases h; rfl

@[simp] theorem Extends.swap {first : Trace spills source middle} {trace : Trace spills source prev}
    (idx : Nat) (hlen : idx < prev.length) (hlo : 1 ≤ idx) (hhi : idx ≤ MAX_SWAP_DEPTH)
    (h : Extends first trace) : Extends first (.Swap idx hlen hlo hhi trace) := by
  rcases h with ⟨suffix, hp, rfl⟩
  exact ⟨.Swap idx hlen hlo hhi suffix, hp, rfl⟩

@[simp] theorem Extends.dup {first : Trace spills source middle} {trace : Trace spills source prev}
    (idx : Nat) (hlen : idx ≤ prev.length) (hlo : 1 ≤ idx) (hhi : idx ≤ MAX_DUP_DEPTH + 1)
    (h : Extends first trace) : Extends first (.Dup idx hlen hlo hhi trace) := by
  rcases h with ⟨suffix, hp, rfl⟩
  exact ⟨.Dup idx hlen hlo hhi suffix, hp, rfl⟩

@[simp] theorem Extends.push {first : Trace spills source middle} {trace : Trace spills source prev}
    (value : Value) (hfree : value.can_be_freely_generated)
    (h : Extends first trace) : Extends first (.Push value hfree trace) := by
  rcases h with ⟨suffix, hp, rfl⟩
  exact ⟨.Push value hfree suffix, hp, rfl⟩

@[simp] theorem Extends.load {first : Trace spills source middle} {trace : Trace spills source prev}
    (id : VarId) (hspill : id ∈ spills)
    (h : Extends first trace) : Extends first (.Load id hspill trace) := by
  rcases h with ⟨suffix, hp, rfl⟩
  exact ⟨.Load id hspill suffix, hp, rfl⟩

end Shuffler.Optimality.BBU
