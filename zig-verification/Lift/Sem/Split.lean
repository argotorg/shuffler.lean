module

public import Lift.Trusted.Object

@[expose] public section

/-! The split of one object into two adjacent objects. An object whose fields are `xs ++ ys` holds
in a memory when the object of `xs` at its address and the object of `ys` after it hold, if the
whole object does not wrap past `2^64`. The lemmas are generic: they do not name a function. -/

namespace Lift.Sem.Split

open Lift.P2.Total Lift.Trusted

theorem offsets_append (n : Nat) (fs gs : List Field) :
    offsets n (fs ++ gs) = offsets n fs ++ offsets (n + (fs.map fun f => f.w.bytes).sum) gs := by
  induction fs generalizing n with
  | nil => simp [offsets]
  | cons f fs ih =>
    simp only [List.cons_append, offsets, ih, List.map_cons, List.sum_cons, List.cons.injEq,
      true_and]
    congr 2
    omega

theorem offsets_shift (n k : Nat) (gs : List Field) :
    offsets (n + k) gs = (offsets k gs).map fun x => (n + x.1, x.2) := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    simp only [offsets, List.map_cons, List.cons.injEq, true_and]
    rw [show n + k + g.w.bytes = n + (k + g.w.bytes) by omega, ih]

theorem offsets_shift0 (n : Nat) (gs : List Field) :
    offsets n gs = (offsets 0 gs).map fun x => (n + x.1, x.2) := by
  have := offsets_shift n 0 gs
  rwa [Nat.add_zero] at this

/-- The address `a + s`, as a natural number, with the wrap at `2^64`. -/
theorem toNat_add_ofNat (a : BitVec 64) (s : Nat) :
    (a + BitVec.ofNat 64 s).toNat = (a.toNat + s) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]

/-- The second part ends within the address space when the whole object does. -/
theorem second_part_fits (a : BitVec 64) (s1 s2 : Nat) (hw : a.toNat + (s1 + s2) ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 s1).toNat + s2 ≤ 2 ^ 64 := by
  rw [toNat_add_ofNat]
  by_cases hl : a.toNat + s1 < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hl]
    omega
  · have e : a.toNat + s1 = 2 ^ 64 := by omega
    rw [e, Nat.mod_self]
    omega

/-- The two parts of a split do not share a byte. -/
theorem apart_split (a : BitVec 64) (fs gs : List Field) (wr : Bool)
    (hw : a.toNat + (Object.mk a (fs ++ gs) wr).size ≤ 2 ^ 64) :
    Apart a (Object.mk a fs wr).size (a + BitVec.ofNat 64 (Object.mk a fs wr).size)
      (Object.mk a gs wr).size := by
  have hs : (Object.mk a (fs ++ gs) wr).size =
      (Object.mk a fs wr).size + (Object.mk a gs wr).size := by
    simp [Object.size]
  unfold Apart
  rw [toNat_add_ofNat]
  by_cases hl : a.toNat + (Object.mk a fs wr).size < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hl]
    exact Or.inl (Nat.le_refl _)
  · have e : a.toNat + (Object.mk a fs wr).size = 2 ^ 64 := by omega
    rw [e, Nat.mod_self]
    exact Or.inr (by omega)

/-- One object with the fields `fs ++ gs` is the object of `fs` at `a`, and the object of `gs`
right after it, when the whole object does not wrap past `2^64`. -/
theorem has_append (policy : CpuPolicy) (m : DataMem) (a : BitVec 64) (fs gs : List Field)
    (wr : Bool) (hw : a.toNat + (Object.mk a (fs ++ gs) wr).size ≤ 2 ^ 64) :
    Mem.has policy m ⟨a, fs ++ gs, wr⟩ ↔
      Mem.has policy m ⟨a, fs, wr⟩ ∧
        Mem.has policy m ⟨a + BitVec.ofNat 64 (Object.mk a fs wr).size, gs, wr⟩ := by
  have hs : (Object.mk a (fs ++ gs) wr).size =
      (Object.mk a fs wr).size + (Object.mk a gs wr).size := by
    simp [Object.size]
  -- the address of a field of the second part
  have addr : ∀ k : Nat, a + BitVec.ofNat 64 ((Object.mk a fs wr).size + k) =
      a + BitVec.ofNat 64 (Object.mk a fs wr).size + BitVec.ofNat 64 k := by
    intro k; rw [BitVec.add_assoc, BitVec.ofNat_add]
  have hnw2 : (a + BitVec.ofNat 64 (Object.mk a fs wr).size).toNat +
      (Object.mk a gs wr).size ≤ 2 ^ 64 := by
    apply second_part_fits
    simp only [Object.size] at hs hw ⊢
    omega
  unfold Mem.has
  simp only [offsets_append, Nat.zero_add, List.mem_append]
  rw [offsets_shift0 _ gs]
  simp only [List.mem_map]
  show (_ ∧ ∀ x, x ∈ offsets 0 fs ∨ (∃ y ∈ offsets 0 gs, ((Object.mk a fs wr).size + y.1, y.2) = x) → _) ↔ _
  constructor
  · rintro ⟨-, h⟩
    refine ⟨⟨by simp only [Object.size] at hs hw ⊢; omega, fun x hx => h x (.inl hx)⟩, hnw2,
      fun x hx => ?_⟩
    have := h ((Object.mk a fs wr).size + x.1, x.2) (.inr ⟨x, hx, rfl⟩)
    rw [addr] at this
    exact this
  · rintro ⟨⟨-, h1⟩, -, h2⟩
    refine ⟨hw, fun x hx => ?_⟩
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact h1 x hx
    · have := h2 y hy
      rw [← addr] at this
      exact this

end Lift.Sem.Split
