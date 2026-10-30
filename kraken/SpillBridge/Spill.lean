import Shuffler.Trace
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image
import BbuKraken.FlatSpill

/-!
The link between the flat model of the spill set (`BbuKraken/FlatSpill.lean`) and
`SpillSet.add` and `SpillSet.is_spilled` of PR31 (`Shuffler/Trace.lean`).

- `val`: the value of a slot. A variable (`Flat.isVariable`) is the variable with the id of its
  payload. The C++ keys the spilled bytes by the payload only, so two variable slots with one
  payload are one variable.
- `abs sp n`: the spill set of the bytes `sp`: the ids below `n` whose byte is not 0.
- `isSpilled_iff`, `add_corr`: `Flat.spillIsSpilled` and `Flat.spillAdd` are `SpillSet.is_spilled`
  and `SpillSet.add` through `val` and `abs`, for a variable id below `n`.
- `spill_set_corr`: `Flat.spill_set` folds `SpillSet.add` over the adds, from the spill set of
  the bytes at the call, and gives `SpillSet.is_spilled` of the result for each query. It
  returns -2 for a failed add, and for an id that is not below `idCount` (`spill_set_bad`).
-/

namespace SpillBridge

open Bbu

-- The value of a slot.
def val (x : StackSlot) : Value :=
  if Flat.isVariable x then .Var ⟨x.payload.toNat⟩
  else if x.kind = Junk then .Wildcard
  else if x.kind = FunctionReturnLabel then .FunctionReturnLabel
  else .Lit (Fin.ofNat _ x.payload.toNat)

-- The spill set of the bytes `sp` of the ids below `n`.
def abs (sp : BitVec 32 → BitVec 8) (n : Nat) : SpillSet :=
  ((Finset.range n).filter fun i => sp (BitVec.ofNat 32 i) ≠ 0).image VarId.mk

theorem mem_abs {sp : BitVec 32 → BitVec 8} {n i : Nat} :
    VarId.mk i ∈ abs sp n ↔ i < n ∧ sp (BitVec.ofNat 32 i) ≠ 0 := by
  simp [abs, Finset.mem_image, Finset.mem_filter, Finset.mem_range]

theorem val_var {x : StackSlot} (h : Flat.isVariable x = true) : val x = .Var ⟨x.payload.toNat⟩ :=
  by simp [val, h]

theorem val_not_var {x : StackSlot} (h : Flat.isVariable x = false) : ∀ i, val x ≠ .Var i := by
  intro i; unfold val; simp only [h, Bool.false_eq_true, ↓reduceIte]; split_ifs <;> simp

theorem ofNat_toNat32 (p : BitVec 32) : BitVec.ofNat 32 p.toNat = p := by simp

theorem ofNat_eq_iff {i : Nat} (hi : i < 2 ^ 32) (p : BitVec 32) :
    BitVec.ofNat 32 i = p ↔ i = p.toNat := by
  constructor
  · rintro rfl; simp [Nat.mod_eq_of_lt hi]
  · rintro rfl; simp

theorem isSpilled_iff {sp : BitVec 32 → BitVec 8} {n : Nat} {x : StackSlot}
    (hx : Flat.isVariable x = true → x.payload.toNat < n) :
    Flat.spillIsSpilled sp x = true ↔ (abs sp n).is_spilled (val x) := by
  cases hv : Flat.isVariable x
  · simp only [Flat.spillIsSpilled, hv, Bool.false_and, Bool.false_eq_true, false_iff]
    unfold val; simp only [hv, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp [SpillSet.is_spilled]
  · rw [val_var hv]
    simp [Flat.spillIsSpilled, hv, SpillSet.is_spilled, mem_abs, hx hv]

-- The spill set after `m_spilled[p] = 1`.
theorem abs_setByte {sp : BitVec 32 → BitVec 8} {n : Nat} (hn : n ≤ 2 ^ 32) {p : BitVec 32}
    (hp : p.toNat < n) : abs (Flat.setByte sp p 1) n = insert ⟨p.toNat⟩ (abs sp n) := by
  ext ⟨i⟩
  rw [mem_abs, Finset.mem_insert, mem_abs, VarId.mk.injEq]
  unfold Flat.setByte
  by_cases hi : i < n
  · by_cases h : i = p.toNat
    · subst h; simp [hi]
    · simp [hi, h, ofNat_eq_iff (show i < 2 ^ 32 by omega)]
  · simp only [hi, false_and, or_false, false_iff]
    omega

-- A result of `Flat.spillAdd` and a result of `SpillSet.add`: both are done with the spill set
-- of the bytes, or both fail.
def AddCorr (n : Nat) : Flat.Status × (BitVec 32 → BitVec 8) → Except ShuffleErr SpillSet → Prop
  | (.done, sp), .ok s => s = abs sp n
  | (.assertionFailed, _), .error _ => True
  | _, _ => False

theorem add_corr {sp : BitVec 32 → BitVec 8} {n : Nat} {x : StackSlot} (hn : n ≤ 2 ^ 32)
    (hx : Flat.isVariable x = true → x.payload.toNat < n) :
    AddCorr n (Flat.spillAdd sp x) ((abs sp n).add (val x)) := by
  unfold Flat.spillAdd
  cases hv : Flat.isVariable x
  · simp only [Bool.not_false, ↓reduceIte]
    unfold SpillSet.add
    unfold val; simp only [hv, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp [AddCorr, throw, throwThe, MonadExceptOf.throw]
  · have hp := hx hv
    rw [val_var hv]
    by_cases hz : sp x.payload = 0
    · have hm : VarId.mk x.payload.toNat ∉ abs sp n := by
        simp [mem_abs, hz]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz, bne_self_eq_false]
      simp [SpillSet.add, Shuffler.requires, hm, AddCorr,
        pure, Except.pure]
      exact (abs_setByte hn hp).symm
    · have hm : VarId.mk x.payload.toNat ∈ abs sp n := by
        simpa [mem_abs, hp] using hz
      have hb : (sp x.payload != 0) = true := by simpa using hz
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hb]
      simp [SpillSet.add, Shuffler.requires, hm, AddCorr, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]

theorem addAll_corr {n : Nat} (hn : n ≤ 2 ^ 32) (xs : List StackSlot)
    (hx : ∀ x ∈ xs, Flat.isVariable x = true → x.payload.toNat < n) (sp : BitVec 32 → BitVec 8) :
    AddCorr n (Flat.spillAddAll sp xs) ((xs.map val).foldlM SpillSet.add (abs sp n)) := by
  induction xs generalizing sp with
  | nil => rfl
  | cons x xs ih =>
    have h := add_corr (sp := sp) hn (hx x (List.mem_cons_self ..))
    simp only [Flat.spillAddAll, List.map_cons, List.foldlM_cons]
    revert h
    generalize Flat.spillAdd sp x = r
    generalize (abs sp n).add (val x) = e
    rcases r with ⟨st, sp'⟩
    intro h
    match st, e, h with
    | .done, .ok s, h =>
      simp only [AddCorr] at h
      subst h
      exact ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) sp'
    | .assertionFailed, .error _, _ => trivial

-- The checks pass: the id of each variable is below `ids idCount`.
theorem lt_ids {idCount : Bbu.Word} {x : StackSlot} (h : Flat.idOk idCount x = true)
    (hv : Flat.isVariable x = true) : x.payload.toNat < Flat.ids idCount := by
  simp only [Flat.idOk, hv, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Nat.not_le] at h
  have := x.payload.isLt
  simp only [Flat.ids]; omega

-- The ids of `spill_set` pass the checks: `spill_set` folds `SpillSet.add` and answers the
-- queries with `SpillSet.is_spilled`.
theorem spill_set_corr (idCount : Bbu.Word) (sp : BitVec 32 → BitVec 8)
    (adds queries : List StackSlot) (results : List (BitVec 8))
    (hok : (adds ++ queries).all (Flat.idOk idCount) = true) :
    match (adds.map val).foldlM SpillSet.add (abs sp (Flat.ids idCount)) with
    | .ok s => (Flat.spill_set idCount sp adds queries results).1 = 0
        ∧ abs (Flat.spill_set idCount sp adds queries results).2.1 (Flat.ids idCount) = s
        ∧ (Flat.spill_set idCount sp adds queries results).2.2
          = queries.map fun q => Flat.boolByte (decide (s.is_spilled (val q)))
    | .error _ => (Flat.spill_set idCount sp adds queries results).1 = -2
        ∧ (Flat.spill_set idCount sp adds queries results).2.2 = results := by
  rw [List.all_append, Bool.and_eq_true] at hok
  have hn : Flat.ids idCount ≤ 2 ^ 32 := Nat.min_le_right _ _
  have hc := addAll_corr hn adds (fun x hx => lt_ids (List.all_eq_true.mp hok.1 x hx)) sp
  have hq := fun q hq => lt_ids (List.all_eq_true.mp hok.2 q hq)
  simp only [Flat.spill_set, hok.1, hok.2, Bool.and_self, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  revert hc
  generalize Flat.spillAddAll sp adds = r
  generalize (adds.map val).foldlM SpillSet.add (abs sp (Flat.ids idCount)) = e
  rcases r with ⟨st, sp'⟩
  intro h
  match st, e, h with
  | .done, .ok s, h =>
    simp only [AddCorr] at h
    subst h
    refine ⟨rfl, rfl, List.map_congr_left fun q hm => ?_⟩
    congr 1
    exact Bool.eq_iff_iff.mpr ((isSpilled_iff (hq q hm)).trans decide_eq_true_iff.symm)
  | .assertionFailed, .error _, _ => exact ⟨rfl, rfl⟩

-- An id that is not below `idCount`: `spill_set` returns -2 and writes nothing.
theorem spill_set_bad (idCount : Bbu.Word) (sp : BitVec 32 → BitVec 8)
    (adds queries : List StackSlot) (results : List (BitVec 8))
    (hbad : (adds ++ queries).all (Flat.idOk idCount) = false) :
    Flat.spill_set idCount sp adds queries results = (-2, sp, results) := by
  rw [List.all_append] at hbad
  simp [Flat.spill_set, hbad]

end SpillBridge
