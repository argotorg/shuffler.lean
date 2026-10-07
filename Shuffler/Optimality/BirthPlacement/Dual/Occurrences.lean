import Shuffler.Optimality.BirthPlacement.Dual.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual.Occurrences

variable {α : Type*} [DecidableEq α] {size : Nat}
variable {births target : Fin size → α}

def ordered (hcount : Word.Balanced births target) : Equiv.Perm (Fin size) :=
  Equiv.ofFiberEquiv fun value => (Word.fiber births value).trans
    ((Hall.ordered (Word.positions births value) (Word.positions target value)
      (hcount value)).toEquiv.trans (Word.fiber target value).symm)

theorem compatible (hcount : Word.Balanced births target) (index : Fin size) :
    births index = target (ordered hcount index) :=
  (Equiv.ofFiberEquiv_map _ index).symm

theorem local_ordered (hcount : Word.Balanced births target) (value : α) :
    Word.localMatching births target (ordered hcount) (compatible hcount) value =
      (Hall.ordered (Word.positions births value) (Word.positions target value)
        (hcount value)).toEquiv := by
  apply Equiv.ext
  intro position
  rcases position with ⟨position, hposition⟩
  obtain ⟨hlt, he⟩ := (Word.mem_positions births value position).mp hposition
  subst value
  apply Subtype.ext
  rfl

theorem ordered_lt_iff (hcount : Word.Balanced births target) (first second : Fin size)
    (hvalue : births first = births second) :
    ordered hcount first < ordered hcount second ↔ first < second := by
  let left := (Word.fiber births (births second)) ⟨first, hvalue⟩
  let right := (Word.fiber births (births second)) ⟨second, rfl⟩
  have he := (Hall.ordered (Word.positions births (births second))
    (Word.positions target (births second)) (hcount (births second))).lt_iff_lt
      (x := left) (y := right)
  change (Hall.ordered (Word.positions births (births second))
    (Word.positions target (births second)) (hcount (births second))).toEquiv left <
      (Hall.ordered (Word.positions births (births second))
        (Word.positions target (births second)) (hcount (births second))).toEquiv right ↔
      left < right at he
  rw [← local_ordered hcount (births second)] at he
  exact he

theorem rank_eq (hcount : Word.Balanced births target) (index : Fin size) :
    (Finset.univ.filter fun other => other < index ∧ births other = births index).card =
    (Finset.univ.filter fun other => other < ordered hcount index ∧ target other = births index).card := by
  have hp (other : Fin size) :
      (other < index ∧ births other = births index) ↔
      (ordered hcount other < ordered hcount index ∧ target (ordered hcount other) = births index) := by
    rw [← compatible hcount other]
    constructor
    · rintro ⟨hlt, hv⟩
      exact ⟨(ordered_lt_iff hcount other index hv).mpr hlt, hv⟩
    · rintro ⟨hlt, hv⟩
      exact ⟨(ordered_lt_iff hcount other index hv).mp hlt, hv⟩
  have he := Fintype.card_congr ((ordered hcount).subtypeEquiv
    (p := fun other => other < index ∧ births other = births index)
    (q := fun other => other < ordered hcount index ∧ target other = births index) hp)
  simpa only [Fintype.card_subtype] using he

theorem count_take_ofFn (word : Fin size → α) (height : Nat) (value : α) :
    ((List.ofFn word).take height).count value =
      (Finset.univ.filter fun index => index.val < height ∧ word index = value).card := by
  rw [← RawWord.positions_card, RawWord.positions_take, RawWord.positions_ofFn,
    Word.positions, Finset.filter_image, Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext index
  simp [and_comm]

theorem count_rank_eq (hcount : Word.Balanced births target) (index : Fin size) :
    ((List.ofFn births).take index.val).count (births index) =
      ((List.ofFn target).take (ordered hcount index).val).count (births index) := by
  rw [count_take_ofFn, count_take_ofFn]
  exact rank_eq hcount index

theorem count_succ (word : Fin size → α) (index : Fin size) :
    ((List.ofFn word).take (index.val + 1)).count (word index) =
      ((List.ofFn word).take index.val).count (word index) + 1 := by
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp

theorem count_rank_succ_eq (hcount : Word.Balanced births target) (index : Fin size) :
    ((List.ofFn births).take (index.val + 1)).count (births index) =
      ((List.ofFn target).take ((ordered hcount index).val + 1)).count (births index) := by
  rw [count_succ, compatible hcount index, count_succ, ← compatible hcount index, count_rank_eq]

def earlier (word : Fin size → α) (index : Fin size) : Finset (Fin size) :=
  Finset.univ.filter fun other => other < index ∧ word other = word index

def previous (word : Fin size → α) (index : Fin size) : Fin size :=
  if h : (earlier word index).Nonempty then (earlier word index).max' h else index

theorem previous_mem (word : Fin size → α) (index : Fin size)
    (h : (earlier word index).Nonempty) : previous word index ∈ earlier word index := by
  simpa only [previous, dite_eq_left h] using Finset.max'_mem (earlier word index) h

theorem previous_lt (word : Fin size → α) (index : Fin size)
    (h : (earlier word index).Nonempty) : previous word index < index :=
  (Finset.mem_filter.mp (previous_mem word index h)).2.1

theorem previous_value (word : Fin size → α) (index : Fin size)
    (h : (earlier word index).Nonempty) : word (previous word index) = word index :=
  (Finset.mem_filter.mp (previous_mem word index h)).2.2

theorem le_previous (word : Fin size → α) (index other : Fin size)
    (h : other ∈ earlier word index) : other ≤ previous word index := by
  have hn : (earlier word index).Nonempty := ⟨other, h⟩
  simpa only [previous, dite_eq_left hn] using Finset.le_max' (earlier word index) other h

theorem previous_injective (word : Fin size → α) (first second : Fin size)
    (hfirst : (earlier word first).Nonempty) (hsecond : (earlier word second).Nonempty)
    (he : previous word first = previous word second) : first = second := by
  have hv : word first = word second := by
    rw [← previous_value word first hfirst, ← previous_value word second hsecond, he]
  have hnot (left right : Fin size) (hn : (earlier word left).Nonempty)
      (heq : previous word left = previous word right) (hvalue : word left = word right) :
      ¬left < right := by
    intro hlt
    have hl := le_previous word right left (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hvalue⟩)
    rw [← heq] at hl
    exact (not_le_of_gt (previous_lt word left hn)) hl
  exact le_antisymm (le_of_not_gt (hnot second first hsecond he.symm hv.symm))
    (le_of_not_gt (hnot first second hfirst he hv))

theorem count_previous (word : Fin size → α) (index : Fin size)
    (h : (earlier word index).Nonempty) :
    ((List.ofFn word).take ((previous word index).val + 1)).count (word index) =
      ((List.ofFn word).take index.val).count (word index) := by
  rw [count_take_ofFn, count_take_ofFn]
  congr 1
  ext other
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hv⟩
    have hp := previous_lt word index h
    exact ⟨by omega, hv⟩
  · rintro ⟨hlt, hv⟩
    have hp := le_previous word index other (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hv⟩)
    exact ⟨by omega, hv⟩

end Shuffler.Optimality.BirthPlacement.Dual.Occurrences
