module

public import FlatShuffler.Unit.Plan.Emission
import all FlatShuffler.Unit.Plan.Emission
public import FlatShuffler.Unit.Lowest.Defs
import all FlatShuffler.Unit.Lowest.Defs
public import FlatShuffler.Unit.RemoveSurplusLemmas
import all FlatShuffler.Unit.RemoveSurplusLemmas

@[expose] public section

/-! The checks after the two preparation calls of `Emission::run`. -/

namespace FlatShuffler.Unit.RunU

def checks (st : Flat.St) : Prop :=
  st.size + st.pend = st.targetSize ∧ Flat.unmappedFrom st 0#64 0#64 = st.pend ∧
    Flat.availableFrom st 0#64 = true ∧ Flat.labelsFrom st 0#64 = true

def finish (st : Flat.St) : Flat.Status × Flat.St :=
  if st.size + st.pend ≠ st.targetSize then (.assertionFailed, st)
  else if Flat.unmappedFrom st 0#64 0#64 ≠ st.pend then (.assertionFailed, st)
  else if !Flat.availableFrom st 0#64 then (.assertionFailed, st)
  else if !Flat.labelsFrom st 0#64 then (.assertionFailed, st)
  else Flat.buildBottomUp st

-- These are the memory bounds and mapping conditions of the four callees. They contain
-- no machine execution predicate. A caller must prove them for its constructed mapping.
structure Safe (planned : Vector Word MAX_N) (st : Flat.St) (x : Nat) : Prop where
  surplus : st.trace.length + 2 * st.size.toNat ≤ 6 * st.targetSize.toNat + x ∧ DestOk st
  lowest : (Flat.removeSurplus st).1 = .done →
    let a := (Flat.removeSurplus st).2
    a.trace.length + 2 * a.size.toNat ≤ 6 * a.targetSize.toNat + x ∧
      DestOk a ∧ Flat.LowOk planned a
  loop : ∀ l, (Flat.removeSurplus st).1 = .done →
    let r := Flat.permuteAtLowestHeight planned l (Flat.removeSurplus st).2
    r.1 = .done → checks r.2 → Flat.HInv r.2 0 x

def afterLowest (planned : Vector Word MAX_N) (l : Flat.Locals)
    (st current : Flat.St) : Prop :=
  (Flat.removeSurplus st).1 = .done ∧
    Flat.permuteAtLowestHeight planned l (Flat.removeSurplus st).2 = (.done, current)

def zeroLocals : Flat.Locals :=
  ⟨Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0⟩

theorem emission_surplus_fail {planned : Vector Word MAX_N} {l : Flat.Locals} {st : Flat.St}
    (h : (Flat.removeSurplus st).1 ≠ .done) :
    Flat.emissionRun planned l st = Flat.removeSurplus st := by
  unfold Flat.emissionRun
  rw [ite_eq_left h]

theorem emission_lowest {planned : Vector Word MAX_N} {l : Flat.Locals} {st a : Flat.St}
    (h : Flat.removeSurplus st = (.done, a)) :
    Flat.emissionRun planned l st =
      if (Flat.permuteAtLowestHeight planned l a).1 ≠ .done then
        Flat.permuteAtLowestHeight planned l a
      else finish (Flat.permuteAtLowestHeight planned l a).2 := by
  unfold Flat.emissionRun
  rw [h]
  rfl

theorem emission_finish {planned : Vector Word MAX_N} {l : Flat.Locals} {st a : Flat.St}
    (h : afterLowest planned l st a) :
    Flat.emissionRun planned l st = finish a := by
  unfold Flat.emissionRun
  rw [ite_eq_right (fun hn => hn h.1), h.2]
  rfl

theorem finish_size {st : Flat.St} (h : st.size + st.pend ≠ st.targetSize) :
    finish st = (.assertionFailed, st) := by simp only [finish, ite_eq_left h]

theorem finish_unmapped {st : Flat.St} (h : Flat.unmappedFrom st 0#64 0#64 ≠ st.pend) :
    finish st = (.assertionFailed, st) := by
  unfold finish
  split
  · rfl
  · rfl

theorem finish_available {st : Flat.St} (h : Flat.availableFrom st 0#64 = false) :
    finish st = (.assertionFailed, st) := by
  unfold finish
  split
  · rfl
  · split
    · rfl
    · rw [h]; rfl

theorem finish_labels {st : Flat.St} (h : Flat.labelsFrom st 0#64 = false) :
    finish st = (.assertionFailed, st) := by
  unfold finish
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [h]; rfl

theorem finish_success {st : Flat.St} (h : checks st) : finish st = Flat.buildBottomUp st := by
  simp only [finish, h.1, h.2.1, h.2.2.1, h.2.2.2, ne_eq, not_true_eq_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem unmapped_step {st : Flat.St} {i c : Word} (h : i < st.targetSize) :
    Flat.unmappedFrom st i c =
      Flat.unmappedFrom st (i + 1#64) (if Flat.get st.pos i = Flat.NONE then c + 1#64 else c) := by
  rw [Flat.unmappedFrom, dite_eq_left h]
  rfl

theorem unmapped_end {st : Flat.St} {c : Word} :
    Flat.unmappedFrom st st.targetSize c = c := by
  rw [Flat.unmappedFrom, dite_eq_right (by bv_omega)]

theorem available_step {st : Flat.St} {i : Word} (h : i < st.targetSize) :
    Flat.availableFrom st i = (Flat.isAvailable st i && Flat.availableFrom st (i + 1#64)) := by
  rw [Flat.availableFrom, dite_eq_left h]
  rfl

theorem available_end (st : Flat.St) : Flat.availableFrom st st.targetSize = true := by
  rw [Flat.availableFrom, dite_eq_right (by bv_omega)]

theorem labels_step {st : Flat.St} {i : Word} (h : i < st.targetSize) :
    Flat.labelsFrom st i =
      (((Flat.get st.target i).kind ≠ FunctionReturnLabel || Flat.get st.pos i ≠ Flat.NONE) &&
        Flat.labelsFrom st (i + 1#64)) := by
  rw [Flat.labelsFrom, dite_eq_left h]
  rfl

theorem labels_end (st : Flat.St) : Flat.labelsFrom st st.targetSize = true := by
  rw [Flat.labelsFrom, dite_eq_right (by bv_omega)]

theorem labels_pass {st : Flat.St} {i : Word} (hi : i < st.targetSize)
    (h : (Flat.get st.target i).kind ≠ FunctionReturnLabel ∨ Flat.get st.pos i ≠ Flat.NONE) :
    Flat.labelsFrom st i = Flat.labelsFrom st (i + 1#64) := by
  have hb : (decide ((Flat.get st.target i).kind ≠ FunctionReturnLabel) ||
      decide (Flat.get st.pos i ≠ Flat.NONE)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact h
  rw [labels_step hi, hb]
  rfl

theorem labels_fail {st : Flat.St} {i : Word} (hi : i < st.targetSize)
    (hk : (Flat.get st.target i).kind = FunctionReturnLabel)
    (hp : Flat.get st.pos i = Flat.NONE) : Flat.labelsFrom st i = false := by
  rw [labels_step hi]
  simp only [hk, hp, ne_eq, not_true_eq_false, decide_false, Bool.false_or, Bool.false_and]

theorem bit_zero {b : Bool} {v : BitVec 8}
    (h : v = if b then 1#8 else 0#8) (hz : v = 0#8) : b = false := by
  cases b <;> simp_all

theorem bit_ne_zero {b : Bool} {v : BitVec 8}
    (h : v = if b then 1#8 else 0#8) (hz : v ≠ 0#8) : b = true := by
  cases b <;> simp_all

end FlatShuffler.Unit.RunU
