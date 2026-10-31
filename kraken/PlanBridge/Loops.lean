import BbuKraken.FlatPlan
import BbuKraken.FlatPopRel

/-!
The loops of the checks of the flat `Emission::run`: `availableFrom` and `labelsFrom` check a
predicate for each target offset, and `unmappedFrom` counts the `NONE` entries of `pos`.
-/

namespace Bbu.Flat

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_lt_iff {k : Nat} {n : Word} (hk : k ≤ MAX_N) :
    BitVec.ofNat 64 k < n ↔ k < n.toNat := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold MAX_N at hk; omega)]

-- A loop that checks `P` for each offset from `o` on below `n`.
theorem allFrom_iff {n : Word} (hn : n.toNat ≤ MAX_N) (P F : Word → Bool)
    (hF : ∀ o, F o = if o < n then P o && F (o + 1) else true) :
    F 0 = true ↔ ∀ d < n.toNat, P (BitVec.ofNat 64 d) = true := by
  suffices h : ∀ j k, k + j = n.toNat →
      (F (BitVec.ofNat 64 k) = true ↔ ∀ i < j, P (BitVec.ofNat 64 (k + i)) = true) by
    simpa using h n.toNat 0 (by omega)
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [hF, ite_eq_right (by rw [ofNat_lt_iff (by omega)]; omega)]
    simp
  | succ j ih =>
    intro k hk
    rw [hF, ite_eq_left (by rw [ofNat_lt_iff (by omega)]; omega), Bool.and_eq_true, ofNat_succ,
      ih (k + 1) (by omega)]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i => rw [show k + (i + 1) = k + 1 + i by omega]; exact h1 i (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega),
        fun i hi => by rw [show k + 1 + i = k + (i + 1) by omega]; exact h (i + 1) (by omega)⟩

theorem availableFrom_iff (st : St) (hn : st.targetSize.toNat ≤ MAX_N) :
    availableFrom st 0 = true ↔
      ∀ d < st.targetSize.toNat, isAvailable st (BitVec.ofNat 64 d) = true :=
  allFrom_iff hn _ _ fun o => by rw [availableFrom]; simp only [dite_eq_ite]

theorem labelsFrom_iff (st : St) (hn : st.targetSize.toNat ≤ MAX_N) :
    labelsFrom st 0 = true ↔ ∀ d < st.targetSize.toNat,
      ((get st.target (BitVec.ofNat 64 d)).kind ≠ FunctionReturnLabel ||
        get st.pos (BitVec.ofNat 64 d) ≠ NONE) = true :=
  allFrom_iff hn (fun o => (get st.target o).kind ≠ FunctionReturnLabel || get st.pos o ≠ NONE)
    (labelsFrom st) fun o => by rw [labelsFrom]; simp only [dite_eq_ite]

-- `unmappedFrom` adds the number of `NONE` entries of `pos` from `o` on below `targetSize`.
theorem unmappedFrom_eq (st : St) (hn : st.targetSize.toNat ≤ MAX_N) :
    unmappedFrom st 0 0 = BitVec.ofNat 64
      ((offsets st.targetSize).countP fun d => get st.pos d = NONE) := by
  suffices h : ∀ j k (c : Word), k + j = st.targetSize.toNat →
      unmappedFrom st (BitVec.ofNat 64 k) c = c + BitVec.ofNat 64
        (((List.range j).map fun i => BitVec.ofNat 64 (k + i)).countP
          fun d => get st.pos d = NONE) by
    simpa [offsets] using h st.targetSize.toNat 0 0 (by omega)
  intro j
  induction j with
  | zero =>
    intro k c hk
    rw [unmappedFrom, dite_eq_right (by rw [ofNat_lt_iff (by omega)]; omega)]
    simp
  | succ j ih =>
    intro k c hk
    rw [unmappedFrom, dite_eq_left (by rw [ofNat_lt_iff (by omega)]; omega), ofNat_succ,
      ih (k + 1) _ (by omega), List.range_succ_eq_map, List.map_cons, List.map_map,
      List.countP_cons]
    have e : ((fun i => BitVec.ofNat 64 (k + i)) ∘ Nat.succ) = fun i => BitVec.ofNat 64 (k + 1 + i) := by
      funext i; simp only [Function.comp_apply]; congr 1; omega
    rw [e, Nat.add_zero]
    generalize ((List.range j).map fun i => BitVec.ofNat 64 (k + 1 + i)).countP
      (fun d => get st.pos d = NONE) = x
    by_cases h : get st.pos (BitVec.ofNat 64 k) = NONE
    · simp only [Nat.add_zero, h, decide_true, ite_true, BitVec.ofNat_add]
      bv_omega
    · simp only [Nat.add_zero, h, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]

end Bbu.Flat
