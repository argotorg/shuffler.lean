module

public import ShufflerBridge.Planner.Basic
import all ShufflerBridge.Planner.Basic

@[expose] public section

/-!
The relation between a flat result of `emissionRun` and a PR31 result of `Emission.run`
(`ERel`): the same status and blocked slot, and states that agree on the stack, the mapping and
the trace (`Out`). `Out` does not need `Sim`: after a block in `removeSurplus`, a slot can have
no destination.
-/

namespace ShufflerBridge.Planner

open Shuffler Shuffler.Emission ShufflerBridge.Emission

-- The flat state `fs` and the PR31 state `state` have the same stack, mapping and trace.
structure Out {e : FlatShuffler.Env} {source : Stack} (fs : FlatShuffler.Flat.St) (state : OState e source) :
    Prop where
  map : FlatShuffler.Flat.absMapping fs.dest fs.pos fs.size fs.targetSize = absP state.mapping
  stack : (fs.data.toList.take fs.size.toNat).map decodeStackSlot = state.stack
  trace : fs.trace = (traceOperations state.trace).map encodeTraceOperation
  size_le : fs.size.toNat ≤ FlatShuffler.maxStackSize
  tsize_le : fs.targetSize.toNat ≤ FlatShuffler.maxStackSize

-- The flat result `r` and the PR31 result.
def ERel {e : FlatShuffler.Env} {source : Stack} (r : FlatShuffler.Flat.Status × FlatShuffler.Flat.St) :
    Except ShuffleErr (OResult e source) → Prop
  | .error _ => r.1 = .assertionFailed
  | .ok res => Out r.2 res.state ∧ match res.blocked with
    | none => r.1 = .done
    | some b => r.1 = .blocked ∧ r.2.blockedOffset.toNat = b.offset
        ∧ r.2.blockedExcess.toNat = b.excess

/-! ## `Out` from `Sim` and `Rel` -/

theorem take_data {α : Type} [Inhabited α] (v : Vector α FlatShuffler.maxStackSize) {k : Nat}
    (hk : k ≤ FlatShuffler.maxStackSize) :
    v.toList.take k = (List.range k).map fun i => FlatShuffler.Flat.get v (BitVec.ofNat 64 i) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < k := by simpa using h2
  simp only [List.getElem_take, Vector.getElem_toList, List.getElem_map, List.getElem_range]
  rw [FlatShuffler.Flat.get_ofNat v (by omega)]

theorem optOf_optW {x : Option Nat} (hx : ∀ i, x = some i → i < FlatShuffler.maxStackSize) :
    FlatShuffler.Flat.optOf (FlatShuffler.Flat.optW x) = x := by
  cases x with
  | none => exact FlatShuffler.Flat.optOf_none
  | some i =>
    have hi := hx i rfl
    have hl : (BitVec.ofNat 64 i).toNat = i := FlatShuffler.Flat.toNat_ofNat_lt hi
    simp only [FlatShuffler.Flat.optW]
    rw [FlatShuffler.Flat.optOf_some (FlatShuffler.Flat.ne_none (by rw [hl]; exact hi)), hl]

section
variable {e : FlatShuffler.Env} {source : Stack} {fs : FlatShuffler.Flat.St} {st : FlatShuffler.St}
  {state : OState e source}

theorem out_of (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) : Out fs state := by
  have hlen := h.len
  have hsz := hs.size
  have hN := hs.len_lt
  have hn := hs.n
  have hnl := hs.n_le
  have ht := tgt_length e
  have hn' : e.target.length = fs.targetSize.toNat := hn
  refine ⟨?_, ?_, ?_, by omega, hnl⟩
  · simp only [FlatShuffler.Flat.absMapping, absP, FlatShuffler.Map.Mapping.mk.injEq]
    constructor
    · apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      have hi : i < st.len := by simp at h2; omega
      simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList, List.getElem_finRange]
      have hd := hs.dest (BitVec.ofNat 64 i) (by rw [FlatShuffler.Flat.toNat_ofNat_lt (by omega)]; exact hi)
      rw [FlatShuffler.Flat.get_ofNat _ (by omega), FlatShuffler.Flat.toNat_ofNat_lt (by omega)] at hd
      have hlt := hs.dest_lt hi
      rw [FlatShuffler.Flat.optOf_some (FlatShuffler.Flat.ne_none (by omega)), hd]
      exact (h.dest ⟨i, by omega⟩).symm
    · apply List.ext_getElem (by simp; omega)
      intro d h1 h2
      have hd : d < e.n := by simp at h2; simp only [FlatShuffler.Env.n]; omega
      simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList, List.getElem_finRange]
      have hp := hs.pos (BitVec.ofNat 64 d) (by rw [FlatShuffler.Flat.toNat_ofNat_lt (by omega)]; omega)
      rw [FlatShuffler.Flat.get_ofNat _ (by omega), FlatShuffler.Flat.toNat_ofNat_lt (by omega)] at hp
      rw [hp, optOf_optW]
      · exact (h.positionOf ⟨d, by omega⟩).symm
      · intro i hi
        obtain ⟨hl, _⟩ := (hs.hpos.iff d i).mp hi
        simp only [FlatShuffler.St.dests, List.length_map] at hl
        simp only [FlatShuffler.St.len] at hN
        omega
  · rw [take_data _ (by omega), h.stack]
    apply List.ext_getElem (by simp [FlatShuffler.St.len] at hsz ⊢; omega)
    intro i h1 h2
    have hi : i < st.len := by simpa [FlatShuffler.St.len] using h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hs.data _ (by rw [FlatShuffler.Flat.toNat_ofNat_lt (by omega)]; exact hi),
      FlatShuffler.Flat.toNat_ofNat_lt (by omega)]
    simp [FlatShuffler.St.val, List.getElem?_eq_getElem (show i < st.slots.length from hi)]
  · rw [hs.trace, h.trace]

-- `ERel` from `SimR` and `ResCorr`.
theorem erel_of {r : FlatShuffler.Flat.Status × FlatShuffler.Flat.St} {m : FlatShuffler.M FlatShuffler.St}
    {x : Except ShuffleErr (OResult e source)} (hs : FlatShuffler.Flat.SimR e r m)
    (hc : ResCorr (Rel e) m x) : ERel r x := by
  rcases m with (_ | ⟨pos, ex, st'⟩) | st' <;> rcases x with x | res <;>
    simp only [ResCorr, FlatShuffler.Flat.SimR] at hs hc
  all_goals try exact hs
  · simp only [ERel, hc.1]
    exact ⟨out_of hs.2.sim hc.2, hs.1, hs.2.blk0, hs.2.blk1⟩
  · simp only [ERel, hc.1]
    exact ⟨out_of hs.2 hc.2, hs.1⟩

end

end ShufflerBridge.Planner
