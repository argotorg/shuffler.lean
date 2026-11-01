module

public import PlanBridge.Basic
import all PlanBridge.Basic

@[expose] public section

/-!
The relation between a flat result of `emissionRun` and a PR31 result of `Emission.run`
(`ERel`): the same status and blocked slot, and states that agree on the stack, the mapping and
the trace (`Out`). `Out` does not need `Sim`: after a block in `removeSurplus`, a slot can have
no destination.
-/

namespace PlanBridge

open Shuffler Shuffler.Emission BbuBridge

-- The flat state `fs` and the PR31 state `state` have the same stack, mapping and trace.
structure Out {e : Bbu.Env} {source : Stack} (fs : Bbu.Flat.St) (state : OState e source) :
    Prop where
  map : Bbu.Flat.absMapping fs.dest fs.pos fs.size fs.targetSize = absP state.mapping
  stack : (fs.data.toList.take fs.size.toNat).map decode = state.stack
  trace : fs.trace = (traceOps state.trace).map encodeOp
  size_le : fs.size.toNat ≤ Bbu.MAX_N
  tsize_le : fs.targetSize.toNat ≤ Bbu.MAX_N

-- The flat result `r` and the PR31 result.
def ERel {e : Bbu.Env} {source : Stack} (r : Bbu.Flat.Status × Bbu.Flat.St) :
    Except ShuffleErr (OResult e source) → Prop
  | .error _ => r.1 = .assertionFailed
  | .ok res => Out r.2 res.state ∧ match res.blocked with
    | none => r.1 = .done
    | some b => r.1 = .blocked ∧ r.2.blockedOffset.toNat = b.offset
        ∧ r.2.blockedExcess.toNat = b.excess

/-! ## `Out` from `Sim` and `Rel` -/

theorem take_data {α : Type} [Inhabited α] (v : Vector α Bbu.MAX_N) {k : Nat}
    (hk : k ≤ Bbu.MAX_N) :
    v.toList.take k = (List.range k).map fun i => Bbu.Flat.get v (BitVec.ofNat 64 i) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < k := by simpa using h2
  simp only [List.getElem_take, Vector.getElem_toList, List.getElem_map, List.getElem_range]
  rw [Bbu.Flat.get_ofNat v (by omega)]

theorem optOf_optW {x : Option Nat} (hx : ∀ i, x = some i → i < Bbu.MAX_N) :
    Bbu.Flat.optOf (Bbu.Flat.optW x) = x := by
  cases x with
  | none => exact Bbu.Flat.optOf_none
  | some i =>
    have hi := hx i rfl
    have hl : (BitVec.ofNat 64 i).toNat = i := Bbu.Flat.toNat_ofNat_lt hi
    simp only [Bbu.Flat.optW]
    rw [Bbu.Flat.optOf_some (Bbu.Flat.ne_none (by rw [hl]; exact hi)), hl]

section
variable {e : Bbu.Env} {source : Stack} {fs : Bbu.Flat.St} {st : Bbu.St}
  {state : OState e source}

theorem out_of (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) : Out fs state := by
  have hlen := h.len
  have hsz := hs.size
  have hN := hs.len_lt
  have hn := hs.n
  have hnl := hs.n_le
  have ht := tgt_length e
  have hn' : e.target.length = fs.targetSize.toNat := hn
  refine ⟨?_, ?_, ?_, by omega, hnl⟩
  · simp only [Bbu.Flat.absMapping, absP, Bbu.Map.Mapping.mk.injEq]
    constructor
    · apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      have hi : i < st.len := by simp at h2; omega
      simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList, List.getElem_finRange]
      have hd := hs.dest (BitVec.ofNat 64 i) (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; exact hi)
      rw [Bbu.Flat.get_ofNat _ (by omega), Bbu.Flat.toNat_ofNat_lt (by omega)] at hd
      have hlt := hs.dest_lt hi
      rw [Bbu.Flat.optOf_some (Bbu.Flat.ne_none (by omega)), hd]
      exact (h.dest ⟨i, by omega⟩).symm
    · apply List.ext_getElem (by simp; omega)
      intro d h1 h2
      have hd : d < e.n := by simp at h2; simp only [Bbu.Env.n]; omega
      simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList, List.getElem_finRange]
      have hp := hs.pos (BitVec.ofNat 64 d) (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega)
      rw [Bbu.Flat.get_ofNat _ (by omega), Bbu.Flat.toNat_ofNat_lt (by omega)] at hp
      rw [hp, optOf_optW]
      · exact (h.positionOf ⟨d, by omega⟩).symm
      · intro i hi
        obtain ⟨hl, _⟩ := (hs.hpos.iff d i).mp hi
        simp only [Bbu.St.dests, List.length_map] at hl
        simp only [Bbu.St.len] at hN
        omega
  · rw [take_data _ (by omega), h.stack]
    apply List.ext_getElem (by simp [Bbu.St.len] at hsz ⊢; omega)
    intro i h1 h2
    have hi : i < st.len := by simpa [Bbu.St.len] using h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hs.data _ (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; exact hi),
      Bbu.Flat.toNat_ofNat_lt (by omega)]
    simp [Bbu.St.val, List.getElem?_eq_getElem (show i < st.slots.length from hi)]
  · rw [hs.trace, h.trace]

-- `ERel` from `SimR` and `ResCorr`.
theorem erel_of {r : Bbu.Flat.Status × Bbu.Flat.St} {m : Bbu.M Bbu.St}
    {x : Except ShuffleErr (OResult e source)} (hs : Bbu.Flat.SimR e r m)
    (hc : ResCorr (Rel e) m x) : ERel r x := by
  rcases m with (_ | ⟨pos, ex, st'⟩) | st' <;> rcases x with x | res <;>
    simp only [ResCorr, Bbu.Flat.SimR] at hs hc
  all_goals try exact hs
  · simp only [ERel, hc.1]
    exact ⟨out_of hs.2.sim hc.2, hs.1, hs.2.blk0, hs.2.blk1⟩
  · simp only [ERel, hc.1]
    exact ⟨out_of hs.2 hc.2, hs.1⟩

end

end PlanBridge
