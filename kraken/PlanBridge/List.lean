module

public import PlanBridge.Out
import all PlanBridge.Out

@[expose] public section

/-!
The list state of a flat state in which each slot has a destination (`listOf`), as after a
`removeSurplus` that is not blocked. If the arrays of the flat state hold a PR31 mapping that
binds each slot, the flat state holds `listOf` (`Sim`), and `listOf` agrees with each PR31 state
with that mapping, stack and trace (`Rel`).
-/

namespace PlanBridge

open Shuffler Shuffler.Emission BbuBridge
open Bbu.Flat (get optOf optW absMapping)

-- The list state of `fs`.
def listOf (fs : Bbu.Flat.St) : Bbu.St where
  slots := (List.range fs.size.toNat).map fun i =>
    ⟨get fs.data (BitVec.ofNat 64 i), (get fs.dest (BitVec.ofNat 64 i)).toNat⟩
  positionOf := (fs.pos.toList.take fs.targetSize.toNat).map optOf
  pendingGenerations := fs.pend.toNat
  trace := fs.trace

-- The entries of an array that holds a list.
theorem abs_get {v : Vector Bbu.Word Bbu.MAX_N} {k a : Nat} {f : Fin a → Option Nat}
    (hk : k ≤ Bbu.MAX_N) (h : (v.toList.take k).map optOf = (List.finRange a).map f) :
    k = a ∧ ∀ i : Fin a, optOf (get v (BitVec.ofNat 64 i.val)) = f i := by
  have hl := congrArg List.length h
  simp only [List.length_map, List.length_take, Vector.length_toList, List.length_finRange] at hl
  have hka : k = a := by omega
  refine ⟨hka, fun i => ?_⟩
  have := List.getElem_of_eq h (i := i.val) (by simp; omega)
  simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList,
    List.getElem_finRange] at this
  rw [Bbu.Flat.get_ofNat v (by omega)]
  exact this

theorem optW_optOf (w : Bbu.Word) : optW (optOf w) = w := by
  unfold optOf
  split
  · next h => rw [h]; rfl
  · simp [optW]

variable {fs : Bbu.Flat.St}

theorem listOf_len : (listOf fs).len = fs.size.toNat := by simp [listOf, Bbu.St.len]

theorem listOf_val {i : Nat} (hi : i < fs.size.toNat) :
    (listOf fs).val i = get fs.data (BitVec.ofNat 64 i) := by
  simp [listOf, Bbu.St.val, List.getElem?_range hi]

theorem listOf_dest {i : Nat} (hi : i < fs.size.toNat) :
    (listOf fs).dest i = (get fs.dest (BitVec.ofNat 64 i)).toNat := by
  simp [listOf, Bbu.St.dest, List.getElem?_range hi]

theorem listOf_dests_iff {i d : Nat} :
    (∃ h : i < (listOf fs).dests.length, (listOf fs).dests[i] = d) ↔
      i < fs.size.toNat ∧ (get fs.dest (BitVec.ofNat 64 i)).toNat = d := by
  simp [listOf, Bbu.St.dests]

theorem listOf_posOf {d : Nat} (hn : fs.targetSize.toNat ≤ Bbu.MAX_N)
    (hd : d < fs.targetSize.toNat) :
    Bbu.positionOf (listOf fs) d = optOf (get fs.pos (BitVec.ofNat 64 d)) := by
  simp only [Bbu.positionOf, listOf, List.getElem?_map, List.getElem?_take, ite_eq_left hd,
    List.getElem?_eq_getElem (show d < fs.pos.toList.length by simp; omega),
    Option.map_some, Option.join_some, Vector.getElem_toList]
  rw [Bbu.Flat.get_ofNat _ (by omega)]

theorem listOf_posOf_ge {d : Nat} (hd : ¬d < fs.targetSize.toNat) :
    Bbu.positionOf (listOf fs) d = none := by
  simp [Bbu.positionOf, listOf, hd]

section
variable {e : Bbu.Env} {source : Stack} {state : OState e source}
  (hn : fs.targetSize.toNat ≤ Bbu.MAX_N) (hsz : fs.size.toNat ≤ Bbu.MAX_N)
  (hmap : absMapping fs.dest fs.pos fs.size fs.targetSize = absP state.mapping)
  (htot : ∀ i, (state.mapping i).isSome)
include hn hsz hmap htot

-- The arrays hold the mapping: the sizes, and the entries.
omit htot in
theorem map_sizes : fs.size.toNat = state.stack.length ∧ fs.targetSize.toNat = (tgt e).length := by
  simp only [absMapping, absP, Bbu.Map.Mapping.mk.injEq] at hmap
  exact ⟨(abs_get hsz hmap.1).1, (abs_get hn hmap.2).1⟩

omit hn in
theorem map_dest (i : Fin state.stack.length) :
    some (get fs.dest (BitVec.ofNat 64 i.val)).toNat = (state.mapping i).map Fin.val := by
  simp only [absMapping, absP, Bbu.Map.Mapping.mk.injEq] at hmap
  have h := (abs_get hsz hmap.1).2 i
  have hs : (state.mapping i).map Fin.val ≠ none := by
    have := htot i; cases hm : state.mapping i <;> simp_all
  rw [← h] at hs ⊢
  rw [Bbu.Flat.optOf_some fun h' => hs (by rw [h']; exact Bbu.Flat.optOf_none)]

omit hsz htot in
theorem map_pos (d : Fin (tgt e).length) :
    optOf (get fs.pos (BitVec.ofNat 64 d.val)) = (state.mapping.symm d).map Fin.val := by
  simp only [absMapping, absP, Bbu.Map.Mapping.mk.injEq] at hmap
  exact (abs_get hn hmap.2).2 d

theorem listOf_pos : Bbu.Pos fs.targetSize.toNat (listOf fs) := by
  obtain ⟨hs, ht⟩ := map_sizes hn hsz hmap
  refine ⟨by simp [listOf]; omega, fun d i => ?_⟩
  rw [listOf_dests_iff]
  constructor
  · intro h
    by_cases hd : d < fs.targetSize.toNat
    · rw [listOf_posOf hn hd, map_pos hn hmap ⟨d, by omega⟩] at h
      obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      have hm := (state.mapping.eq_some_iff).mp hi'
      have hdst := map_dest hsz hmap htot i'
      rw [hm, Option.map_some, Option.some_inj] at hdst
      exact ⟨by omega, hdst⟩
    · rw [listOf_posOf_ge hd] at h; cases h
  · rintro ⟨hi, hdi⟩
    have hdst := map_dest hsz hmap htot ⟨i, by omega⟩
    rw [hdi] at hdst
    obtain ⟨j, hj, hjd⟩ := Option.map_eq_some_iff.mp hdst.symm
    have hd : d < fs.targetSize.toNat := by have := j.isLt; omega
    rw [listOf_posOf hn hd, map_pos hn hmap ⟨d, by omega⟩]
    have : (⟨d, by omega⟩ : Fin (tgt e).length) = j := Fin.ext hjd.symm
    rw [this, (state.mapping.eq_some_iff).mpr hj]
    rfl

theorem listOf_sim (he : e = Bbu.Flat.listEnv fs.targetSize.toNat fs.target fs.spills) :
    Bbu.Flat.Sim e fs (listOf fs) := by
  have hp := listOf_pos hn hsz hmap htot
  have hlen := listOf_len (fs := fs)
  refine ⟨he, hn, hlen.symm, ?_, fun i hi => ?_, fun i hi => ?_, fun d hd => ?_, rfl, rfl, hp⟩
  · have := hp.dests.length_le; rw [Bbu.St.length_dests] at this; exact this
  · rw [hlen] at hi; rw [listOf_val hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hlen] at hi; rw [listOf_dest hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [Bbu.positionOf, listOf, List.getElem?_map, List.getElem?_take, ite_eq_left hd,
      List.getElem?_eq_getElem (show d.toNat < fs.pos.toList.length by simp; omega),
      Option.map_some, Option.join_some, Vector.getElem_toList, optW_optOf]
    rw [Bbu.Flat.get_toNat _ (by omega)]

theorem listOf_rel (he : e = Bbu.Flat.listEnv fs.targetSize.toNat fs.target fs.spills)
    (hstack : (fs.data.toList.take fs.size.toNat).map decode = state.stack)
    (htrace : fs.trace = (traceOps state.trace).map encodeOp)
    (hpend : state.pending_generations = fs.pend.toNat)
    (hcs : ∀ v ∈ fs.data.toList.take fs.size.toNat, Canon v) (hct : ∀ v ∈ e.target, Canon v) :
    Rel e (listOf fs) state := by
  have hs := listOf_sim hn hsz hmap htot he
  obtain ⟨hl, ht⟩ := map_sizes hn hsz hmap
  refine ⟨?_, fun i => ?_, hpend, htrace.symm, hs.n ▸ hs.hpos, ?_, hct⟩
  · rw [← hstack, take_data _ hsz]; simp [listOf]
  · rw [← map_dest hsz hmap htot i, listOf_dest (by omega)]
  · intro s hs'
    simp only [listOf, List.mem_map, List.mem_range] at hs'
    obtain ⟨i, hi, rfl⟩ := hs'
    apply hcs
    rw [take_data _ hsz]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

end

end PlanBridge
