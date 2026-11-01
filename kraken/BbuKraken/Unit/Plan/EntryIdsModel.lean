module

public import BbuKraken.Unit.Plan.EntryDefs
import all BbuKraken.Unit.Plan.EntryDefs

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

theorem idsFrom_end (words : List Word) (idCount : Word) {i : Nat}
    (hi : words.length ≤ i) : idsFrom words idCount i = true := by
  simp [idsFrom, List.drop_eq_nil_of_le hi]

theorem idsFrom_step (words : List Word) (idCount : Word) {i : Nat}
    (hi : i < words.length) :
    idsFrom words idCount i =
      (Flat.idOk idCount (StackSlot.ofWord words[i]) && idsFrom words idCount (i + 1)) := by
  simp only [idsFrom, List.drop_eq_getElem_cons hi, List.all_cons]

theorem idsFrom_good (words : List Word) (idCount : Word) {i : Nat}
    (hi : i < words.length) (h : Flat.idOk idCount (StackSlot.ofWord words[i]) = true) :
    idsFrom words idCount i = idsFrom words idCount (i + 1) := by
  rw [idsFrom_step words idCount hi, h, Bool.true_and]

theorem idsFrom_bad (words : List Word) (idCount : Word) {i : Nat}
    (hi : i < words.length) (h : Flat.idOk idCount (StackSlot.ofWord words[i]) = false) :
    idsFrom words idCount i = false := by
  rw [idsFrom_step words idCount hi, h, Bool.false_and]

theorem idOk_opcode (idCount : Word) (x : StackSlot) (h : x.valueOpcode = 0#8) :
    Flat.idOk idCount x = true := by
  simp [Flat.idOk, Flat.isVariable, isLiteralValue, Const, h]

theorem idOk_kind (idCount : Word) (x : StackSlot) (h : x.kind ≠ 0#8) :
    Flat.idOk idCount x = true := by
  simp [Flat.idOk, Flat.isVariable, Value, h]

theorem idOk_payload (idCount : Word) (x : StackSlot)
    (h : x.payload.toNat < idCount.toNat) : Flat.idOk idCount x = true := by
  simp [Flat.idOk, Nat.not_le_of_gt h]

theorem idOk_bad (idCount : Word) (x : StackSlot)
    (hk : x.kind = 0#8) (ho : x.valueOpcode ≠ 0#8)
    (hp : idCount.toNat ≤ x.payload.toNat) : Flat.idOk idCount x = false := by
  simp [Flat.idOk, Flat.isVariable, Value, isLiteralValue, Const, hk, ho, hp]

theorem ids_model (words : List Word) (idCount m : Word)
    (hl : words.length = m.toNat) (hm : m.toNat ≤ MAX_N) :
    ((Flat.offsets m).all fun i => Flat.idOk idCount
      (Flat.get (vec (words.map StackSlot.ofWord)) i)) = idsFrom words idCount 0 := by
  have hmap : (Flat.offsets m).map (fun i =>
      Flat.get (vec (words.map StackSlot.ofWord)) i) = words.map StackSlot.ofWord := by
    apply List.ext_getElem
    · simp [Flat.offsets, hl]
    · intro i hi hi'
      have him : i < words.length := by simpa [Flat.offsets, hl] using hi
      have hiM : i < MAX_N := Nat.lt_of_lt_of_le him (hl ▸ hm)
      have ht : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        change i < 1024 at hiM
        omega
      simp only [Flat.offsets, List.getElem_map, List.getElem_range]
      rw [get_vecL (by simpa only [List.length_map, ht] using him)
        (by simpa only [List.length_map, hl] using hm)]
      simp only [ht, List.getElem_map]
  have he := congrArg (fun xs : List StackSlot => xs.all (Flat.idOk idCount)) hmap
  simpa only [List.all_map, idsFrom, List.drop_zero, Function.comp_def] using he

theorem sizes_m {g : EG} (h : Sizes g) : g.r.p.m.toNat ≤ MAX_N := by
  unfold Sizes EntryU.BadArgs at h
  omega

theorem sizes_n {g : EG} (h : Sizes g) : g.r.p.n.toNat ≤ MAX_N := by
  unfold Sizes EntryU.BadArgs at h
  omega

theorem sizes_guard {g : EG} (hs : Sizes g) :
    ¬ (g.r.p.m > BitVec.ofNat 64 MAX_N ∨ g.r.p.n > BitVec.ofNat 64 MAX_N ∨
      g.allowed.setWidth 8 > 1 ∨ g.strategy.setWidth 8 > 1) := by
  exact hs

theorem model_reject_source (g : EG) (hok : g.Ok) (hs : Sizes g)
    (hb : idsFrom g.r.p.sw g.idCount 0 = false) (us : Nat → Flat.RunU) :
    model g us = (-2#64, none) := by
  unfold model
  apply EntryU.reject_source
  · exact sizes_guard hs
  · exact (ids_model g.r.p.sw g.idCount g.r.p.m hok.sw (sizes_m hs)).trans hb

theorem model_reject_target (g : EG) (hok : g.Ok) (hs : Sizes g)
    (hsrc : idsFrom g.r.p.sw g.idCount 0 = true)
    (htgt : idsFrom g.r.p.tw g.idCount 0 = false) (us : Nat → Flat.RunU) :
    model g us = (-2#64, none) := by
  unfold model
  apply EntryU.reject_target
  · exact sizes_guard hs
  · exact (ids_model g.r.p.sw g.idCount g.r.p.m hok.sw (sizes_m hs)).trans hsrc
  · exact (ids_model g.r.p.tw g.idCount g.r.p.n hok.tw (sizes_n hs)).trans htgt

end Bbu.Unit.EntryValidU
